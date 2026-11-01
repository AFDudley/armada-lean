"""The gate-quality checks beyond the spec check: the type-doctrine linter
count, the `decisionScope` bound, and the counterexample build. Design
record: this module's own doc comments. Used by `spec_check.py`.

Each check compares the working tree against the merge base with the
trunk branch (`merge_base`), not against a stored threshold: a merge must
not raise a linter count, and must not add or enlarge a `decisionScope`
finding, past what the trunk already carries. On the trunk branch itself
the merge base IS `HEAD` (the trunk's own ancestor search for itself), so
both checks compare the tree with itself and always pass there.

The merge-base measurement runs in a throwaway `git worktree` under
`.scratch/check/`, with `.lake/packages` symlinked from the real
checkout (never copied, `worker.md`'s own setup rule) and its OWN
`.lake/build` (a different source tree cannot share build artifacts with
the one already built in the real checkout). The worktree is removed
after each measurement; the measured JSON is cached by merge-base commit
under `.scratch/check/base_cache/`, so a second `check.sh` run against an
unchanged merge base skips the rebuild entirely.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import spec_lib

LAKE = spec_lib.LAKE

TRUNK = "integrated"

# The six `scripts/type_lint.lean` summary fields that are finding COUNTS
# (`docs/lean/type-doctrine.md`'s merge rule). `decls_scanned`,
# `nitro_decls`, `pool_decls` and the two `..._spec_total` denominators
# grow with the project's own size, by design, and are not a regression
# by themselves.
LINT_REGRESSION_FIELDS = (
    "repeatedPremise_groups",
    "premiseVariant_groups",
    "looseHypothesis_findings",
    "aliasHypothesis_findings",
    "layerDiscipline_nitro_hits",
    "layerDiscipline_pool_hits",
)

# `ArmadaLean/Lint/DecisionScope.lean`'s own committed bounds
# (`type-doctrine.md` §3): the trunk's own measured maxima.
DECISION_MAX_OMEGA_HYPS = 13
DECISION_MAX_DECIDE_SIZE = 300

_OMEGA_RE = re.compile(r"omega call in (\S+) \(line (\d+)\) consumes (\d+) hypotheses")
_DECIDE_SIZE_RE = re.compile(r"decide call in (\S+) \(line (\d+)\): goal size (\d+)")
_DECIDE_FVAR_RE = re.compile(
    r"decide call in (\S+) \(line (\d+)\): goal has a free variable")
_DECIDE_KERNEL_RE = re.compile(r"decide \+kernel in (\S+) \(line (\d+)\)")
_NATIVE_DECIDE_RE = re.compile(r"native_decide in (\S+) \(line (\d+)\)")


def _run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)


def head_sha(root: Path) -> str:
    out = _run(["git", "rev-parse", "HEAD"], root)
    if out.returncode != 0:
        raise RuntimeError(f"git rev-parse HEAD failed:\n{out.stderr}")
    return out.stdout.strip()


def merge_base_sha(root: Path) -> str:
    """The commit `git merge-base HEAD` and the trunk branch share. A
    read-only query: it does not move the trunk branch or run exophial."""
    out = _run(["git", "merge-base", "HEAD", TRUNK], root)
    if out.returncode != 0:
        raise RuntimeError(f"git merge-base HEAD {TRUNK} failed:\n{out.stderr}")
    return out.stdout.strip()


def _cache_path(root: Path, sha: str, name: str) -> Path:
    d = root / ".scratch" / "check" / "base_cache"
    d.mkdir(parents=True, exist_ok=True)
    return d / f"{sha}-{name}.json"


class _BaseWorktree:
    """A throwaway `git worktree` of one merge-base commit, removed on
    exit. `.lake/packages` is a symlink to the real checkout's; its
    `.lake/build` is its own (a different source tree)."""

    def __init__(self, root: Path, sha: str):
        self.root = root
        self.sha = sha
        self.path = root / ".scratch" / "check" / f"base-{sha}"

    def __enter__(self) -> Path:
        if self.path.exists():
            shutil.rmtree(self.path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        add = _run(["git", "worktree", "add", "--detach", "--force",
                    str(self.path), self.sha], self.root)
        if add.returncode != 0:
            raise RuntimeError(f"git worktree add {self.path} {self.sha} failed:\n{add.stderr}")
        (self.path / ".lake").mkdir(parents=True, exist_ok=True)
        (self.path / ".lake" / "packages").symlink_to(self.root / ".lake" / "packages")
        return self.path

    def __exit__(self, *exc) -> None:
        _run(["git", "worktree", "remove", "--force", str(self.path)], self.root)
        shutil.rmtree(self.path, ignore_errors=True)


def _lake_build(cwd: Path, *targets: str) -> None:
    proc = _run([LAKE, "build", *targets], cwd)
    if proc.returncode != 0:
        raise RuntimeError(
            f"lake build {' '.join(targets)} failed (exit {proc.returncode}) in {cwd}:\n"
            f"{proc.stdout[-4000:]}\n{proc.stderr[-4000:]}"
        )


# ---------------------------------------------------------------------------
# 1. The linter-count check


def run_type_lint(root: Path) -> dict:
    """Build the default target and `ArmadaLean.Lint.TypeDoctrine`
    (`scripts/type_lint.lean` imports both), run the driver, and return
    its `{"summary":true,...}` line."""
    _lake_build(root)
    _lake_build(root, "ArmadaLean.Lint.TypeDoctrine")
    proc = _run([LAKE, "env", "lean", "scripts/type_lint.lean"], root)
    lines = [ln for ln in proc.stdout.splitlines() if ln.startswith('{"summary"')]
    if proc.returncode != 0 or not lines:
        raise RuntimeError(
            f"scripts/type_lint.lean failed (exit {proc.returncode}) in {root}:\n"
            f"{proc.stdout[-4000:]}\n{proc.stderr[-4000:]}"
        )
    return json.loads(lines[-1])


def check_lint(root: Path) -> dict:
    """`lint_ok`: no `LINT_REGRESSION_FIELDS` count is higher on the
    working tree than on the merge base with the trunk branch."""
    t0 = time.monotonic()
    sha = head_sha(root)
    base = merge_base_sha(root)
    tree_summary = run_type_lint(root)
    if base == sha:
        base_summary = tree_summary
    else:
        cache = _cache_path(root, base, "lint")
        if cache.exists():
            base_summary = json.loads(cache.read_text(encoding="utf-8"))
        else:
            with _BaseWorktree(root, base) as wt:
                base_summary = run_type_lint(wt)
            cache.write_text(json.dumps(base_summary), encoding="utf-8")
    regressions = sorted(f for f in LINT_REGRESSION_FIELDS
                          if tree_summary[f] > base_summary[f])
    return {
        "lint_ok": not regressions,
        "lint_regressions": regressions,
        "lint_summary": tree_summary,
        "lint_base_summary": base_summary,
        "lint_merge_base": base,
        "lint_seconds": round(time.monotonic() - t0, 1),
    }


# ---------------------------------------------------------------------------
# 2. The decision-procedure bounds check


def _decision_scope_files(root: Path) -> list[Path]:
    """Every `ArmadaLean` source file except `ArmadaLean/Lint/`: the
    linter module cannot import itself (`ArmadaLean.Lint.DecisionScope`
    prepended as an extra import to its own source would be a self-
    import cycle)."""
    return sorted(
        p.relative_to(root) for p in (root / "ArmadaLean").rglob("*.lean")
        if "Lint" not in p.relative_to(root).parts
    )


def _parse_decision_findings(relpath: str, text: str) -> list[dict]:
    out: list[dict] = []
    for m in _OMEGA_RE.finditer(text):
        out.append({"file": relpath, "decl": m.group(1), "line": int(m.group(2)),
                    "kind": "omega", "size": int(m.group(3))})
    for m in _DECIDE_SIZE_RE.finditer(text):
        out.append({"file": relpath, "decl": m.group(1), "line": int(m.group(2)),
                    "kind": "decide_size", "size": int(m.group(3))})
    for m in _DECIDE_FVAR_RE.finditer(text):
        out.append({"file": relpath, "decl": m.group(1), "line": int(m.group(2)),
                    "kind": "decide_fvar", "size": 0})
    for m in _DECIDE_KERNEL_RE.finditer(text):
        out.append({"file": relpath, "decl": m.group(1), "line": int(m.group(2)),
                    "kind": "decide_kernel", "size": 0})
    for m in _NATIVE_DECIDE_RE.finditer(text):
        out.append({"file": relpath, "decl": m.group(1), "line": int(m.group(2)),
                    "kind": "native_decide", "size": 0})
    return out


def _scan_decision_file(root: Path, relpath: Path, tmp_root: Path) -> list[dict]:
    """`linter.decisionScope` only fires on a command freshly elaborated
    with its option set: a plain `lake build`, or a bare `import
    ArmadaLean`, never re-runs it on an already-compiled proof. So each
    file is copied to `tmp_root` with `ArmadaLean.Lint.DecisionScope`
    prepended as an extra import, then re-elaborated alone through `lake
    env lean`, reusing the real checkout's already-built imports."""
    src = (root / relpath).read_text(encoding="utf-8")
    tmp_file = tmp_root / relpath
    tmp_file.parent.mkdir(parents=True, exist_ok=True)
    tmp_file.write_text("import ArmadaLean.Lint.DecisionScope\n" + src, encoding="utf-8")
    proc = _run(
        [LAKE, "env", "lean", "-R", str(tmp_root),
         "-Dlinter.decisionScope=true",
         f"-Dlinter.decisionScope.maxOmegaHyps={DECISION_MAX_OMEGA_HYPS}",
         f"-Dlinter.decisionScope.maxDecideSize={DECISION_MAX_DECIDE_SIZE}",
         str(tmp_file)],
        root,
    )
    return _parse_decision_findings(str(relpath), proc.stdout + proc.stderr)


def run_decision_scope(root: Path) -> list[dict]:
    """Every `decisionScope` finding over the whole `ArmadaLean` source
    tree, at the committed bounds (`maxOmegaHyps = 13`,
    `maxDecideSize = 300`)."""
    _lake_build(root)
    _lake_build(root, "ArmadaLean.Lint.DecisionScope")
    tmp_root = root / ".scratch" / "check" / "decision_scope_src"
    if tmp_root.exists():
        shutil.rmtree(tmp_root)
    files = _decision_scope_files(root)
    findings: list[dict] = []
    with ThreadPoolExecutor(max_workers=min(16, os.cpu_count() or 4)) as ex:
        futures = {ex.submit(_scan_decision_file, root, f, tmp_root): f for f in files}
        for fut in as_completed(futures):
            findings.extend(fut.result())
    shutil.rmtree(tmp_root, ignore_errors=True)
    return sorted(findings, key=lambda d: (d["file"], d["line"], d["kind"]))


def check_decision_scope(root: Path) -> dict:
    """`decision_ok`: no finding on the working tree is new, and none has
    grown in size, versus the merge base with the trunk branch. The
    trunk is not required to be clean: `NonVacuity.lean:2660` is a known
    trunk finding (a `decide` of size 21,601), so this compares against
    the base instead of requiring zero findings."""
    t0 = time.monotonic()
    sha = head_sha(root)
    base = merge_base_sha(root)
    tree_findings = run_decision_scope(root)
    if base == sha:
        base_findings = tree_findings
    else:
        cache = _cache_path(root, base, "decision")
        if cache.exists():
            base_findings = json.loads(cache.read_text(encoding="utf-8"))
        else:
            with _BaseWorktree(root, base) as wt:
                base_findings = run_decision_scope(wt)
            cache.write_text(json.dumps(base_findings), encoding="utf-8")

    def key(f: dict) -> tuple:
        return (f["file"], f["decl"], f["kind"])

    base_by_key: dict[tuple, list[dict]] = {}
    for f in base_findings:
        base_by_key.setdefault(key(f), []).append(f)

    new_findings = []
    larger_findings = []
    for f in tree_findings:
        matches = base_by_key.get(key(f), [])
        if not matches:
            new_findings.append(f)
        elif f["size"] > max(m["size"] for m in matches):
            larger_findings.append(f)

    return {
        "decision_ok": not new_findings and not larger_findings,
        "decision_findings": tree_findings,
        "decision_base_findings": base_findings,
        "decision_new_findings": new_findings,
        "decision_larger_findings": larger_findings,
        "decision_merge_base": base,
        "decision_seconds": round(time.monotonic() - t0, 1),
    }


# ---------------------------------------------------------------------------
# 3. The counterexample build


def check_counterexamples(root: Path) -> dict:
    """`counterexamples_ok`: every `docs/counterexamples/*.lean` builds
    (`lake env lean`, exit 0), and none has `sorryAx` in its own
    `#print axioms` output (an open proof the file already names, not a
    finished counterexample)."""
    t0 = time.monotonic()
    files = sorted((root / "docs" / "counterexamples").glob("*.lean"))
    results = []
    ok = True
    for f in files:
        rel = str(f.relative_to(root))
        proc = _run([LAKE, "env", "lean", rel], root)
        has_sorry = "sorryAx" in proc.stdout
        passed = proc.returncode == 0 and not has_sorry
        ok = ok and passed
        results.append({
            "file": rel,
            "exit_code": proc.returncode,
            "sorryAx": has_sorry,
            "ok": passed,
        })
    return {
        "counterexamples_ok": ok,
        "counterexamples": results,
        "counterexamples_seconds": round(time.monotonic() - t0, 1),
    }
