"""The gate-quality checks beyond the spec check: the type-doctrine linter
count, the `decisionScope` bound, and the counterexample build. Design
record: this module's own doc comments. Used by `spec_check.py`. Run
standalone with `python3 scripts/gate_extra.py --json` (see `main`, at
the end of this file): a worker checks its own branch before a merge,
with no `spec_check.py` build report needed.

Each check compares the working tree against `scripts/gate-baseline.json`,
a file tracked in the repository (`BASELINE_REL`), not a live git query.
A merge must not raise a linter count, and must not add or enlarge a
`decisionScope` finding, past what the baseline already carries.

This replaces an earlier live `git merge-base HEAD integrated` design. The
commit-boundary gate container judges the tree as a single orphan commit
with no other ref, and passes neither the host git history nor the host
environment into the container, so a live `git merge-base` query can never
work inside the real gate. A committed
baseline file needs no git history at all: it travels with the tree
itself, the one thing the container does carry.

The `decisionScope` check scans only the `ArmadaLean/**/*.lean` files
whose sha256 differs from `BASELINE_REL`'s recorded hash (plus any file
the baseline does not name at all) — not the whole 78-file source tree.
A full-tree scan re-elaborated all 78 files on every gate run, 235s on
an idle host and up to 1,328s under load, against the gate's 1,800s
timeout. A hash-scoped scan costs the size of the change instead. A file
whose hash matches the baseline is not scanned: its content is byte
identical to what the baseline already measured, so it can carry no new
or enlarged finding.

`scripts/update_gate_baseline.py` writes `BASELINE_REL` from the current
tree: the full type-lint summary, every `decisionScope` finding over
every `ArmadaLean/**/*.lean` file outside `ArmadaLean/Lint/`, and the
sha256 of each such file. Run it in the same branch that lowers a linter
count or fixes a `decisionScope` finding, and commit the result; never
run it to raise a count or add a finding — the gate compares the tree
against the committed file, so a baseline raised without a matching fix
shows up in the branch's own diff for review.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import spec_lib

LAKE = spec_lib.LAKE

# The committed baseline (repo-relative to `root`).
# `scripts/update_gate_baseline.py` is its only writer.
BASELINE_REL = Path("scripts/gate-baseline.json")

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

# The host runs at most 4 Lean processes at once, to bound memory use.
# build each run their own `lake env lean` processes, in a
# `ThreadPoolExecutor` capped at this count.
LEAN_PROCESS_MAX_WORKERS = 4

_OMEGA_RE = re.compile(r"omega call in (\S+) \(line (\d+)\) consumes (\d+) hypotheses")
_DECIDE_SIZE_RE = re.compile(r"decide call in (\S+) \(line (\d+)\): goal size (\d+)")
_DECIDE_FVAR_RE = re.compile(
    r"decide call in (\S+) \(line (\d+)\): goal has a free variable")
_DECIDE_KERNEL_RE = re.compile(r"decide \+kernel in (\S+) \(line (\d+)\)")
_NATIVE_DECIDE_RE = re.compile(r"native_decide in (\S+) \(line (\d+)\)")


def _run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)


def _lake_build(cwd: Path, *targets: str) -> None:
    proc = _run([LAKE, "build", *targets], cwd)
    if proc.returncode != 0:
        raise RuntimeError(
            f"lake build {' '.join(targets)} failed (exit {proc.returncode}) in {cwd}:\n"
            f"{proc.stdout[-4000:]}\n{proc.stderr[-4000:]}"
        )


def _lean_files(root: Path) -> list[Path]:
    """Every `ArmadaLean` source file except `ArmadaLean/Lint/`: the
    linter module cannot import itself (`ArmadaLean.Lint.DecisionScope`
    prepended as an extra import to its own source would be a self-
    import cycle)."""
    return sorted(
        p.relative_to(root) for p in (root / "ArmadaLean").rglob("*.lean")
        if "Lint" not in p.relative_to(root).parts
    )


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ---------------------------------------------------------------------------
# The committed baseline


def load_baseline(root: Path) -> dict:
    """`BASELINE_REL`'s content: `{"lint_summary": {...},
    "decision_findings": [{"file","declaration","kind","size"}, ...],
    "file_hashes": {relpath: sha256hex}}`. Fails loud, never silently,
    when the file is absent or malformed: every check below needs a real
    baseline to compare against, and a missing/broken file is a repo
    defect to fix, not a reason to skip the comparison."""
    path = root / BASELINE_REL
    if not path.is_file():
        raise RuntimeError(
            f"{BASELINE_REL} is missing in {root}. The lint/decisionScope "
            "checks compare the tree against this committed baseline; run "
            "scripts/update_gate_baseline.py from the trunk tree and "
            "commit the result."
        )
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        raise RuntimeError(f"{BASELINE_REL} is not valid JSON: {e}")
    for key in ("lint_summary", "decision_findings", "file_hashes"):
        if key not in data:
            raise RuntimeError(f"{BASELINE_REL} is missing the required key {key!r}")
    return data


def write_baseline(root: Path, baseline: dict) -> None:
    """Write `baseline` to `BASELINE_REL`, sorted for a stable,
    reviewable diff: `decision_findings` by (file, declaration, kind),
    `file_hashes` keys sorted, `lint_summary` keys sorted."""
    ordered = {
        "lint_summary": dict(sorted(baseline["lint_summary"].items())),
        "decision_findings": sorted(
            baseline["decision_findings"],
            key=lambda f: (f["file"], f["declaration"], f["kind"]),
        ),
        "file_hashes": dict(sorted(baseline["file_hashes"].items())),
    }
    path = root / BASELINE_REL
    path.write_text(json.dumps(ordered, indent=2, sort_keys=False) + "\n", encoding="utf-8")


def compute_baseline(root: Path) -> dict:
    """The full baseline for the CURRENT tree: the type-lint summary, every
    `decisionScope` finding over every `ArmadaLean` source file (the full
    scan `check_decision_scope` no longer runs on every gate call), and
    the sha256 of each such file. `scripts/update_gate_baseline.py`'s own
    implementation; also used directly by its test harness."""
    lint_summary = run_type_lint(root)
    files = _lean_files(root)
    raw_findings = run_decision_scope(root, files)
    decision_findings = [
        {"file": f["file"], "declaration": f["declaration"], "kind": f["kind"], "size": f["size"]}
        for f in raw_findings
    ]
    file_hashes = {str(f): _file_sha256(root / f) for f in files}
    return {
        "lint_summary": lint_summary,
        "decision_findings": decision_findings,
        "file_hashes": file_hashes,
    }


# ---------------------------------------------------------------------------
# 1. The linter-count check


def run_type_lint(root: Path) -> dict:
    """Build the default target, `ArmadaLean.Lint.TypeDoctrine` and its
    failure tests `ArmadaLean.Lint.TypeDoctrineTest` (a failed test fails
    the build), run the driver `scripts/type_lint.lean`, and return its
    `{"summary":true,...}` line."""
    _lake_build(root)
    _lake_build(root, "ArmadaLean.Lint.TypeDoctrine", "ArmadaLean.Lint.TypeDoctrineTest")
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
    working tree than `BASELINE_REL` records (a ratchet: equal or lower
    passes). A field that dropped gets a notice on stderr: the author
    can run `scripts/update_gate_baseline.py` to lower the baseline to
    match."""
    t0 = time.monotonic()
    baseline = load_baseline(root)
    base_summary = baseline["lint_summary"]
    tree_summary = run_type_lint(root)
    regressions = sorted(f for f in LINT_REGRESSION_FIELDS
                          if tree_summary[f] > base_summary.get(f, 0))
    lowered = sorted(f for f in LINT_REGRESSION_FIELDS
                      if tree_summary[f] < base_summary.get(f, 0))
    for f in lowered:
        print(
            f"NOTICE: {f} dropped from {base_summary[f]} to {tree_summary[f]}. "
            "Run scripts/update_gate_baseline.py and commit the result to lower "
            f"the baseline for {f}.",
            file=sys.stderr,
        )
    return {
        "lint_ok": not regressions,
        "lint_regressions": regressions,
        "lint_lowered_fields": lowered,
        "lint_summary": tree_summary,
        "lint_baseline_summary": base_summary,
        "lint_seconds": round(time.monotonic() - t0, 1),
    }


# ---------------------------------------------------------------------------
# 2. The decision-procedure bounds check


def _parse_decision_findings(relpath: str, text: str) -> list[dict]:
    out: list[dict] = []
    for m in _OMEGA_RE.finditer(text):
        out.append({"file": relpath, "declaration": m.group(1), "line": int(m.group(2)),
                    "kind": "omega", "size": int(m.group(3))})
    for m in _DECIDE_SIZE_RE.finditer(text):
        out.append({"file": relpath, "declaration": m.group(1), "line": int(m.group(2)),
                    "kind": "decide_size", "size": int(m.group(3))})
    for m in _DECIDE_FVAR_RE.finditer(text):
        out.append({"file": relpath, "declaration": m.group(1), "line": int(m.group(2)),
                    "kind": "decide_fvar", "size": 0})
    for m in _DECIDE_KERNEL_RE.finditer(text):
        out.append({"file": relpath, "declaration": m.group(1), "line": int(m.group(2)),
                    "kind": "decide_kernel", "size": 0})
    for m in _NATIVE_DECIDE_RE.finditer(text):
        out.append({"file": relpath, "declaration": m.group(1), "line": int(m.group(2)),
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


def run_decision_scope(root: Path, files: list[Path]) -> list[dict]:
    """Every `decisionScope` finding over `files`, at the committed
    bounds (`maxOmegaHyps = 13`, `maxDecideSize = 300`). An empty
    `files` list skips the build and returns no findings: nothing
    changed, so there is nothing to scan. `LEAN_PROCESS_MAX_WORKERS`
    caps the concurrent `lake env lean` processes at the host's
    4-process Lean limit."""
    if not files:
        return []
    _lake_build(root)
    _lake_build(root, "ArmadaLean.Lint.DecisionScope")
    tmp_root = root / ".scratch" / "check" / "decision_scope_src"
    if tmp_root.exists():
        shutil.rmtree(tmp_root)
    findings: list[dict] = []
    workers = min(LEAN_PROCESS_MAX_WORKERS, len(files))
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futures = {ex.submit(_scan_decision_file, root, f, tmp_root): f for f in files}
        for fut in as_completed(futures):
            findings.extend(fut.result())
    shutil.rmtree(tmp_root, ignore_errors=True)
    return sorted(findings, key=lambda d: (d["file"], d["line"], d["kind"]))


def check_decision_scope(root: Path) -> dict:
    """`decision_ok`: no finding on the working tree is new, and none has
    grown in size, versus `BASELINE_REL`. The baseline is not required to
    be clean: `NonVacuity.lean:2660` is a known trunk finding (a `decide`
    of size 21,601), so this compares against the baseline's own
    recorded findings instead of requiring zero findings.

    The scan is scoped to the files whose sha256 differs from
    `BASELINE_REL`'s `file_hashes` (plus any file the baseline does not
    name at all): a file whose hash matches is byte-identical to what
    the baseline already measured, so it is not rescanned. The
    whole-tree scan this replaced took 235-1,328s against the gate's
    1,800s timeout."""
    t0 = time.monotonic()
    baseline = load_baseline(root)
    base_hashes: dict[str, str] = baseline["file_hashes"]
    base_findings: list[dict] = baseline["decision_findings"]

    files = _lean_files(root)
    changed = [f for f in files if base_hashes.get(str(f)) != _file_sha256(root / f)]
    tree_findings = run_decision_scope(root, changed)

    def key(f: dict) -> tuple:
        return (f["file"], f["declaration"], f["kind"])

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
        "decision_new_findings": new_findings,
        "decision_larger_findings": larger_findings,
        "decision_files_scanned": [str(f) for f in changed],
        "decision_seconds": round(time.monotonic() - t0, 1),
    }


# ---------------------------------------------------------------------------
# 3. The counterexample build


def check_counterexamples(root: Path) -> dict:
    """`counterexamples_ok`: every `docs/counterexamples/*.lean` builds
    (`lake env lean`, exit 0), and none has `sorryAx` in its own
    `#print axioms` output (an open proof the file already names, not a
    finished counterexample). Each file runs through its own `lake env
    lean` process, in a `ThreadPoolExecutor` capped at
    `LEAN_PROCESS_MAX_WORKERS`, the same pattern `run_decision_scope`
    uses for the host's 4-process Lean limit."""
    t0 = time.monotonic()
    files = sorted((root / "docs" / "counterexamples").glob("*.lean"))

    def check_one(f: Path) -> dict:
        rel = str(f.relative_to(root))
        proc = _run([LAKE, "env", "lean", rel], root)
        has_sorry = "sorryAx" in proc.stdout
        passed = proc.returncode == 0 and not has_sorry
        return {
            "file": rel,
            "exit_code": proc.returncode,
            "sorryAx": has_sorry,
            "ok": passed,
        }

    results: list[dict] = []
    if files:
        workers = min(LEAN_PROCESS_MAX_WORKERS, len(files))
        with ThreadPoolExecutor(max_workers=workers) as ex:
            futures = {ex.submit(check_one, f): f for f in files}
            for fut in as_completed(futures):
                results.append(fut.result())
        results.sort(key=lambda r: r["file"])
    ok = all(r["ok"] for r in results)
    return {
        "counterexamples_ok": ok,
        "counterexamples": results,
        "counterexamples_seconds": round(time.monotonic() - t0, 1),
    }


# ---------------------------------------------------------------------------
# 4. Standalone entry point


def main(argv: list[str]) -> int:
    """Run the three gate-quality checks against the current directory
    and report. `--json` prints one JSON line to stdout and exit 0 means
    every `_ok` field is `true`; without it, a short PASS/FAIL line per
    check goes to stdout. A worker runs `python3 scripts/gate_extra.py
    --json` on its own branch to check `lint_ok` and `decision_ok`
    against the committed baseline before a merge, with no
    `spec_check.py` build report needed."""
    root = Path.cwd()
    json_mode = bool(argv) and argv[0] == "--json"

    try:
        lint_result = check_lint(root)
    except RuntimeError as e:
        lint_result = {"lint_ok": False, "lint_error": str(e)}
    try:
        decision_result = check_decision_scope(root)
    except RuntimeError as e:
        decision_result = {"decision_ok": False, "decision_error": str(e)}
    try:
        counterexamples_result = check_counterexamples(root)
    except RuntimeError as e:
        counterexamples_result = {"counterexamples_ok": False, "counterexamples_error": str(e)}

    passed = (lint_result["lint_ok"] and decision_result["decision_ok"]
              and counterexamples_result["counterexamples_ok"])

    if json_mode:
        print(json.dumps({
            "lint_ok": lint_result["lint_ok"],
            "lint_regressions": lint_result.get("lint_regressions", []),
            "lint_error": lint_result.get("lint_error"),
            "decision_ok": decision_result["decision_ok"],
            "decision_new_findings": decision_result.get("decision_new_findings", []),
            "decision_larger_findings": decision_result.get("decision_larger_findings", []),
            "decision_files_scanned": decision_result.get("decision_files_scanned", []),
            "decision_error": decision_result.get("decision_error"),
            "counterexamples_ok": counterexamples_result["counterexamples_ok"],
            "counterexamples_error": counterexamples_result.get("counterexamples_error"),
        }))
    else:
        for name, result, ok_field, err_field in (
            ("lint", lint_result, "lint_ok", "lint_error"),
            ("decisionScope", decision_result, "decision_ok", "decision_error"),
            ("counterexamples", counterexamples_result, "counterexamples_ok",
             "counterexamples_error"),
        ):
            print(("PASS " if result[ok_field] else "FAIL ") + name)
            if result.get(err_field):
                print(f"  {result[err_field]}")

    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
