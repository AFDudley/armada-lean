"""The two measures that `scripts/check.sh --json --base REF` reports for a rewrite of the model.

Design record: armada-laconic `docs/process.md`, R.3 and R.5. Both measures compare
the working tree with a base commit REF, given as `--base REF`. Without `--base`,
`spec_check.py` does not compute them: the gate container's copy of the repository
has no `integrated` branch, so no default base exists there.

- model_net_lines: the added lines minus the deleted lines of `ArmadaLean/` outside
  `ArmadaLean/Lint/`, from REF to the working tree. Untracked files count as added.
  It is a measurement, not a gate (armada-laconic `docs/process.md`).
- spec_changed: the sorted names of the definitions in `ArmadaLean/Spec/` whose text
  differs from REF, or that REF has and the working tree does not. A definition's
  text is its declaration from the keyword to the next line in column 0; the
  docstring above it is not part of it, and runs of whitespace compare as one space.
  A name in this list is a change to an approved statement (R.3).

The two measures only report. `spec_check.py` does not use them for its verdict.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

MODEL_DIR = "ArmadaLean"
LINT_DIR = "ArmadaLean/Lint"
SPEC_DIR = "ArmadaLean/Spec"

_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|inductive|instance|class)\s+([^\s:({\[]+)"
)
_NAMESPACE = re.compile(r"^namespace\s+(\S+)")
_END = re.compile(r"^end(?:\s+(\S+))?\s*$")


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout


def model_net_lines(root: Path, base: str) -> int:
    """Added minus deleted lines of the model code, from `base` to the working tree."""
    net = 0
    numstat = _git(root, "diff", "--numstat", base, "--", MODEL_DIR, f":!{LINT_DIR}")
    for line in numstat.splitlines():
        added, deleted, _path = line.split("\t", 2)
        if added != "-":  # "-" marks a binary file
            net += int(added) - int(deleted)
    untracked = _git(
        root, "ls-files", "--others", "--exclude-standard", "--", MODEL_DIR, f":!{LINT_DIR}"
    )
    for path in untracked.splitlines():
        net += len((root / path).read_text(encoding="utf-8").splitlines())
    return net


def spec_declarations(text: str) -> dict[str, str]:
    """The declarations of one Lean file: qualified name -> whitespace-normalized text."""
    decls: dict[str, str] = {}
    namespaces: list[str] = []
    name = ""
    body: list[str] = []

    def close() -> None:
        if name:
            decls[name] = " ".join(" ".join(body).split())

    for line in text.splitlines():
        if line[:1].isspace() or not line:
            if name:
                body.append(line)
            continue
        close()
        name, body = "", []
        if m := _NAMESPACE.match(line):
            namespaces.append(m.group(1))
        elif (m := _END.match(line)) and namespaces:
            namespaces.pop()
        elif m := _DECL.match(line):
            name = ".".join([*namespaces, m.group(1)])
            body = [line]
    close()
    return decls


def _spec_files_at(root: Path, base: str) -> dict[str, str]:
    paths = _git(root, "ls-tree", "-r", "--name-only", base, "--", SPEC_DIR).split()
    return {
        p: _git(root, "show", f"{base}:{p}") for p in paths if p.endswith(".lean")
    }


def _spec_files_now(root: Path) -> dict[str, str]:
    return {
        str(p.relative_to(root)): p.read_text(encoding="utf-8")
        for p in sorted((root / SPEC_DIR).rglob("*.lean"))
    }


def spec_changed(root: Path, base: str) -> list[str]:
    """Names of Spec definitions that changed or vanished from `base` to the working tree."""
    before: dict[str, str] = {}
    for text in _spec_files_at(root, base).values():
        before.update(spec_declarations(text))
    after: dict[str, str] = {}
    for text in _spec_files_now(root).values():
        after.update(spec_declarations(text))
    return sorted(n for n, t in before.items() if after.get(n) != t)


def measure(root: Path, base: str) -> dict[str, object]:
    """The `--json` fields: the base used, model_net_lines, spec_changed."""
    return {
        "measure_base": base,
        "model_net_lines": model_net_lines(root, base),
        "spec_changed": spec_changed(root, base),
    }
