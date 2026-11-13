"""Shared parts of the spec check (`scripts/spec_check.py`) and the conversion
(`scripts/convert_spec.py`). Design record: `docs/spec-module-design.md`.

Nothing here is a stored list of names, counts or signatures, with one named
exception. The rules are:

- `citations`: the source-citation forms of `armada-laconic/docs/lean/writing-lean.md`
  §11. A `theorem` whose doc comment has one is a spec theorem (operator decision
  2026-10-31, decision 1). Every other `theorem` is a helper.
- `every_state_reason`: the line "Every state: REASON" in a spec definition's doc
  comment (decision 2).
- `run_report`: the computed facts of `scripts/spec_report.lean`.
- `load_approved_open`: the one stored list. `scripts/approved-open.tsv` names each
  spec theorem the operator approved to stay open with `sorry`, with the date of that
  approval (`docs/process.md` rule 8.3, `docs/spec-module-design.md` §7).
"""
from __future__ import annotations

import json
import os
import re
import subprocess
from pathlib import Path

# writing-lean.md §11: "a paper passage (title and lines), a go-nitro or pool
# contract line, or a dated design-review citation". A paper passage is
# `SATP:213-215` or `SATP §2.1`. A repo property id (`Nitro-26`, `SATP-15`,
# `ForceMove-D11`, `docs-0080-03`, `P-5`, `S-RG`) names one passage through the
# maps `docs/nitro-theorems.md` and `docs/pool-symbolic-changes.md`.
_PAPER = re.compile(r"\b(?:ForceMove|Nitro|SATP)(?::\s*\d|\s*§\s*\d)")
_CONTRACT = re.compile(r"\b[A-Za-z]\w*\.(?:sol|circom)\s*:\s*\d")
_RULING = re.compile(r"\bdesign\s+decision,?\s*\d{4}-\d{2}-\d{2}", re.IGNORECASE)
_PROPERTY_ID = re.compile(
    r"\b(?:ForceMove|Nitro|SATP)-[A-Z]?\d+\b|\bdocs-\d{4}-\d{2}\b|\bP-\d+\b|\bS-RG\b"
)
CITATION_FORMS = (_PAPER, _CONTRACT, _RULING, _PROPERTY_ID)

_EVERY_STATE = re.compile(r"^\s*Every state:\s*(\S.*?)\s*$", re.MULTILINE)
_THEOREM_KEYWORD = re.compile(r"\btheorem\s")

LAKE = os.path.expanduser("~/.elan/bin/lake")
if not os.path.exists(LAKE):
    LAKE = "lake"

# The committed list `load_approved_open` reads (repo-relative to `root`). The one
# stored list this module reads: every other fact is computed from the environment.
APPROVED_OPEN_REL = Path("scripts/approved-open.tsv")


def citations(doc: str) -> list[str]:
    """The source citations in a doc comment, in the §11 forms."""
    return sorted({m.group(0) for pat in CITATION_FORMS for m in pat.finditer(doc)})


def every_state_reason(doc: str) -> str | None:
    m = _EVERY_STATE.search(doc)
    return m.group(1) if m else None


def module_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def load_approved_open(root: Path) -> dict[str, dict[str, str]]:
    """`APPROVED_OPEN_REL`'s rows, keyed by theorem name: `{"approved": DATE,
    "reason": TEXT}`. A blank line or a line starting with `#` is a comment.
    `spec_check.py` fails a spec theorem whose axioms include `sorryAx` and whose
    name is not a key here (`docs/spec-module-design.md` §7); it also reports this
    map in `--json` as `approved_open`. Fails loud on a missing file: the gate needs
    a real list to compare against, not a silent empty one."""
    path = root / APPROVED_OPEN_REL
    if not path.is_file():
        raise RuntimeError(
            f"{APPROVED_OPEN_REL} is missing in {root}. It is the committed list of "
            "spec theorems approved to stay open with `sorry` (rule 8.3); an empty "
            "repository state is not the same as an empty list."
        )
    out: dict[str, dict[str, str]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        name, approved, reason = line.split("\t", 2)
        out[name] = {"approved": approved, "reason": reason}
    return out


def run_report(root: Path) -> dict:
    """Run `scripts/spec_report.lean` and return its JSON object. The report is
    the last stdout line that starts with `{`; Lean prints warnings before it."""
    proc = subprocess.run(
        [LAKE, "env", "lean", "scripts/spec_report.lean"],
        cwd=root, capture_output=True, text=True, check=False,
    )
    lines = [ln for ln in proc.stdout.splitlines() if ln.startswith("{")]
    if proc.returncode != 0 or not lines:
        raise RuntimeError(
            "scripts/spec_report.lean failed (exit %d):\n%s\n%s"
            % (proc.returncode, proc.stdout[-4000:], proc.stderr[-4000:])
        )
    return json.loads(lines[-1])


def source_theorems(root: Path, report: dict) -> list[dict]:
    """The report's theorems that a `theorem` command declares. A structure
    projection or an auxiliary lemma has no `theorem` keyword on its name line."""
    cache: dict[str, list[str]] = {}
    out = []
    for t in report["theorems"]:
        path = module_path(root, t["module"])
        key = str(path)
        if key not in cache:
            cache[key] = path.read_text(encoding="utf-8").split("\n")
        lines = cache[key]
        line = lines[t["line"] - 1] if 0 < t["line"] <= len(lines) else ""
        if _THEOREM_KEYWORD.search(line):
            t = dict(t)
            t["path"] = str(path.relative_to(root))
            out.append(t)
    return out


def classify(theorems: list[dict]) -> tuple[list[dict], list[dict]]:
    """Split into (spec theorems, helpers) by the membership algorithm."""
    members, helpers = [], []
    for t in theorems:
        (members if citations(t["doc"]) else helpers).append(t)
    return members, helpers


# ---------------------------------------------------------------------------
# Lean source text


def code_mask(text: str) -> list[bool]:
    """`True` for each character of `text` that is code: not in a comment (`--`,
    nested `/- -/`, doc comments) and not in a string literal."""
    mask = [True] * len(text)
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                mask[i] = mask[i + 1] = False
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                mask[i] = mask[i + 1] = False
                i += 2
            else:
                mask[i] = False
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            mask[i] = mask[i + 1] = False
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = False
            i = j
        elif text[i] == '"':
            mask[i] = False
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    mask[i] = False
                    i += 1
                mask[i] = False
                i += 1
            if i < n:
                mask[i] = False
                i += 1
        else:
            i += 1
    return mask


OPEN = "([{⟨⦃"
CLOSE = ")]}⟩⦄"
IDENT_CHAR = re.compile(r"[\w'!?₀-₉]")


def ident_re(name: str) -> re.Pattern:
    """An identifier token `name`: not part of a longer name, not a field `x.name`."""
    return re.compile(r"(?<![\w.'!?])" + re.escape(name) + r"(?![\w'!?])")
