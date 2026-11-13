#!/usr/bin/env python3
"""Record every search tactic call in its `says`-pinned form.

Doctrine: docs/lean/type-doctrine.md section 4a rule 5 (operator, 2026-10-31).
A search tactic (`simp`, `simp [..]`, `simp at ..`, `simp_all`, `simpa`,
`grind`, `grind [..]`) depends on the library state. Its result is pinned
in the source with Mathlib's `says` combinator
(`Mathlib/Tactic/Says.lean`): `simp? [h] says simp only [h, ...]`.
`simp only [...]` calls are already pinned; this script leaves them alone.
`omega` and `decide` are NOT in scope (type-doctrine.md section 4a rule 5):
they read the goal, not the library, so they need no search recording.

Re-runnable: run again on a converted file and it makes no further change
(every call is already in `tac? ... says tac2` form, or is a listed
exception left bare because it failed to record).

Usage:
    scripts/record_searches.py FILE.lean [FILE.lean ...]
    scripts/record_searches.py --all          # every ArmadaLean/**/*.lean

Each run:
  1. Marks every bare target call `tac [...] [at ..|using ..]` with `tac?`
     (same arguments, same at/using clause), in a backup copy.
  2. Elaborates the file through `lean-run lake env lean --json FILE`.
  3. Reads each "Try this: ..." message and its position.
  4. Inserts ` says <suggestion>` right after the matching `tac? ...` call.
  5. Re-elaborates. A call that produced no message, or that fails to
     elaborate after recording, is restored to its ORIGINAL text (not left
     half-marked) and printed to stderr as an exception.

LEAN_RUN: the elaboration command prefix (default: the real lean-run
wrapper). Override LEAN_RUN="lake env lean --json" to skip the slice/
semaphore wrapper in tests that already hold a slot.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field

LEAN_RUN = os.environ.get("LEAN_RUN", "lean-run lake env lean --json")  # relies on PATH

KEYWORDS = ["simp_all", "simpa", "simp", "grind"]  # longest/most-specific first
KW_RE = re.compile(r"\b(simp_all|simpa|simp|grind)\b")
IDENT = r"[A-Za-z_][A-Za-z0-9_'\u2080-\u2089\u2090-\u209c]*"
AT_TOKEN_RE = re.compile(r"[ \t]+(" + IDENT + r"|\u22a2|\*)")
MAX_ROUNDS = 6


def code_mask(text: str) -> bytearray:
    """1 where text[i] is real code; 0 inside a comment or string literal."""
    n = len(text)
    mask = bytearray(b"\x01" * n)
    i = 0
    block_depth = 0
    while i < n:
        c = text[i]
        if block_depth > 0:
            if text.startswith("/-", i):
                block_depth += 1
                mask[i] = mask[i + 1] = 0
                i += 2
                continue
            if text.startswith("-/", i):
                block_depth -= 1
                mask[i] = mask[i + 1] = 0
                i += 2
                continue
            mask[i] = 0
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                mask[k] = 0
            i = j
            continue
        if text.startswith("/-", i):
            block_depth = 1
            mask[i] = mask[i + 1] = 0
            i += 2
            continue
        if c == '"':
            mask[i] = 0
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    mask[i] = mask[i + 1] = 0
                    i += 2
                    continue
                mask[i] = 0
                i += 1
            if i < n:
                mask[i] = 0
                i += 1
            continue
        i += 1
    return mask


@dataclass
class Site:
    keyword: str
    kw_start: int
    kw_end: int  # keyword end, before any '?'
    line: int  # 1-indexed
    col: int  # 0-indexed, Lean convention
    status: str = "pending"  # pending|recorded|failed
    reason: str = ""
    orig_text: str = ""  # the full original site text (for exact restore)


def line_col_index(text: str) -> list[int]:
    """index[i] = absolute offset of the start of line i (1-indexed)."""
    idx = [0, 0]
    for m in re.finditer("\n", text):
        idx.append(m.end())
    return idx


def find_candidates(text: str, mask: bytearray) -> list[Site]:
    """Bare (unconverted) target call sites, in source order."""
    sites: list[Site] = []
    lstarts = line_col_index(text)
    for m in KW_RE.finditer(text):
        start, end = m.start(), m.end()
        if mask[start] == 0:
            continue
        if start > 0 and text[start - 1] == ".":
            continue  # qualified name, e.g. Foo.simp
        if end < len(text) and text[end] == "?":
            continue  # already marked this round / already converted
        # @[simp] attribute, not a tactic call
        if m.group(1) == "simp":
            before = text[:start].rstrip(" \t")
            after = text[end:].lstrip(" \t")
            if before.endswith("@[") and after.startswith("]"):
                continue
        # already-recorded form: `tac only [...]` (simp only, grind only, ...)
        rest = text[end:end + 8]
        if re.match(r"\s+only\b", rest):
            continue
        # locate 1-indexed line, 0-indexed column
        line_no = 0
        for i, off in enumerate(lstarts):
            if off <= start:
                line_no = i
            else:
                break
        col = start - lstarts[line_no]
        sites.append(Site(keyword=m.group(1), kw_start=start, kw_end=end,
                           line=line_no, col=col))
    return sites


def skip_ws_same_run(text: str, pos: int) -> int:
    n = len(text)
    while pos < n and text[pos] in " \t":
        pos += 1
    return pos


def consume_bracket(text: str, pos: int) -> int:
    """pos is right after the tactic name (+ '?'). If next non-space is
    '[', return the position right after the matching ']'. Else pos."""
    p = skip_ws_same_run(text, pos)
    if p >= len(text) or text[p] != "[":
        return pos
    depth = 0
    i = p
    n = len(text)
    while i < n:
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return pos  # unbalanced; refuse to consume


def consume_at_clause(text: str, pos: int) -> int:
    m = re.match(r"[ \t]+at\b", text[pos:])
    if not m:
        return pos
    p = pos + m.end()
    last_good = p
    while True:
        m2 = AT_TOKEN_RE.match(text, p)
        if not m2 or m2.group(1) == "says":
            break
        p = m2.end()
        last_good = p
    return last_good


def consume_using_clause(text: str, pos: int, tac_col: int) -> int:
    m = re.match(r"[ \t]+using\b", text[pos:])
    if not m:
        return pos
    p = pos + m.end()
    n = len(text)
    depth = 0
    last_nonspace = p
    while p < n:
        if (depth == 0 and text.startswith("says", p)
                and (p == 0 or not (text[p - 1].isalnum() or text[p - 1] in "_'"))
                and (p + 4 >= n or not (text[p + 4].isalnum() or text[p + 4] in "_'"))):
            break
        c = text[p]
        if c in "([\u27e8":
            depth += 1
            p += 1
            last_nonspace = p
            continue
        if c in ")]\u27e9":
            if depth == 0:
                break
            depth -= 1
            p += 1
            last_nonspace = p
            continue
        if depth == 0 and c in ",;":
            break
        if c == "\n":
            if depth > 0:
                p += 1
                continue
            # look ahead: is the next non-blank line a continuation
            # (indented deeper than the tactic) or a sibling/dedent?
            j = p + 1
            while j < n and text[j] in " \t\n":
                j += 1
            next_col = 0
            k = p + 1
            while k < n and text[k] in " \t":
                next_col += 1
                k += 1
            if j < n and next_col > tac_col and text[j] not in ")]\u27e9,;":
                p += 1
                continue
            break
        if text.startswith("<;>", p) and depth == 0:
            break
        if not c.isspace():
            last_nonspace = p + 1
        p += 1
    return last_nonspace


def span_end(text: str, kw_end_with_q: int, kind: str, tac_col: int) -> int:
    p = consume_bracket(text, kw_end_with_q)
    if kind in ("simp", "simp_all"):
        p = consume_at_clause(text, p)
    elif kind == "simpa":
        p = consume_using_clause(text, p, tac_col)
    # grind: nothing further
    return p


def run_lean(path: str) -> list[dict]:
    # This script's own elaboration passes are discovery, not the acceptance
    # check; running them under CI's automatic says.verify would re-run
    # every already-recorded search on every pass (slow) and can surface
    # spurious mismatches mid-edit. scripts/verify_says.sh does the real
    # verify, deliberately, with -Dsays.verify=true.
    cmd = LEAN_RUN.split() + ["-Dweak.says.no_verify_in_CI=true", path]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    msgs = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            msgs.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return msgs


def clean_suggestion(data: str) -> str | None:
    """Extract the replacement tactic text from a "Try this:"/"Try these:"
    message. `grind?` prints several alternatives ("Try these:") at
    2-space indent, each with its own further-indented continuation; take
    only the first alternative, as `says` would."""
    if data.startswith("Try these:"):
        body = data[len("Try these:"):].lstrip("\n")
    elif data.startswith("Try this:"):
        body = data[len("Try this:"):].lstrip("\n")
    else:
        return None
    lines = body.split("\n")
    if not lines:
        return None
    first_indent = len(lines[0]) - len(lines[0].lstrip(" "))
    out = []
    for ln in lines:
        indent = len(ln) - len(ln.lstrip(" "))
        if out and ln.strip() and indent <= first_indent:
            break  # next top-level alternative
        s = ln.strip()
        if s.startswith("[apply] "):
            s = s[len("[apply] "):]
        out.append(s)
    return " ".join(out).strip()


def mark_file(text: str) -> tuple[str, list[Site]]:
    mask = code_mask(text)
    sites = find_candidates(text, mask)
    for s in sites:
        orig_end = span_end(text, s.kw_end, s.keyword, s.col)
        s.orig_text = text[s.kw_start:orig_end]
    # insert '?' right after each keyword, descending order so offsets hold
    out = text
    for s in sorted(sites, key=lambda s: -s.kw_end):
        out = out[:s.kw_end] + "?" + out[s.kw_end:]
    return out, sites


def process_file(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        true_original = f.read()

    exceptions: list[dict] = []
    _dry_sites = find_candidates(true_original, code_mask(true_original))
    if not _dry_sites:
        return {"path": path, "sites": 0, "recorded": 0, "exceptions": []}

    original = ensure_says_import_text(true_original)
    marked, sites = mark_file(original)

    with open(path, "w", encoding="utf-8") as f:
        f.write(marked)

    current = marked
    recorded_count = 0
    # Inserting '?' for an earlier same-line site shifts the column of a
    # later same-line site; re-scan the actually-marked text (in the same
    # left-to-right order as `sites`) for the real post-mark positions,
    # so `bare_sites` keys match what Lean itself reports.
    post_mark_sites = find_candidates_with_question(marked, code_mask(marked))
    bare_sites = {(s.line, s.col) for s in post_mark_sites}
    orig_by_key = {(post.line, post.col): pre for pre, post in zip(sites, post_mark_sites)}
    resolved_records: list[dict] = []

    for round_no in range(MAX_ROUNDS):
        if not bare_sites:
            break
        msgs = run_lean(path)
        suggestions: dict[tuple[int, int], str] = {}
        ambiguous: set[tuple[int, int]] = set()
        errors_near: dict[tuple[int, int], str] = {}
        for m in msgs:
            pos = m.get("pos") or {}
            key = (pos.get("line"), pos.get("column"))
            if m.get("severity") == "information":
                sug = clean_suggestion(m.get("data", ""))
                if sug is not None and key in bare_sites:
                    if key in suggestions and suggestions[key] != sug:
                        ambiguous.add(key)
                    else:
                        suggestions[key] = sug
            elif m.get("severity") == "error":
                errors_near.setdefault(key, m.get("data", ""))
        for key in ambiguous:
            suggestions.pop(key, None)

        if not suggestions and not ambiguous and round_no > 0:
            break  # no progress; remaining bare_sites are failures

        # recompute current text + positions fresh (file on disk == current)
        with open(path, encoding="utf-8") as f:
            current = f.read()
        mask = code_mask(current)
        cand = {(s.line, s.col): s for s in find_candidates_with_question(current, mask)}

        edits: list[tuple[int, int, str]] = []  # (start, end, replacement)
        resolved_this_round = set()
        for key, sug in suggestions.items():
            s = cand.get(key)
            if s is None:
                continue
            end = span_end(current, s.kw_end, s.keyword, s.col)
            # Wrapped in parens: `says`'s explicit-result grammar is a
            # tacticSeq, which otherwise greedily swallows every tactic
            # chained after it with `;` on the same line as part of its
            # own recorded result (confirmed against `-Dsays.verify=true`).
            edits.append((s.kw_start, s.kw_start, "("))
            edits.append((end, end, " says " + sug + ")"))
            resolved_this_round.add(key)
            recorded_count += 1
            orig_text = orig_by_key[key].orig_text
            marked_prefix = orig_text[:len(s.keyword)] + "?" + orig_text[len(s.keyword):]
            resolved_records.append({"marker": "(" + marked_prefix + " says " + sug + ")",
                                      "orig_text": orig_text, "keyword": s.keyword,
                                      "line": s.line, "col": s.col})
        for key in ambiguous:
            s = cand.get(key)
            if s is None:
                continue
            edits.append((s.kw_end - 1, s.kw_end, ""))  # drop the '?'
            exceptions.append({"path": path, "line": s.line, "col": s.col,
                                "keyword": s.keyword,
                                "reason": "applied via <;>/combinator to several "
                                          "goals with differing Try-this suggestions"})
            resolved_this_round.add(key)

        # sites with no suggestion and no error are simply not reached
        # again (e.g. unreachable branch); leave them bare for next round.
        bare_sites -= resolved_this_round

        if edits:
            edits.sort(key=lambda e: -e[0])
            new_text = current
            for start, end, repl in edits:
                new_text = new_text[:start] + repl + new_text[end:]
            with open(path, "w", encoding="utf-8") as f:
                f.write(new_text)

        if not edits and round_no > 0:
            break

    # final: anything still bare is an exception; strip its '?' and report.
    if bare_sites:
        with open(path, encoding="utf-8") as f:
            current = f.read()
        mask = code_mask(current)
        cand = {(s.line, s.col): s for s in find_candidates_with_question(current, mask)}
        edits = []
        for key in bare_sites:
            s = cand.get(key)
            if s is None:
                continue
            edits.append((s.kw_end - 1, s.kw_end, ""))  # drop the '?'
            exceptions.append({"path": path, "line": s.line, "col": s.col,
                                "keyword": s.keyword, "reason": "no Try-this message"})
        edits.sort(key=lambda e: -e[0])
        for start, end, repl in edits:
            current = current[:start] + repl + current[end:]
        with open(path, "w", encoding="utf-8") as f:
            f.write(current)

    # verification elaboration: must build clean, no leftover Try-this.
    # A call that elaborates differently (or fails) after recording is
    # restored to its own original text, by locating its known marker
    # text in the current file and matching failures to the nearest
    # marker at or before the failure position; this never touches a
    # site that did not itself fail.
    resolved_records.sort(key=lambda r: (r["line"], r["col"]))
    for repair_round in range(MAX_ROUNDS):
        verify_msgs = run_lean(path)
        leftover = [m for m in verify_msgs if m.get("severity") == "information"
                    and clean_suggestion(str(m.get("data", ""))) is not None]
        errs = [m for m in verify_msgs if m.get("severity") == "error"]
        if not errs and not leftover:
            return {"path": path, "sites": len(sites), "recorded": recorded_count,
                    "exceptions": exceptions}
        if not resolved_records:
            break  # nothing left we can localize; fall through to hard revert

        with open(path, encoding="utf-8") as f:
            current = f.read()
        lstarts = line_col_index(current)

        def abs_pos(pos: dict) -> int:
            ln = pos.get("line") or 1
            return lstarts[ln] + (pos.get("column") or 0)

        cursor = 0
        located = []  # (start, end, record)
        for rec in resolved_records:
            # Anchor the search to the record's own original line. Two
            # records on different lines can produce byte-identical marker
            # text (same says-replacement), and a file already carrying an
            # earlier identical marker from a previous run (a site this
            # round did not touch) would otherwise match first, mapping
            # this record to the WRONG location and corrupting it on
            # revert.
            start_hint = max(cursor, lstarts[rec["line"]])
            idx = current.find(rec["marker"], start_hint)
            if idx == -1:
                continue
            located.append((idx, idx + len(rec["marker"]), rec))
            cursor = idx + len(rec["marker"])
        if not located:
            break

        bad_positions = [abs_pos(m.get("pos") or {}) for m in errs + leftover]
        to_revert_ids = set()
        for pos in bad_positions:
            before = [L for L in located if L[0] <= pos]
            chosen = max(before, key=lambda L: L[0]) if before else min(located, key=lambda L: L[0])
            to_revert_ids.add(id(chosen[2]))
        if not to_revert_ids:
            break

        revert_edits = []
        for start, end, rec in located:
            if id(rec) in to_revert_ids:
                revert_edits.append((start, end, rec["orig_text"]))
                exceptions.append({"path": path, "line": rec["line"], "col": rec["col"],
                                    "keyword": rec["keyword"],
                                    "reason": "elaborates differently (or fails) "
                                              "after recording"})
                recorded_count -= 1
        revert_edits.sort(key=lambda e: -e[0])
        new_text = current
        for start, end, repl in revert_edits:
            new_text = new_text[:start] + repl + new_text[end:]
        with open(path, "w", encoding="utf-8") as f:
            f.write(new_text)
        resolved_records = [r for r in resolved_records if id(r) not in to_revert_ids]

    # could not localize every failure after MAX_ROUNDS repair attempts:
    # restore the whole file verbatim rather than risk committing drift.
    with open(path, "w", encoding="utf-8") as f:
        f.write(true_original)
    exceptions.append({"path": path, "line": None, "col": None, "keyword": None,
                        "reason": "post-record elaboration kept failing after "
                                  "targeted reverts; whole file restored"})
    return {"path": path, "sites": len(sites), "recorded": 0,
            "exceptions": exceptions, "reverted_whole_file": True}


def find_candidates_with_question(text: str, mask: bytearray) -> list[Site]:
    """Like find_candidates, but matches `tac?` (just-marked, no says yet)."""
    sites: list[Site] = []
    lstarts = line_col_index(text)
    for m in KW_RE.finditer(text):
        start, end = m.start(), m.end()
        if mask[start] == 0:
            continue
        if start > 0 and text[start - 1] == ".":
            continue
        if end >= len(text) or text[end] != "?":
            continue
        qend = end + 1
        line_no = 0
        for i, off in enumerate(lstarts):
            if off <= start:
                line_no = i
            else:
                break
        col = start - lstarts[line_no]
        arg_end = span_end(text, qend, m.group(1), col)
        if re.match(r"\s+says\b", text[arg_end:arg_end + 8]):
            continue  # already recorded
        col = start - lstarts[line_no]
        sites.append(Site(keyword=m.group(1), kw_start=start, kw_end=qend,
                           line=line_no, col=col))
    return sites


def ensure_says_import_text(text: str) -> str:
    """Return `text` with `import Mathlib.Tactic.Says` after the last
    import line, unless it is already imported. A file with no import
    line at all (a leaf module) gets the import at the top, after any
    leading module doc-comment."""
    if re.search(r"^import Mathlib\.Tactic\.Says$", text, re.M):
        return text
    lines = text.split("\n")
    last_import = -1
    for i, ln in enumerate(lines):
        if ln.startswith("import "):
            last_import = i
    if last_import != -1:
        lines.insert(last_import + 1, "import Mathlib.Tactic.Says")
        return "\n".join(lines)
    # No import line: a Lean file's `import`s must all be the very first
    # thing in the file (Lean rejects one after a stray doc-comment too),
    # so prepend it.
    return "import Mathlib.Tactic.Says\n\n" + text



def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    if argv[0] == "--all":
        root = "ArmadaLean"
        files = []
        for dirpath, _dirs, filenames in os.walk(root):
            for fn in filenames:
                if fn.endswith(".lean"):
                    files.append(os.path.join(dirpath, fn))
        files.sort()
    else:
        files = argv

    all_exceptions = []
    total_sites = 0
    total_recorded = 0
    for path in files:
        result = process_file(path)
        total_sites += result["sites"]
        total_recorded += result["recorded"]
        all_exceptions.extend(result["exceptions"])
        print(f"{path}: {result['recorded']}/{result['sites']} recorded"
              + (f", {len(result['exceptions'])} exceptions" if result["exceptions"] else ""),
              file=sys.stderr)

    print(json.dumps({"files": len(files), "sites": total_sites,
                       "recorded": total_recorded,
                       "exceptions": all_exceptions}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
