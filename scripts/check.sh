#!/usr/bin/env bash
# Acceptance check for armada-lean, moved into the tracked tree from
# docs/lean/verification.md section 1 (the gate container sees only tracked
# files, REPO_INIT.md "The gate Dockerfile"). Adapted for the whole
# ArmadaLean tree, not one file.
#
# Usage: scripts/check.sh [ALLOWLIST_FILE]
#        scripts/check.sh --json [THEOREM_NAME]
# Run from the repo root. Exit 0 means every check passed.
#
# --json mode prints exactly ONE JSON object to stdout (every other line
# goes to stderr), for an exophial `behavior` oracle's `stdout_json`
# observation (docs/ORACLES.md section 7). "the gate passes" alone is a
# vacuous acceptance predicate (any no-op program returns exit 0); this
# gives a pebble a field to name instead. Fields: build_ok, sorry (the
# fully-qualified name of every theorem whose own proof body still carries
# sorry), sorry_count, axioms_ok, signatures_ok, nonvacuity_ok, and
# theorem_under_test (the optional THEOREM_NAME argument, echoed back
# unconditionally — not a lookup — so a `then` predicate can pair it with
# `sorry` via `{"op": "not_member", "elem": "theorem_under_test",
# "collection": "sorry"}`, exophial `then_ops.py`'s member-family shape),
# and theorem_in_sorry (true when THEOREM_NAME, or a fully-qualified name
# that ends in ".THEOREM_NAME", is in `sorry`). A spec derivation offers only
# `{field, op, value}` predicates, so a pebble states
# `{"field": "theorem_in_sorry", "op": "eq", "value": false}` with no probe script.
# No ALLOWLIST_FILE support in --json mode (verification.md section 4's
# allowlist is a coordinator-only mechanism; a one-theorem worker pebble
# does not need it).
#
# Checks (docs/lean/proof-dispatch-plan.md Phase 0 decision 2,
# docs/lean/verification.md section 1 and section 5a):
#   1. lake build exits 0.
#   2. No MORE sorry lines than the baseline count (45 declarations plus
#      one doc-comment mention of the word, at 62197f4; see BASELINE_SORRY
#      below). A worker proves a theorem by removing its sorry, which
#      lowers the count; nothing may raise it.
#   3. No vacuous `:= True` / `:= False` Prop body.
#   4. Every theorem's axioms are in the allowed set: propext,
#      Classical.choice, Quot.sound, sorryAx (expected while BASELINE_SORRY
#      sorries remain open), EdDSAVerify, VerifyAccepts, VerifyOwnedAccepts.
#   5. No approved theorem's statement text changed against
#      scripts/sigs-baseline.tsv, a frozen snapshot taken at 62197f4 (the tip
#      both pool-symbolic-approved-2026-10-28 and
#      nitro-proofs-approved-2026-10-28 are reachable from). The gate
#      container carries no `.git` (its tree is a tar of the judged commit),
#      so this check compares against a COMMITTED FILE, never `git show
#      BASE:FILE` — a git-based compare silently passes everything the one
#      time it matters, inside the gate, because the baseline sha is
#      unreachable there. An ALLOWLIST_FILE names declarations a brief is
#      permitted to change (verification.md section 4); a worker never adds
#      a name to it.
#      Re-baseline (operator/coordinator only, when a new tag ratifies a
#      changed approved statement):
#      `python3 scripts/sigs.py $(find ArmadaLean -name '*.lean' | sort) > scripts/sigs-baseline.tsv`.
#   6. The Nitro non-vacuity witness module (ArmadaLean/Nitro/NonVacuity.lean)
#      builds with no sorry (verification.md section 5a).
#   7. Prints `SORRY <fully.qualified.name>` for every theorem whose own
#      proof body still carries a literal `sorry`, then `SORRY_COUNT <n>`.
set -u

JSON_MODE=0
THEOREM_UNDER_TEST=""
if [ "${1:-}" = "--json" ]; then
  JSON_MODE=1
  shift
  THEOREM_UNDER_TEST="${1:-}"
  ALLOW=/dev/null
else
  ALLOW="${1:-/dev/null}"
fi

LAKE="$HOME/.elan/bin/lake"
command -v "$LAKE" >/dev/null 2>&1 || LAKE="lake"
OUT=.scratch/check
mkdir -p "$OUT"
fail=0
if [ "$JSON_MODE" -eq 1 ]; then
  say() { printf '%s\n' "$*" >&2; }
else
  say() { printf '%s\n' "$*"; }
fi

BASELINE_SORRY=46

LEAN_FILES=$(find ArmadaLean -name '*.lean' | sort)

# 1. Build, exit 0.
"$LAKE" build > "$OUT/build.log" 2>&1
rc=$?
if [ "$rc" -ne 0 ]; then say "FAIL build exit $rc (see $OUT/build.log)"; fail=1; build_ok=false; else say "PASS build"; build_ok=true; fi

# 2. No new sorry beyond the baseline count.
now_sorry=$(grep -rn "sorry" ArmadaLean/ | wc -l)
if [ "$now_sorry" -gt "$BASELINE_SORRY" ]; then
  say "FAIL sorry count $now_sorry exceeds baseline $BASELINE_SORRY"
  fail=1
else
  say "PASS sorry count $now_sorry (baseline $BASELINE_SORRY)"
fi

# 3. No vacuous Prop body.
if grep -rnE ":=\s*(True|False)\s*$" ArmadaLean > "$OUT/vacuous.txt"; then
  say "FAIL vacuous body:"; cat "$OUT/vacuous.txt" >&2; fail=1
else
  say "PASS no vacuous body"
fi

# 4. Axioms of every theorem in the tree.
python3 scripts/sigs.py $LEAN_FILES > "$OUT/sigs-now.tsv"
cut -f2 "$OUT/sigs-now.tsv" | sed 's/^/#print axioms /' > "$OUT/ax-body.txt"
{ echo "import ArmadaLean"; echo "import ArmadaLean.Nitro.Lemmas"; cat "$OUT/ax-body.txt"; } > "$OUT/axioms.lean"
"$LAKE" env lean "$OUT/axioms.lean" > "$OUT/axioms.out" 2>&1
python3 - "$OUT/axioms.out" <<'PY' 1>&2
import re, sys
ok = {"propext", "Classical.choice", "Quot.sound", "sorryAx",
      "EdDSAVerify", "VerifyAccepts", "VerifyOwnedAccepts"}
text = open(sys.argv[1]).read().replace("\n", " ")
bad = 0
for m in re.finditer(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", text):
    names = {n.strip() for n in m.group(2).split(",") if n.strip()}
    extra = names - ok
    if extra:
        print("FAIL axioms", m.group(1), sorted(extra)); bad = 1
if "error" in text.lower() and "unknown identifier" not in text.lower():
    print("FAIL axioms.lean did not elaborate cleanly"); bad = 1
print("PASS axioms" if not bad else "FAIL axioms")
sys.exit(bad)
PY
axioms_rc=$?
if [ "$axioms_rc" -ne 0 ]; then fail=1; axioms_ok=false; else axioms_ok=true; fi

# 5. Statement signatures unchanged against the committed frozen baseline.
python3 - scripts/sigs-baseline.tsv "$OUT/sigs-now.tsv" "$ALLOW" <<'PY' 1>&2
import sys
def load(p):
    d = {}
    for line in open(p, encoding="utf-8"):
        parts = line.rstrip("\n").split("\t")
        if len(parts) == 3:
            _, name, sig = parts
            d[name] = sig
    return d
base, now = load(sys.argv[1]), load(sys.argv[2])
allow = {l.strip() for l in open(sys.argv[3]) if l.strip() and not l.startswith("#")}
bad = 0
for k, v in base.items():
    if k in allow:
        continue
    if k not in now:
        print("FAIL statement removed:", k); bad = 1
    elif now[k] != v:
        print("FAIL statement changed:", k); bad = 1
print("PASS signatures" if not bad else "FAIL signatures")
sys.exit(bad)
PY
signatures_rc=$?
if [ "$signatures_rc" -ne 0 ]; then fail=1; signatures_ok=false; else signatures_ok=true; fi

# 6. Non-vacuity witnesses build with no sorry.
nonvacuity_ok=true
if [ -f ArmadaLean/Nitro/NonVacuity.lean ]; then
  if grep -q "sorry" ArmadaLean/Nitro/NonVacuity.lean; then
    say "FAIL NonVacuity.lean carries sorry"; fail=1; nonvacuity_ok=false
  else
    say "PASS NonVacuity.lean no sorry"
  fi
  nv=$(grep -c "^example" ArmadaLean/Nitro/NonVacuity.lean)
  say "NonVacuity examples: $nv"
fi

# 7. SORRY report: one observable line per theorem that still carries
#    sorry, plus a count. See the file header note above.
python3 scripts/sorry_report.py $LEAN_FILES > "$OUT/sorry-report.txt"
if [ "$JSON_MODE" -eq 1 ]; then
  cat "$OUT/sorry-report.txt" >&2
else
  cat "$OUT/sorry-report.txt"
fi

# 8. Line counts (report only; current tree — the gate container carries no
#    .git to diff a baseline against, see section 5's note).
for f in ArmadaLean/PoolSafety.lean ArmadaLean/PoolOwned.lean ArmadaLean/Nitro/Liveness.lean; do
  n=$(wc -l < "$f"); say "LINES $f now=$n"
done

if [ "$JSON_MODE" -eq 1 ]; then
  python3 - "$OUT/sorry-report.txt" "$build_ok" "$axioms_ok" "$signatures_ok" "$nonvacuity_ok" "$THEOREM_UNDER_TEST" <<'PY'
import json
import sys

sorry_report_path, build_ok, axioms_ok, signatures_ok, nonvacuity_ok, theorem = sys.argv[1:7]
names = []
count = 0
for line in open(sorry_report_path, encoding="utf-8"):
    line = line.rstrip("\n")
    if line.startswith("SORRY "):
        names.append(line[len("SORRY "):])
    elif line.startswith("SORRY_COUNT "):
        count = int(line[len("SORRY_COUNT "):])

obj = {
    "build_ok": build_ok == "true",
    "sorry": names,
    "sorry_count": count,
    "axioms_ok": axioms_ok == "true",
    "signatures_ok": signatures_ok == "true",
    "nonvacuity_ok": nonvacuity_ok == "true",
    "theorem_under_test": theorem,
    "theorem_in_sorry": bool(theorem) and any(
        n == theorem or n.endswith("." + theorem) for n in names
    ),
}
print(json.dumps(obj))
PY
fi

exit $fail
