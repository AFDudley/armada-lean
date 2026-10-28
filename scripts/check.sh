#!/usr/bin/env bash
# Acceptance check for armada-lean, moved into the tracked tree from
# docs/lean/verification.md section 1 (the gate container sees only tracked
# files, REPO_INIT.md "The gate Dockerfile"). Adapted for the whole
# ArmadaLean tree, not one file.
#
# Usage: scripts/check.sh [ALLOWLIST_FILE]
# Run from the repo root. Exit 0 means every check passed.
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
set -u
ALLOW="${1:-/dev/null}"
LAKE="$HOME/.elan/bin/lake"
command -v "$LAKE" >/dev/null 2>&1 || LAKE="lake"
OUT=.scratch/check
mkdir -p "$OUT"
fail=0
say() { printf '%s\n' "$*"; }

BASELINE_SORRY=46

LEAN_FILES=$(find ArmadaLean -name '*.lean' | sort)

# 1. Build, exit 0.
"$LAKE" build > "$OUT/build.log" 2>&1
rc=$?
if [ "$rc" -ne 0 ]; then say "FAIL build exit $rc (see $OUT/build.log)"; fail=1; else say "PASS build"; fi

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
  say "FAIL vacuous body:"; cat "$OUT/vacuous.txt"; fail=1
else
  say "PASS no vacuous body"
fi

# 4. Axioms of every theorem in the tree.
python3 scripts/sigs.py $LEAN_FILES > "$OUT/sigs-now.tsv"
cut -f2 "$OUT/sigs-now.tsv" | sed 's/^/#print axioms /' > "$OUT/ax-body.txt"
{ echo "import ArmadaLean"; echo "import ArmadaLean.Nitro.Lemmas"; cat "$OUT/ax-body.txt"; } > "$OUT/axioms.lean"
"$LAKE" env lean "$OUT/axioms.lean" > "$OUT/axioms.out" 2>&1
python3 - "$OUT/axioms.out" <<'PY' || fail=1
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

# 5. Statement signatures unchanged against the committed frozen baseline.
python3 - scripts/sigs-baseline.tsv "$OUT/sigs-now.tsv" "$ALLOW" <<'PY' || fail=1
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

# 6. Non-vacuity witnesses build with no sorry.
if [ -f ArmadaLean/Nitro/NonVacuity.lean ]; then
  if grep -q "sorry" ArmadaLean/Nitro/NonVacuity.lean; then
    say "FAIL NonVacuity.lean carries sorry"; fail=1
  else
    say "PASS NonVacuity.lean no sorry"
  fi
  nv=$(grep -c "^example" ArmadaLean/Nitro/NonVacuity.lean)
  say "NonVacuity examples: $nv"
fi

# 7. Line counts (report only; current tree — the gate container carries no
#    .git to diff a baseline against, see section 5's note).
for f in ArmadaLean/PoolSafety.lean ArmadaLean/PoolOwned.lean ArmadaLean/Nitro/Liveness.lean; do
  n=$(wc -l < "$f"); say "LINES $f now=$n"
done

exit $fail
