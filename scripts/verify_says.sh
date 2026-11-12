#!/usr/bin/env bash
# Verify every recorded `says` search tactic still reproduces its pinned
# result, per type-doctrine.md section 4a rule 5.
#
# Run this on a toolchain or Mathlib upgrade, and in a periodic check.
# Do NOT run it on every build: it re-executes every recorded search
# (simp?, simp_all?, simpa?, grind?), which is the cost the `says`
# combinator exists to avoid paying on each build.
#
# Usage: scripts/verify_says.sh [FILE.lean ...]   # default: every
#        ArmadaLean/**/*.lean
set -euo pipefail
cd "$(dirname "$0")/.."

if [ "$#" -gt 0 ]; then
    files=("$@")
else
    mapfile -t files < <(find ArmadaLean -name '*.lean' | sort)
fi

fail=0
for f in "${files[@]}"; do
    out=$(lake env lean --json -Dweak.says.verify=true "$f" 2>&1) || true
    errs=$(printf '%s\n' "$out" | python3 -c '
import json, sys
n = 0
for line in sys.stdin:
    line = line.strip()
    if not line.startswith("{"):
        continue
    try:
        m = json.loads(line)
    except json.JSONDecodeError:
        continue
    if m.get("severity") == "error":
        n += 1
        print("  %s:%s: %s" % (m.get("fileName"), m.get("pos"), m.get("data")), file=sys.stderr)
print(n)
')
    if [ "$errs" != "0" ]; then
        echo "FAIL $f ($errs recorded search(es) drifted)" >&2
        fail=1
    fi
done

if [ "$fail" -eq 0 ]; then
    echo "verify_says: every recorded search still matches its pinned result."
fi
exit "$fail"
