#!/usr/bin/env bash
# The gate's acceptance check, run as `scripts/check.sh` and as
# `scripts/check.sh --json THEOREM`.
# The check itself is scripts/spec_check.py (`lake build` plus the computed
# report of scripts/spec_report.lean); design record docs/spec-module-design.md.
# It reads no stored list of names, counts or signatures.
exec python3 "$(dirname "$0")/spec_check.py" "$@"
