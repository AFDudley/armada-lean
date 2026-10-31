#!/usr/bin/env bash
# The gate's acceptance check: `.exophial/config.yaml` `gate.command` and the
# open pebble specs run `scripts/check.sh` and `scripts/check.sh --json THEOREM`.
# The check itself is scripts/spec_check.py (`lake build` plus the computed
# report of scripts/spec_report.lean); design record docs/spec-module-design.md.
# It reads no stored list of names, counts or signatures.
exec python3 "$(dirname "$0")/spec_check.py" "$@"
