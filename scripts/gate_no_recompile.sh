#!/usr/bin/env bash
# The flake gate's own acceptance check (docs/plans/nix-images.md,
# coordinator design 2026-11-22): `lake build` must compile ZERO
# ArmadaLean or Exophial modules in the gate container. The Nix build
# (nix/lean-build.nix) already compiled every module and shipped its own
# Lake artifact-cache entry as an image layer; `LAKE_CACHE_DIR` in the
# image (nix/gate.nix) points straight at it. A `Built ArmadaLean.*` or
# `Built Exophial.*` line here means the Nix build and the gate
# disagree -- the cache is stale or wrong, not that the module changed
# (a changed module already has a fresh Nix-built entry before the gate
# ever runs).
set -euo pipefail

log="$(mktemp)"
trap 'rm -f "$log"' EXIT

lake build 2>&1 | tee "$log"

if grep -qE '^(✔|✘|⚠|ℹ) \[[0-9]+/[0-9]+\] Built (ArmadaLean|Exophial)' "$log"; then
  echo "gate_no_recompile: lake build compiled an ArmadaLean or Exophial module; the image's Lake artifact-cache layer disagrees with this commit's tree" >&2
  exit 1
fi
