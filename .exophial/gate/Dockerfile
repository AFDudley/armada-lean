# armada-lean commit-boundary gate image (exophial D49,
# exophial/docs/decisions/2026-10-14-gate-runs-in-a-container-built-from-the-judged-commit.md).
# The pattern is armada-sdk's .exophial/gate/Dockerfile (commit c2a04b1) and
# lean-mend's .exophial/gate/Dockerfile (the elan + toolchain install steps).
#
# gate_container.build_gate_image builds this image from the judged commit's
# own tree (a tar of the working tree, .git and .scratch excluded) with
# `docker build --quiet -f .exophial/gate/Dockerfile -`.
# gate_container.run_in_container then runs gate.command (.exophial/config.yaml)
# as the sole process, with no volume and no environment from the host. The
# image's own ENV, HOME and WORKDIR are all that the container sees, so
# `lake exe cache get` runs at BUILD time here: the gate itself runs offline.
#
# gate.command runs `lake build` then `scripts/check.sh`. Each tool that
# these steps call is image content, pinned to the version the host runs:
#   python 3.12 + uv + git + the exophial wheel -> FROM exophial-e2e-base
#       (the local pre-commit hooks call exophial-check-claude-md,
#        exophial-reroute-main-commit, exophial-red-before-green,
#        exophial-check-subtree-edits, exophial-session-trailer)
#   elan + leanprover/lean4:v4.35.0 (lean-toolchain)   -> lake build
#       and leanprover/lean4:v4.33.1, kept so that a tree from before the
#       v4.35.0 move still builds in this image (exophial env_change_e2e
#       grades the parent tree in the new image)
#   pre-commit 4.5.1 (the host's version)              -> scripts/check.sh
#       does not itself run pre-commit, but the pre-commit hook
#       environments are still built here so a future gate.command that
#       adds `pre-commit run --all-files` needs no further image change
#   the Mathlib build cache (lake exe cache get)        -> lake build offline
#       (fetched from lean-toolchain, lakefile.lean, lake-manifest.json only,
#        before the judged tree is copied, so an unrelated source change
#        never busts this layer)
FROM exophial-e2e-base

USER root
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates build-essential \
    && rm -rf /var/lib/apt/lists/*

# --- elan + the pinned toolchain (lean-toolchain: leanprover/lean4:v4.35.0),
#     plus v4.33.1 for trees from before the move ---
ENV ELAN_HOME=/root/.elan HOME=/root
ENV PATH="/root/.elan/bin:${PATH}"
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --no-modify-path --default-toolchain none \
    && elan toolchain install leanprover/lean4:v4.35.0 \
    && elan toolchain install leanprover/lean4:v4.33.1

# --- pre-commit 4.5.1 (the host's version) ---
RUN uv tool install pre-commit==4.5.1 \
    && ln -sf /root/.local/bin/pre-commit /usr/local/bin/pre-commit

WORKDIR /gate

# Under `docker build --quiet` a RUN step that streams much output to the
# step pipe can die mid-write (armada-poc: npm ci exited 146; armada-sdk
# Dockerfile applies the same tail-on-failure discipline here). Each heavy
# step writes to a log file and prints the log tail only on failure.

# --- The Mathlib download cache, from the dependency manifest
#     (lean-toolchain, lakefile.lean, lake-manifest.json: the three files
#     lake needs to resolve and fetch every pinned git/registry package --
#     mathlib, plausible, LeanSearchClient, importGraph, proofwidgets,
#     aesop, Qq, batteries, Cli), plus vendor/exophial_core, the one
#     local-path dependency's own source (`lake exe cache get` must see a
#     path dependency's tree to resolve it; a git/registry dependency needs
#     only the manifest). A commit that touches none of these keeps this
#     layer's cache hit, so it never re-fetches Mathlib. `lake build` of
#     the project itself runs after the full tree is copied, below. ---
COPY lean-toolchain lakefile.lean lake-manifest.json ./
COPY vendor/exophial_core vendor/exophial_core
RUN lake exe cache get \
        > /tmp/lake-cache.log 2>&1 || { tail -c 40000 /tmp/lake-cache.log; exit 1; }

COPY . .

# --- The project build, now that the full tree is present. Depends on the
#     cache layer above; a source-only commit re-runs only this step. ---
RUN lake build \
        > /tmp/lake-build.log 2>&1 || { tail -c 40000 /tmp/lake-build.log; exit 1; }

# --- A throwaway git history gives pre-commit a repo (the judged tree has
#     no .git). `git add -A` honors .gitignore, so the file set matches the
#     host's `pre-commit run --all-files`. install-hooks builds each hook
#     environment and registers no git hook. The branch is not main,
#     because the reroute-main-commit hook refuses a commit on main. ---
RUN { git init -q -b gate-tree \
        && git add -A \
        && git -c user.email=gate@armada-lean -c user.name=gate \
               commit -qm "gate tree" \
        && pre-commit install-hooks --config .pre-commit-config.yaml ; } \
        > /tmp/precommit.log 2>&1 || { tail -c 40000 /tmp/precommit.log; exit 1; }

# No ENTRYPOINT: run_in_container passes gate.command directly. It runs in
# WORKDIR /gate with this image's PATH.
