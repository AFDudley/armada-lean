/*
  The commit-boundary gate image for armada-lean, built with Nix via
  nix2container (docs/plans/nix-images.md T3.lean + T3.x.b; D1-D11).
  Layout mirrors exophial's own nix/gate.nix and armada-sdk's own
  nix/gate.nix: explicit layers, each keyed on its own inputs, plus one
  per-commit layer carrying the judged tree.

    toolsLayer    system tools, the elan-less Lean v4.33.1/v4.35.0
                  dispatch (nix/lean.nix), gcc (Lean's native-code
                  compiles need a C compiler), python3 (scripts/check.sh),
                  pre-commit 4.5.1, pre-commit-hooks 4.6.0 (D6's 7 local
                  "Base hooks"), and the exophial flake input's own
                  `exophial` package (its 5 `exophial-*` console-script
                  local hooks)
    depsLayer     armada-lean's own Lake dependency tree and Mathlib's
                  build cache (nix/lean-deps.nix `mathlibCache`, exposed
                  at the flake's own `packages.x86_64-linux.lake-deps`),
                  merged in at `/gate/.lake/packages`
    buildLayer    armada-lean's own ~93 ArmadaLean modules
                  (nix/lean-build.nix), already compiled at
                  `/gate/.lake/build`
    per commit    the judged tree at /gate, verbatim

  Nothing downloads at container run time (D11): `lake build` resolves
  every dependency, including Mathlib, from depsLayer's already-built
  `.lake/packages/<name>/.lake/build`, and pre-commit's 7 "Base hooks"
  and the 5 exophial-owned hooks are all `language: system` console
  scripts this image already carries on PATH -- no hook environment for
  pre-commit to build, and no `lake exe cache get` at run time.

  armada-lean's own ~93 ArmadaLean modules ARE built here
  (nix/lean-build.nix), seeded from the tracked `lake-artifact-cache/`
  directory (coordinator instruction, 2026-11-22). `gate.command`
  (.exophial/config.yaml, unchanged: `lake build && scripts/check.sh`)
  then sees a `.lake/build` that already matches the judged tree, so its
  own `lake build` is a fast re-verification, the same two-phase shape
  `.exophial/gate/Dockerfile`'s own `RUN lake build` plus `gate.command`
  already had. A commit whose tree carries an UNREFRESHED
  `lake-artifact-cache/` (a worker skipped the refresh step) still
  builds correctly -- Lake just recompiles the modules the stale seed
  does not cover, same as a cold cache.
*/
{
  pkgs,
  lib,
  n2c,
  pins,
  gateSrc,
  leanToolchains,
  leanDeps,
  leanBuild,
  exophialPkg,
}:
let
  toolPaths = [
    (pkgs.dockerTools.fakeNss.override { extraGroupLines = [ "nogroup:x:65534:" ]; })
    pkgs.bashInteractive
    pkgs.coreutils
    pkgs.gnugrep
    pkgs.gnused
    pkgs.findutils
    pkgs.gnutar
    pkgs.gzip
    pkgs.which
    pkgs.gitMinimal
    pkgs.gnumake
    pkgs.gcc
    pkgs.python312
    pins.preCommit
    pins.preCommitHooks
    leanToolchains.leanDispatch
    exophialPkg
  ];

  toolsEnv = pkgs.buildEnv {
    name = "armada-lean-gate-tools";
    paths = toolPaths;
    ignoreCollisions = true;
  };

  # The CA bundle: a safety net for any TLS client in the exophial
  # package's own dependency closure, never load-bearing for the gate's
  # own run (D11: no network at container run time; Lean's own binaries
  # and `lake build` against an already-warm `.lake/packages` need none).
  fhsRoot = pkgs.runCommand "armada-lean-gate-fhs-root" { } ''
    mkdir -p $out/etc/ssl/certs $out/tmp $out/usr/bin
    ln -s ${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt $out/etc/ssl/certs/ca-certificates.crt
    ln -s ${pkgs.coreutils}/bin/env $out/usr/bin/env
  '';

  # armada-lean's own Lake dependency tree and Mathlib build cache
  # (nix/lean-deps.nix), placed at the path `lake` expects under the
  # judged tree's own root: `/gate/.lake/packages`.
  depsRoot = pkgs.runCommand "armada-lean-gate-deps-root" { } ''
    mkdir -p $out/gate/.lake
    cp -r ${leanDeps.mathlibCache} $out/gate/.lake/packages
  '';

  # armada-lean's own complete Lake artifact-cache (nix/lean-build.nix):
  # every module's own cache entry, merged into one `LAKE_CACHE_DIR`.
  # `gate.command`'s own `lake build` (unchanged) restores every entry
  # from it and compiles nothing, as long as a worker's commit did not
  # change a module this cache has no entry for.
  buildRoot = pkgs.runCommand "armada-lean-gate-build-root" { } ''
    mkdir -p $out/gate
    cp -r ${leanBuild.allEntriesUnion} $out/gate/.lake-cache-seed
  '';

  # The judged tree, placed AT /gate: `copyToRoot` merges a listed
  # path's own CONTENTS at the image root, so `gateSrc` itself (a plain
  # checkout directory) would land its files at `/`, not `/gate` -- this
  # wrapper is what actually puts them at `/gate`.
  gateTree = pkgs.runCommand "armada-lean-gate-tree" { } ''
    mkdir -p $out/gate
    cp -r ${gateSrc}/. $out/gate/
  '';

  toolsLayer = n2c.buildLayer { copyToRoot = [ toolsEnv ]; };
  fhsLayer = n2c.buildLayer {
    copyToRoot = [ fhsRoot ];
    layers = [ toolsLayer ];
  };
  depsLayer = n2c.buildLayer {
    copyToRoot = [ depsRoot ];
    layers = [
      toolsLayer
      fhsLayer
    ];
  };
  buildLayer = n2c.buildLayer {
    copyToRoot = [ buildRoot ];
    layers = [
      toolsLayer
      fhsLayer
      depsLayer
    ];
  };
in
n2c.buildImage {
  name = "localhost/armada-lean-gate";
  layers = [
    toolsLayer
    fhsLayer
    depsLayer
    buildLayer
  ];
  copyToRoot = [ gateTree ];
  config = {
    WorkingDir = "/gate";
    Env = [
      "PATH=/bin"
      "HOME=/root"
      "SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
      # Without this, `lake build` (gate.command, run at container start)
      # falls back to its own default cache dir under the toolchain's own
      # install path (elan-less here, so there is no `~/.elan/...`
      # default to fall into either) and never sees buildLayer's seeded
      # entries at all -- `lake build` would then recompile every
      # ArmadaLean module from scratch, defeating the per-module Nix
      # build graph above (nix/lean-build.nix) even though its own
      # output is correct.
      "LAKE_CACHE_DIR=/gate/.lake-cache-seed"
    ];
  };
}
