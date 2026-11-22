/*
  Lake's own dependency tree, in the Nix store at build time (D11): every
  `lake-manifest.json` git dependency fetched by its pinned rev
  (`pkgs.fetchgit`, one fixed-output derivation per dependency -- D5's
  "a lockfile feeds Nix, no hand-maintained hash" extended to
  `lake-manifest.json`), then Mathlib's own precompiled build cache
  (`lake exe cache get`) fetched by ONE further fixed-output derivation.

  `lake exe cache get` still runs, same as `.exophial/gate/Dockerfile`'s own
  `RUN lake exe cache get` -- D11 moves WHEN it runs (Nix build time, inside
  a fixed-output derivation, content-addressed by its own declared hash)
  rather than removing it. Measured against this exact mechanism
  (.scratch probe, 2026-11-22): a workspace assembled from these 9
  `fetchgit` outputs plus `vendor/exophial_core` accepts `lake exe cache
  get` with no further `git clone`/`lake update` step -- Lake reads the
  committed `lake-manifest.json` and the already-present package
  directories, and only the Mathlib cache's own per-file downloads touch
  the network.

  This derivation's own inputs are ONLY `leanToolchainFile`,
  `lakefileFile`, `lakeManifestFile` and `exophialCoreDir` -- never the
  judged tree's own ArmadaLean Lean sources. A commit that changes
  only the project's own Lean code leaves this derivation's hash, and so
  its Nix store path, UNCHANGED: Nix skips rebuilding it and the host's
  gate build reuses the already-fetched Mathlib cache instead of touching
  the network again.
*/
{
  pkgs,
  lib,
  lean,
  leanToolchainFile,
  lakefileFile,
  lakeManifestFile,
  exophialCoreDir,
}:
let
  fetchDep =
    { url, rev, hash }:
    pkgs.fetchgit {
      inherit url rev hash;
      # `leaveDotGit`: Lake inspects each dependency's own `.git` (the
      # "repository has local changes" check `cache get` runs on every
      # package) -- a plain source tarball with no `.git` is not what a
      # `lake-manifest.json` git dependency looks like on disk.
      leaveDotGit = true;
      # `deepClone = false`: one commit, not the dependency's full
      # history -- Lake never walks history, only the pinned rev.
      deepClone = false;
      fetchSubmodules = false;
    };

  # Every git dependency `lake-manifest.json` pins, fetched by its exact
  # rev. Hashes measured 2026-11-22 (`lib.fakeHash` then the build's own
  # reported `got:` value, same method T1.1 used for `pb-release`/
  # `pb-fork`). The dict key is the manifest's own `name` field -- the
  # directory name Lake expects under `.lake/packages/`.
  depSources = {
    mathlib = fetchDep {
      url = "https://github.com/leanprover-community/mathlib4.git";
      rev = "56a005855ea17e0b0958f73ec801ae140b0a1679";
      hash = "sha256-hjTR6L+ebJT669Tu+FlAhA7L//0G44h7UDZfsgkWdSg=";
    };
    plausible = fetchDep {
      url = "https://github.com/leanprover-community/plausible";
      rev = "dfa4f38190d07c37e315953e08b90fe2d95b3c24";
      hash = "sha256-fj5IdturPiqy/ZwSlUn+bvbsAGNMWMu1oi/oLY2YNKM=";
    };
    LeanSearchClient = fetchDep {
      url = "https://github.com/leanprover-community/LeanSearchClient";
      rev = "d6b4c7be5be75ec4917c873ac50c756dc1436372";
      hash = "sha256-/edp7AgIYtgJ1umoRaLiUs49eJWg+Jl9ymgd0ZQdr1g=";
    };
    importGraph = fetchDep {
      url = "https://github.com/leanprover-community/import-graph";
      rev = "a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93";
      hash = "sha256-/9DHLkd+wsUyh2SBFLlzcRsy4a3/FG2VVOod4ioy2m4=";
    };
    proofwidgets = fetchDep {
      url = "https://github.com/leanprover-community/ProofWidgets4";
      rev = "df72b022e558978a1c50264cfc4d7fec86fa8e04";
      hash = "sha256-z2oJNtpeDVGqRVwxWwAuo3QA0vAT+I6/BuqOulh3+50=";
    };
    aesop = fetchDep {
      url = "https://github.com/leanprover-community/aesop";
      rev = "4a174c490d8707121c4a9290800489f105d85e07";
      hash = "sha256-H9raO/IaXsB+FrPED8UnHHCxn7kxIZDGuuie5Ifl4f4=";
    };
    Qq = fetchDep {
      url = "https://github.com/leanprover-community/quote4";
      rev = "dce0ad79c486cb1fb504af04f953c3466b0c6db8";
      hash = "sha256-tmP5BRloR00B9jJ+loNk76gP+/D3MDD6a5H4+nX+Iwc=";
    };
    batteries = fetchDep {
      url = "https://github.com/leanprover-community/batteries";
      rev = "66e469188fe07963e5cf666c7d4433f45b8131c5";
      hash = "sha256-lLpldZKYwDaHfI3fx9GqbJLwEypa/vhcfduhS5wjTW0=";
    };
    Cli = fetchDep {
      url = "https://github.com/leanprover/lean4-cli";
      rev = "c24fe6078c630e89b489bffe59b3e20ac30d12c8";
      hash = "sha256-arjq+sEAJYW2o8pEZRS8EUyQABjb8vJX8zZJ6/+lrEk=";
    };
  };

  # `.lake/packages/<name>` for every fetched dependency, writable (a
  # `fetchgit` output is a read-only store path; `cache get` writes each
  # package's own `.lake/build`).
  packagesDir = pkgs.runCommand "armada-lean-lake-packages-src" { } (
    ''
      mkdir -p $out
    ''
    + lib.concatStringsSep "\n" (
      lib.mapAttrsToList (name: src: ''
        cp -r ${src} $out/${name}
        chmod -R u+w $out/${name}
      '') depSources
    )
  );

  # The Mathlib build cache (`lake exe cache get`): a fixed-output
  # derivation (D11), network-enabled inside its own sandbox only. Its
  # declared `outputHash` is the one thing a `lake-manifest.json`
  # dependency-rev bump or a `lean-toolchain` move must refresh --
  # computed the same way as every other pin in this migration
  # (`lib.fakeHash`, then the build's own reported `got:`).
  mathlibCache = pkgs.stdenv.mkDerivation {
    pname = "armada-lean-lake-deps-cache";
    version = "0";
    # A fixed-output derivation's content must carry no Nix store
    # reference (the content-addressing contract). The default
    # fixupPhase's own `patchShebangs` rewrites mathlib's and
    # batteries' own `scripts/*.sh` shebangs to an absolute
    # `/nix/store/...-bash` path, which trips exactly that check
    # (measured 2026-11-22: "fixed-output derivations must not
    # reference store paths"). `ompNodeModulesRaw` in exophial's own
    # nix/gate.nix hits the identical gotcha and carries the same fix.
    dontFixup = true;
    dontUnpack = true;
    nativeBuildInputs = [
      lean
      pkgs.gitMinimal
      pkgs.curl
      pkgs.cacert
      pkgs.gcc
      pkgs.gnutar
      pkgs.gzip
    ];
    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR/home"
      mkdir -p "$HOME"
      export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
      # `leanc`'s own default C compiler is a bundled clang whose produced
      # binaries ask for the FHS dynamic linker (`/lib64/ld-linux-*`),
      # which does not exist inside the Nix build sandbox (measured,
      # 2026-11-22: `could not execute external process '.../bin/cache'`
      # after a clean compile). `LEAN_CC` (`leanc --help`) overrides the
      # wrapped compiler; nixpkgs' own gcc wrapper always embeds a Nix
      # store interpreter in whatever it links.
      export LEAN_CC=${pkgs.gcc}/bin/cc
      mkdir -p build/.lake build/vendor
      cp -r ${packagesDir} build/.lake/packages
      chmod -R u+w build/.lake/packages
      cp ${leanToolchainFile} build/lean-toolchain
      cp ${lakefileFile} build/lakefile.lean
      cp ${lakeManifestFile} build/lake-manifest.json
      cp -r ${exophialCoreDir} build/vendor/exophial_core
      chmod -R u+w build/vendor
      cd build
      lake exe cache get
      # `cache get`'s own tool (mathlib's `Cache.*`, compiled fresh by
      # this build) is not reproducible build-to-build -- measured
      # 2026-11-22, three distinct output hashes across four otherwise
      # identical builds. Prune its compiled binary and object files:
      # the gate's own `lake build` never imports `Cache.*` or runs the
      # `cache` executable again, so only the genuinely content-addressed
      # Mathlib cache this step downloaded needs to survive into $out.
      rm -rf .lake/packages/mathlib/.lake/build/bin
      rm -rf .lake/packages/mathlib/.lake/build/lib/lean/Cache
      rm -rf .lake/packages/mathlib/.lake/build/ir/Cache
      # A fixed-output derivation's own output must carry no Nix store
      # reference. `lake exe cache get` writes a handful of per-package
      # trace/marker files recording the absolute path of the Lean
      # toolchain used (measured 2026-11-22, 2-3 files, varying by run) --
      # evidence of validity, not the content Lake's own cache key hashes
      # (lakefile.lean's own comment: the cache key carries no absolute
      # path). Strip the literal store-path text from every plain-text
      # file that carries one; a binary file (.olean, .o, .c, .ir) never
      # matches `grep -I`'s own text heuristic, so this never touches
      # Mathlib's actual compiled output.
      grep -rlI --null "/nix/store/" .lake/packages 2>/dev/null \
        | xargs -0 -r sed -i 's#/nix/store/[a-z0-9]\{32\}-[^"[:space:]]*##g'
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p $out
      cp -r .lake/packages/. $out/
      runHook postInstall
    '';
    outputHashMode = "recursive";
    outputHashAlgo = "sha256";
    outputHash = "sha256-PQ3y2KEqrYl4DBMsM94dGb6ewqLWxw4YtBJnzXsJt5Q=";
  };
in
{
  inherit depSources packagesDir mathlibCache;
  # Every Lake dependency's own compiled `.olean` search root, joined
  # for `LEAN_PATH` -- what every ArmadaLean module's own per-module
  # derivation (nix/lean-build.nix) puts ahead of its internal deps.
  mathlibCacheLeanPath = lib.concatStringsSep ":" (
    map (name: "${mathlibCache}/${name}/.lake/build/lib/lean") (lib.attrNames depSources)
  );
}
