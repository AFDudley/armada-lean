/*
  armada-lean's own ArmadaLean modules, ONE NIX DERIVATION PER LEAN MODULE,
  each running `lake build <Module>` -- not `lean` directly (operator
  decision, 2026-11-22, second revision). lakefile.lean already sets
  `enableArtifactCache := true` and `restoreAllArtifacts := true`
  (commit e919b4c): Lake itself puts a compiled module into its own
  content-addressed artifact-cache layout (`LAKE_CACHE_DIR`'s
  `outputs/<package>/*.json` manifests plus the `artifacts/` blobs they
  name) and writes the matching trace files no hand-written code needs
  to reproduce.

  A module's derivation:
    - seeds `LAKE_CACHE_DIR` from the MERGED artifact-cache entries of
      every module it transitively imports (each already its own Nix
      derivation output, below);
    - assembles a project tree carrying only the module's own source
      file and its transitive imports' source files (never the whole
      judged tree), on top of `leanDeps`'s shared Lake dependency tree;
    - runs `lake build <Module>`, which restores every imported entry
      from the seed (0 compiles for those) and compiles only the module
      itself;
    - its OWN output is whatever `lake build` added to `LAKE_CACHE_DIR`
      that was not already in the seed -- that module's own
      artifact-cache entry, found by a before/after file-list diff
      (Lake's own manifest filenames are content hashes, not module
      names, so there is no other way to single out "the new one").

  Nix's own store is the cache: a commit that changes one file gives a
  new derivation only for that module and the modules that (transitively)
  import it; every other module's derivation, and the merged
  `LAKE_CACHE_DIR` the gate image ships (nix/gate.nix), is unchanged.
*/
{
  pkgs,
  lib,
  lean,
  gateSrc,
  leanDeps,
}:
let
  leanRoot = gateSrc + "/ArmadaLean";
  exophialCoreRoot = gateSrc + "/vendor/exophial_core";

  walk =
    root: dir: prefix:
    let
      entries = builtins.readDir dir;
    in
    lib.concatMap (
      name:
      let
        entryType = entries.${name};
        path = dir + "/${name}";
        relPath = if prefix == "" then name else "${prefix}/${name}";
      in
      if entryType == "directory" then
        walk root path relPath
      else if entryType == "regular" && lib.hasSuffix ".lean" name then
        [
          {
            inherit path relPath root;
          }
        ]
      else
        [ ]
    ) (builtins.attrNames entries);

  leanFiles = [
    {
      path = gateSrc + "/ArmadaLean.lean";
      relPath = "ArmadaLean.lean";
      root = gateSrc;
    }
  ] ++ walk gateSrc leanRoot "ArmadaLean" ++ walk exophialCoreRoot exophialCoreRoot "";

  moduleNameOf = relPath: lib.replaceStrings [ "/" ] [ "." ] (lib.removeSuffix ".lean" relPath);

  importsOf =
    path:
    let
      content = builtins.readFile path;
      lines = lib.splitString "\n" content;
      tryMatch = line: builtins.match "import[ \t]+([A-Za-z0-9_'.]+)[ \t]*" line;
      matches = lib.filter (m: m != null) (map tryMatch lines);
    in
    map builtins.head matches;

  modulesByName = lib.listToAttrs (
    map (f: {
      name = moduleNameOf f.relPath;
      value = f;
    }) leanFiles
  );

  isInternal =
    name: (lib.hasPrefix "ArmadaLean" name || lib.hasPrefix "Exophial" name) && modulesByName ? ${name};

  # The package name EACH internal module belongs to, for Lake's own
  # `outputs/<package>/` cache layout: everything under `ArmadaLean/` (and
  # the root `ArmadaLean.lean`) is the `armada-lean` package; everything
  # from `vendor/exophial_core` is the `exophial_core` package (its own
  # `lakefile.toml`'s `name`).
  packageOf = name: if lib.hasPrefix "Exophial" name then "exophial_core" else "armada-lean";

  transitiveInternal = lib.mapAttrs (
    _name: entry:
    let
      internalImports = lib.filter isInternal (importsOf entry.path);
    in
    lib.unique (internalImports ++ lib.concatMap (d: transitiveInternal.${d}) internalImports)
  ) modulesByName;

  # One derivation per module: its own artifact-cache entry.
  moduleCacheEntry = lib.mapAttrs (
    name: entry:
    let
      depNames = transitiveInternal.${name};
      depEntries = map (d: moduleCacheEntry.${d}) depNames;
      allEntries = [ name ] ++ depNames;
      allSourceEntries = map (n: modulesByName.${n}) allEntries;

      # The merged artifact-cache seed: every transitively-imported
      # module's own cache entry, recursively merged (plain `cp`, not
      # `symlinkJoin`: two entries can share a package-name top
      # directory, e.g. `outputs/armada-lean/`, the same collision
      # nix/lean-deps.nix's own dependency merge hit).
      seedCache = pkgs.runCommand "armada-lean-cache-seed-${lib.replaceStrings [ "." ] [ "-" ] name}" { } (
        "mkdir -p $out\n"
        + lib.concatMapStringsSep "\n" (d: "cp -r --no-preserve=mode,ownership ${d}/. $out/") depEntries
      );

      # The project tree this module's own `lake build` needs: only its
      # own source file and its transitive imports' own source files,
      # each at its real repo-relative path.
      srcTree = pkgs.runCommand "armada-lean-src-${lib.replaceStrings [ "." ] [ "-" ] name}" { } (
        "mkdir -p $out\n"
        + lib.concatMapStringsSep "\n" (
          e: "mkdir -p \"$out/$(dirname '${e.relPath}')\" && cp '${e.path}' \"$out/${e.relPath}\""
        ) allSourceEntries
      );
    in
    pkgs.stdenv.mkDerivation {
      pname = "armada-lean-cache-entry-${lib.replaceStrings [ "." ] [ "-" ] name}";
      version = "0";
      dontUnpack = true;
      nativeBuildInputs = [
        lean
        pkgs.gcc
        pkgs.gitMinimal
      ];
      buildPhase = ''
        runHook preBuild
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME"
        export LEAN_CC=${pkgs.gcc}/bin/cc

        mkdir -p build/.lake/packages build/vendor
        cp -r --no-preserve=mode,ownership ${leanDeps.mathlibCache}/. build/.lake/packages/
        cp ${gateSrc}/lean-toolchain build/lean-toolchain
        cp ${gateSrc}/lakefile.lean build/lakefile.lean
        cp ${gateSrc}/lake-manifest.json build/lake-manifest.json
        cp -r ${gateSrc}/vendor/exophial_core build/vendor/exophial_core
        chmod -R u+w build/vendor
        cp -r ${srcTree}/. build/

        export LAKE_CACHE_DIR="$TMPDIR/lake-cache"
        mkdir -p "$LAKE_CACHE_DIR"
        cp -r ${seedCache}/. "$LAKE_CACHE_DIR"/
        chmod -R u+w "$LAKE_CACHE_DIR"
        ( cd "$LAKE_CACHE_DIR" && find . -type f | sort ) > "$TMPDIR/cache-before.txt"

        cd build
        # `+<module>` forces Lake to resolve the argument as a MODULE
        # name, never a declared library/exe TARGET. Without it, `lake
        # build ArmadaLean` resolves to the `lean_lib «ArmadaLean»`
        # TARGET instead of the one module named `ArmadaLean` (same
        # name, by construction -- `lakefile.lean`'s root aggregator
        # module and its library share one name), and a target build
        # compiles every declared root of that library, including
        # `ArmadaLean.Machines` -- which this module's own srcTree does
        # not carry, since `ArmadaLean.lean` does not import it
        # (measured 2026-11-22: "no such file or directory …
        # ArmadaLean/Machines.lean" after ~1,100 modules had already
        # compiled, meaning the whole library built before failing).
        lake build +${name}
        cd ..

        ( cd "$LAKE_CACHE_DIR" && find . -type f | sort ) > "$TMPDIR/cache-after.txt"
        comm -13 "$TMPDIR/cache-before.txt" "$TMPDIR/cache-after.txt" > "$TMPDIR/cache-new.txt"
        runHook postBuild
      '';
      installPhase = ''
        runHook preInstall
        mkdir -p $out
        while IFS= read -r f; do
          mkdir -p "$out/$(dirname "$f")"
          cp "$LAKE_CACHE_DIR/$f" "$out/$f"
        done < "$TMPDIR/cache-new.txt"
        # A fixed point (nothing new -- every import, and this module
        # itself, was already in the seed) still ships a valid, if
        # empty, cache-entry tree.
        mkdir -p "$out/outputs/${packageOf name}"
        mkdir -p "$out/artifacts"
        runHook postInstall
      '';
    }
  ) modulesByName;

  allEntriesUnion = pkgs.runCommand "armada-lean-cache-entries-merged" { } (
    "mkdir -p $out\n"
    + lib.concatMapStringsSep "\n" (d: "cp -r --no-preserve=mode,ownership ${d}/. $out/") (
      lib.attrValues moduleCacheEntry
    )
  );
in
{
  inherit moduleCacheEntry allEntriesUnion;
}
