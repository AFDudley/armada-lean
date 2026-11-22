/*
  armada-lean's own ArmadaLean modules, ONE NIX DERIVATION PER LEAN MODULE
  (operator decision, 2026-11-22, superseding an earlier committed-cache
  design): a module's derivation takes its own source FILE and the
  derivations of the modules it imports as inputs, on top of `leanDeps`'s
  shared store path. Nix's own content-addressing is the cache -- a
  commit that changes one file gives ONLY that file's derivation, and
  every derivation that (transitively) imports it, a new store path;
  every other module's derivation is unchanged, so the host Nix daemon
  (which keeps its store between gate builds, `gate_container.
  run_host_nix_build`) never rebuilds it. No committed cache directory,
  no podman volume: this is the same pattern Lean 4's own retired
  `buildLeanPackage` and the `lean4-nix` flake use for a Lake package.

  Import parsing is pure Nix text processing, not an `import`-from-
  derivation step: every `ArmadaLean/**.lean` file lists its own imports
  as plain `import Foo.Bar` lines (Lean's own syntax), read with
  `builtins.readFile` + `builtins.match`. Only imports inside this
  package's own `ArmadaLean.` namespace become a module-to-module Nix
  edge; everything else (Mathlib, Lean core, the other Lake
  dependencies) is satisfied once, by `leanDeps`'s own shared LEAN_PATH,
  the same way every module already depends on it.
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

  # Every `.lean` file under ArmadaLean/, as { relPath, path }. relPath is
  # repo-relative with the `ArmadaLean/` prefix, e.g.
  # "ArmadaLean/Nitro/Liveness.lean".
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

  # `vendor/exophial_core`'s own Lean files are in scope too (its
  # `Exophial` namespace, root AT the package directory -- its own
  # `lakefile.toml` names the library `Exophial`, rooted so that
  # `Exophial.lean` itself is the module `Exophial`): ArmadaLean imports
  # it as a normal dependency, and it is small enough to build the same
  # one-derivation-per-module way, never a separate FOD.
  leanFiles = [
    {
      path = gateSrc + "/ArmadaLean.lean";
      relPath = "ArmadaLean.lean";
      root = gateSrc;
    }
  ] ++ walk gateSrc leanRoot "ArmadaLean" ++ walk exophialCoreRoot exophialCoreRoot "";

  # "ArmadaLean/Nitro/Liveness.lean" -> "ArmadaLean.Nitro.Liveness"
  moduleNameOf = relPath: lib.replaceStrings [ "/" ] [ "." ] (lib.removeSuffix ".lean" relPath);

  # Every `import Foo.Bar` line in a file, in source order. Lean requires
  # the import block to precede all other code, but a line-based scan
  # over the WHOLE file (rather than stopping at the first non-import
  # line) tolerates the rare non-import line this scan would otherwise
  # need to detect as the block's end; a literal `import ` line inside a
  # string or comment is not idiomatic Lean 4 and none occurs in this
  # package (confirmed: every matched line, across all ~93 files, names
  # a real module this package or a Lake dependency actually provides).
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

  # `weak.says.no_verify_in_CI` (lakefile.lean's own `leanOptions`): a
  # recorded `says` search is not re-verified in a normal build. Mathlib's
  # `Says.lean` only re-verifies when `CI` is set, which this build does
  # not set, but the project's own lakefile states the option explicitly
  # rather than relying on an absent environment variable.
  leanOptionArgs = [
    "-D"
    "weak.says.no_verify_in_CI=true"
  ];
  # Lean must resolve a TRANSITIVE import too when it loads a module's
  # own `.olean` (loading `Exophial.CheckSpecBindings` also loads
  # `Exophial.SpecBindings`, which it itself imports) -- a module's own
  # `LEAN_PATH` needs every internal module reachable, not only its
  # direct imports. `transitiveInternal` is the same lazy,
  # self-referential recursive-attrset trick as `moduleDrvs` below, over
  # module NAMES rather than derivations.
  transitiveInternal = lib.mapAttrs (
    _name: entry:
    let
      internalImports = lib.filter isInternal (importsOf entry.path);
    in
    lib.unique (internalImports ++ lib.concatMap (d: transitiveInternal.${d}) internalImports)
  ) modulesByName;

  # One derivation per module, built lazily and self-referentially: each
  # module's own derivation looks up `moduleDrvs.${dep}` for its internal
  # imports, so Nix evaluates and builds each module's derivation exactly
  # once, however many other modules import it.
  moduleDrvs = lib.mapAttrs (
    name: entry:
    let
      depDrvs = map (d: moduleDrvs.${d}) transitiveInternal.${name};
      # `symlinkJoin` only merges at the TOP level: two internal
      # dependencies that share a leading namespace component (e.g.
      # `Exophial.CheckSpecBindings` and `Exophial.SpecBindings`, both
      # under `Exophial/`) collide there instead of merging their
      # nested `.olean` files -- measured 2026-11-22: Lean resolved
      # `Exophial.SpecBindings` against the FIRST `Exophial/`-rooted
      # LEAN_PATH entry it found and reported it missing there, never
      # falling through to the entry that actually has it. A plain
      # recursive `cp` merge (every input is a disjoint file within its
      # own dotted-name path, so no two inputs ever name the same file)
      # merges nested directories correctly.
      mergedDeps = pkgs.runCommand "armada-lean-deps-${lib.replaceStrings [ "." ] [ "-" ] name}" { } (
        "mkdir -p $out\n"
        + lib.concatMapStringsSep "\n" (d: "cp -r --no-preserve=mode,ownership ${d}/. $out/") depDrvs
      );
      leanPath = lib.concatStringsSep ":" (
        [ "${leanDeps.mathlibCacheLeanPath}" ] ++ lib.optional (depDrvs != [ ]) "${mergedDeps}"
      );
      outPath = "${entry.relPath}";
      olean = lib.removeSuffix ".lean" outPath + ".olean";
    in
    pkgs.stdenv.mkDerivation {
      pname = "armada-lean-module-${lib.replaceStrings [ "." ] [ "-" ] name}";
      version = "0";
      dontUnpack = true;
      nativeBuildInputs = [ lean ];
      buildPhase = ''
        runHook preBuild
        mkdir -p "$(dirname "${olean}")"
        LEAN_PATH="${leanPath}" ${lean}/bin/lean ${lib.concatStringsSep " " leanOptionArgs} \
          --root="${entry.root}" -o "${olean}" "${entry.path}"
        runHook postBuild
      '';
      installPhase = ''
        runHook preInstall
        mkdir -p "$out/$(dirname "${olean}")"
        cp "${olean}" "$out/${olean}"
        runHook postInstall
      '';
    }
  ) modulesByName;

  # The union of every module's own derivation output, assembled at the
  # layout `lean`/`LEAN_PATH` expects (one tree, every `.olean` at its
  # dotted-name path) -- what the gate image ships as the project's own
  # pre-built half of `.lake/build`'s search path.
  allModulesUnion = pkgs.symlinkJoin {
    name = "armada-lean-modules";
    paths = lib.attrValues moduleDrvs;
  };
in
{
  inherit moduleDrvs allModulesUnion;
}
