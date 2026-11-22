{
  description = "armada-lean: Nix-built commit-boundary gate image (docs/plans/nix-images.md Milestone 3, T3.lean + T3.x.b)";

  inputs = {
    # Pinned to exophial's own root nixpkgs input (its flake.lock
    # `nixpkgs_2`), per the operator's 2026-11-21 coordination: every
    # Nix-images-migration repo on the same host shares this pin, so a
    # store path is shared instead of rebuilding a second toolchain copy.
    nixpkgs.url = "github:NixOS/nixpkgs/ac62194c3917d5f474c1a844b6fd6da2db95077d";

    # Follows exophial's own nix2container/uv2nix/pyproject-nix/
    # pyproject-build-systems instances (its flake.lock pins all four
    # already): one build of each shared across every repo's gate image,
    # never a second copy built against a different nixpkgs pin.
    nix2container.follows = "exophial/nix2container";
    uv2nix.follows = "exophial/uv2nix";
    pyproject-nix.follows = "exophial/pyproject-nix";
    pyproject-build-systems.follows = "exophial/pyproject-build-systems";

    # The flake AND source tree of the merged coordination repo, pinned to
    # the same rev armada-sdk's own flake.nix already measured building
    # standalone (2026-11-22). The `github:` scheme gives a 404: the repo
    # is private, so the fetch uses an authenticated ssh URL instead.
    exophial = {
      url = "git+ssh://git@github.com/AFDudley/exophial.git?rev=84b680fc5519e326ab48e0a176ed9ad127417be1";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      nixpkgs,
      nix2container,
      uv2nix,
      pyproject-nix,
      pyproject-build-systems,
      exophial,
      ...
    }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      lib = pkgs.lib;
      n2c = nix2container.packages.${system}.nix2container;
      # lib.cleanSource: VCS cruft only (.git etc). The actual commit-
      # boundary gate run hands this flake an already-filtered, .git-free
      # judged-tree tar (gate_container._extract_context_tar), never this
      # live worktree -- this path only matters for a direct `nix build`
      # against a checkout.
      gateSrc = pkgs.lib.cleanSource ./.;

      pins = import ./nix/pins.nix { inherit pkgs; };
      leanToolchains = import ./nix/lean.nix { inherit pkgs; };
      leanDeps = import ./nix/lean-deps.nix {
        inherit pkgs lib;
        lean = leanToolchains.lean4350;
        leanToolchainFile = ./lean-toolchain;
        lakefileFile = ./lakefile.lean;
        lakeManifestFile = ./lake-manifest.json;
        exophialCoreDir = ./vendor/exophial_core;
      };
      leanBuild = import ./nix/lean-build.nix {
        inherit pkgs lib leanDeps gateSrc;
        lean = leanToolchains.lean4350;
      };
      exophialGate = import ./nix/gate.nix {
        inherit
          pkgs
          lib
          n2c
          pins
          gateSrc
          leanToolchains
          leanDeps
          leanBuild
          ;
        exophialPkg = exophial.packages.${system}.exophial;
      };
    in
    {
      packages.${system} = {
        exophial-gate = exophialGate;
        # `lake-deps`: armada-lean's own Lake dependency tree and
        # Mathlib's build cache, built ONCE from lean-toolchain,
        # lakefile.lean, lake-manifest.json and vendor/exophial_core
        # only (nix/lean-deps.nix) -- a fixed public contract another
        # repository's flake can take as a flake input and import
        # directly, with no second copy of this build.
        lake-deps = leanDeps.mathlibCache;
        armada-lean-build = leanBuild.allEntriesUnion;
      };
    };
}
