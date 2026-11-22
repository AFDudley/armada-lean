/*
  The Lean toolchains this repository's gate needs, elan-less (D11): both
  pinned release tarballs, patched with autoPatchelfHook, plus a dispatch
  shim that reads a tree's own `lean-toolchain` file and execs the matching
  binary -- elan's own job, with no network and no elan.

  Byte-identical construction and hashes to exophial's own nix/gate.nix
  (`mkLean`, `lean4331`, `lean4350`): the upstream release tarballs are the
  same regardless of which repository's flake downloads them, so the
  store path is shared, not rebuilt a second time.

  v4.35.0 is `lean-toolchain`'s own pin. v4.33.1 is kept so that a tree
  from before the v4.35.0 move still builds in this image
  (.exophial/gate/Dockerfile's own comment; exophial's env_change_e2e
  grades the parent tree in the new image too).
*/
{ pkgs }:
let
  mkLean = version: hash: pkgs.stdenv.mkDerivation {
    pname = "lean4";
    inherit version;
    src = pkgs.fetchurl {
      url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-linux.tar.zst";
      inherit hash;
    };
    nativeBuildInputs = [ pkgs.autoPatchelfHook pkgs.zstd ];
    buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.gmp pkgs.libuv pkgs.zlib ];
    unpackCmd = ''
      zstd -d --stdout "$curSrc" | tar -x
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p $out
      cp -r --no-preserve=ownership . $out/
      chmod -R u+w $out
      find $out/bin -maxdepth 1 -type f -exec chmod +x {} +
      runHook postInstall
    '';
  };

  lean4331 = mkLean "4.33.1" "sha256-iQr9GFNw+FZmAluIORSrT0szkTb4yWFntpz7Yq7K8jU=";
  lean4350 = mkLean "4.35.0" "sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=";

  leanDispatchScript = name: pkgs.writeShellScriptBin name ''
    set -e
    # No default toolchain: a project without a `lean-toolchain` file, or
    # one that names a version this image does not install, is refused, so
    # no project is ever built with a compiler it did not ask for.
    dir="$PWD"
    while [ "$dir" != "/" ] && [ ! -f "$dir/lean-toolchain" ]; do
      dir="$(dirname "$dir")"
    done
    if [ ! -f "$dir/lean-toolchain" ]; then
      echo "${name}: no lean-toolchain file in $PWD or any parent directory" >&2
      exit 2
    fi
    toolchain="$(tr -d '[:space:]' < "$dir/lean-toolchain")"
    case "$toolchain" in
      leanprover/lean4:v4.35.0) exec ${lean4350}/bin/${name} "$@" ;;
      leanprover/lean4:v4.33.1) exec ${lean4331}/bin/${name} "$@" ;;
      *)
        echo "${name}: $dir/lean-toolchain names '$toolchain'; this image installs leanprover/lean4:v4.35.0 and leanprover/lean4:v4.33.1 only" >&2
        exit 2
        ;;
    esac
  '';
  leanDispatch = pkgs.symlinkJoin {
    name = "lean4-dispatch";
    paths = map leanDispatchScript [ "lean" "lake" "leanc" "lean4checker" ];
  };
in
{
  inherit lean4331 lean4350 leanDispatch;
}
