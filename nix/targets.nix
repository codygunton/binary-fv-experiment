{ pkgs, zesu, rv64 }:
let
  inherit (rv64) riscvBinutils riscvNm riscvReadelf;

  zesuRv64Object = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-rv64im-object";
    version = "d8071c4";
    src = zesu;
    nativeBuildInputs = [ pkgs.zig riscvBinutils ];
    dontConfigure = true;
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      zig build rv64im-object -Doptimize=ReleaseSmall
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p "$out/obj" "$out/meta"
      cp zig-out/lib/zesu.o "$out/obj/zesu.o"
      ${riscvReadelf} -h "$out/obj/zesu.o" > "$out/meta/elf-header.txt"
      ${riscvReadelf} -A "$out/obj/zesu.o" > "$out/meta/elf-attributes.txt"
      ${riscvNm} -u "$out/obj/zesu.o" > "$out/meta/undefined-symbols.txt"
      printf '%s\n' \
        'zesu=Consensys/zesu@d8071c422f0faf2c52d85b401192fdffc31fd5ac' \
        "zig=$(zig version)" > "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };
in
{
  public = {
    inherit zesuRv64Object;
    zesu-rv64-object = zesuRv64Object;
  };
}
