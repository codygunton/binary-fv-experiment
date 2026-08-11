{ pkgs, zesu, rv64 }:
let
  inherit (rv64) riscvBinutils riscvNm riscvReadelf;

  zesuRv64Object = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-rv64im-object";
    version = "6acdbd9";
    src = zesu;
    nativeBuildInputs = [ pkgs.zig riscvBinutils ];
    dontConfigure = true;
    dontFixup = true;

    # Zig strips local symbols and DWARF from ReleaseSmall modules by default.  Retain them in the
    # same optimized object so source locations describe the analyzed instructions, rather than a
    # separately optimized Debug build with different code addresses.
    postPatch = ''
      substituteInPlace build.zig \
        --replace-fail \
          'rv64_obj.root_module.code_model = .medium;' \
          $'rv64_obj.root_module.code_model = .medium;\n        rv64_obj.root_module.strip = false;'
      substituteInPlace build.zig \
        --replace-fail \
          'decode_obj.root_module.code_model = .medium;' \
          $'decode_obj.root_module.code_model = .medium;\n        decode_obj.root_module.strip = false;'
    '';

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
        'zesu=codygunton/zesu@6acdbd90e7d9f543863bf4030d0e649553704558' \
        'upstream-base=Consensys/zesu@d8071c422f0faf2c52d85b401192fdffc31fd5ac' \
        'optimize=ReleaseSmall; debug-metadata=retained-in-analyzed-object' \
        "zig=$(zig version)" > "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  zesuSszDecodeRv64Object = zesuRv64Object.overrideAttrs (old: {
    pname = "zesu-ssz-decode-rv64im-object";
    buildPhase = builtins.replaceStrings
      [ "zig build rv64im-object" ] [ "zig build rv64im-ssz-decode-object" ] old.buildPhase;
    installPhase = builtins.replaceStrings
      [ "zig-out/lib/zesu.o" "$out/obj/zesu.o" ]
      [ "zig-out/lib/zesu-ssz-decode.o" "$out/obj/zesu-ssz-decode.o" ]
      old.installPhase;
  });
in
{
  public = {
    inherit zesuRv64Object zesuSszDecodeRv64Object;
    zesu-rv64-object = zesuRv64Object;
    zesu-ssz-decode-rv64-object = zesuSszDecodeRv64Object;
  };
}
