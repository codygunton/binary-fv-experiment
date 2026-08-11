{ pkgs, repo, zesu, rv64 }:
let
  inherit (rv64) cflags riscvBinutils riscvCc riscvNm riscvReadelf;

  zesuRv64Object = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-rv64im-object";
    version = "c36bb99";
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
        'zesu=codygunton/zesu@c36bb999627ef3818dee3f0e076ea63924760c2e' \
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

  zesuSszDecodeRv64Elf = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-decode-rv64im-elf";
    version = "c36bb99";
    dontUnpack = true;
    nativeBuildInputs = [ riscvBinutils ];
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      ${riscvCc} ${cflags} -g -mcmodel=medany -c \
        ${repo}/runtime/riscv64/riscv64_runtime.c -o runtime.o
      ${riscvCc} ${cflags} -g -mcmodel=medany -c \
        ${repo}/runtime/riscv64/riscv64_start.S -o start.o
      ${riscvCc} -nostdlib -static -no-pie -Wl,--gc-sections -Wl,--build-id=none \
        -Wl,-e,_start -march=${rv64.riscvArch} -mabi=${rv64.riscvAbi} -mcmodel=medany \
        start.o runtime.o ${zesuSszDecodeRv64Object}/obj/zesu-ssz-decode.o \
        -o zesu-ssz-decode.elf
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p "$out/bin" "$out/meta"
      cp zesu-ssz-decode.elf "$out/bin/zesu-ssz-decode"
      ${riscvReadelf} -h "$out/bin/zesu-ssz-decode" > "$out/meta/elf-header.txt"
      ${riscvReadelf} -A "$out/bin/zesu-ssz-decode" > "$out/meta/elf-attributes.txt"
      ${riscvNm} -u "$out/bin/zesu-ssz-decode" > "$out/meta/undefined-symbols.txt"
      test ! -s "$out/meta/undefined-symbols.txt"
      printf '%s\n' \
        'zesu=codygunton/zesu@c36bb999627ef3818dee3f0e076ea63924760c2e' \
        'runtime=runtime/riscv64; linux-riscv-syscall-abi; no-libc' \
        'optimize=ReleaseSmall; static=true; linked=true' > "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  zesuSszDecodeSmoke = pkgs.runCommand "zesu-ssz-decode-smoke-c36bb99" {
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    python ${repo}/tools/make_minimal_ssz.py minimal.ssz
    python ${repo}/tools/make_minimal_ssz.py invalid.ssz --mutation invalid-schema
    python ${repo}/tools/make_minimal_ssz.py block-number.ssz --mutation block-number

    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < minimal.ssz > success.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < minimal.ssz > repeated.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < invalid.ssz > rejected.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < block-number.ssz > changed.out

    test "$(od -An -tx1 -N6 success.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 -N6 changed.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 rejected.out | tr -d ' \n')" = 5a53535a0100
    test "$(wc -c < success.out)" = 703
    cmp success.out repeated.out
    ! cmp -s success.out changed.out
    mkdir -p "$out"
    cp success.out rejected.out changed.out "$out/"
  '';
in
{
  public = {
    inherit zesuRv64Object zesuSszDecodeRv64Object zesuSszDecodeRv64Elf zesuSszDecodeSmoke;
    zesu-rv64-object = zesuRv64Object;
    zesu-ssz-decode-rv64-object = zesuSszDecodeRv64Object;
    zesu-ssz-decode-rv64-elf = zesuSszDecodeRv64Elf;
    zesu-ssz-decode-smoke = zesuSszDecodeSmoke;
  };
}
