{ pkgs, repo, zesu, rv64 }:
let
  inherit (rv64) cflags riscvBinutils riscvCc riscvNm riscvReadelf;
  # Keep the production ELF independent of unrelated files in the outer repository.  This source
  # path changes only when the linked runtime itself changes, so its DWARF paths and ELF digest are
  # stable while proof, UI, fixture, or documentation files evolve.
  runtimeSrc = builtins.path {
    path = ../runtime/riscv64;
    name = "binary-fv-riscv64-runtime";
  };

  mcl = pkgs.stdenv.mkDerivation {
    pname = "mcl";
    version = "3.06";
    src = pkgs.fetchFromGitHub {
      owner = "herumi";
      repo = "mcl";
      rev = "0499298adcfad3bbcebf77f17700ebbe97166060";
      hash = "sha256-Nyd8SyURTpExgvB2B/uEfhEBU7YLQgNY6s1saQ1rS1Y=";
    };
    nativeBuildInputs = [ pkgs.gnumake pkgs.python3 pkgs.stdenv.cc pkgs.gmp ];
    buildPhase = "make -j$NIX_BUILD_CORES MCL_FP_BIT=384 MCL_FR_BIT=256";
    installPhase = ''
      mkdir -p "$out/lib" "$out/include"
      cp lib/libmcl.so lib/libmcl.a "$out/lib/"
      cp -r include/mcl "$out/include/"
    '';
  };

  nativeCrypto = pkgs.symlinkJoin {
    name = "zesu-native-crypto";
    paths = [ pkgs.blst mcl pkgs.secp256k1 pkgs.openssl.dev pkgs.openssl.out ];
  };

  zesuRv64Object = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-rv64im-object";
    version = "e5f8c13";
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
        'zesu=codygunton/zesu@e5f8c13a691b61f8a6e67d7e7c646638c8bdf467' \
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
    version = "e5f8c13";
    dontUnpack = true;
    nativeBuildInputs = [ riscvBinutils ];
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      ${riscvCc} ${cflags} -g -mcmodel=medany -c \
        ${runtimeSrc}/riscv64_runtime.c -o runtime.o
      ${riscvCc} ${cflags} -g -mcmodel=medany -c \
        ${runtimeSrc}/riscv64_start.S -o start.o
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
        'zesu=codygunton/zesu@e5f8c13a691b61f8a6e67d7e7c646638c8bdf467' \
        'runtime=runtime/riscv64; linux-riscv-syscall-abi; no-libc' \
        'optimize=ReleaseSmall; static=true; linked=true' > "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  zesuSszDecodeSmoke = pkgs.runCommand "zesu-ssz-decode-smoke-e5f8c13" {
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    python ${repo}/tools/make_minimal_ssz.py minimal.ssz
    python ${repo}/tools/make_minimal_ssz.py invalid.ssz --mutation invalid-schema
    python ${repo}/tools/make_minimal_ssz.py block-number.ssz --mutation block-number
    python ${repo}/tools/make_minimal_ssz.py chain-id-zero.ssz --mutation chain-id-zero
    python ${repo}/tools/make_minimal_ssz.py legacy-requests.ssz --mutation legacy-requests
    python ${repo}/tools/make_minimal_ssz.py legacy-payload.ssz --mutation legacy-payload
    python ${repo}/tools/make_minimal_ssz.py future-activation.ssz --mutation future-activation
    python ${repo}/tools/make_minimal_ssz.py extra-data-33.ssz --mutation extra-data-33
    python ${repo}/tools/make_minimal_ssz.py public-key-overflow.ssz --mutation public-key-overflow
    python ${repo}/tools/make_minimal_ssz.py versioned-hash-overflow.ssz --mutation versioned-hash-overflow

    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < minimal.ssz > success.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < minimal.ssz > repeated.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < invalid.ssz > rejected.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < block-number.ssz > changed.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < chain-id-zero.ssz > chain-id-zero.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < legacy-requests.ssz > legacy-requests.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < legacy-payload.ssz > legacy-payload.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < future-activation.ssz > future-activation.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < extra-data-33.ssz > extra-data-33.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < public-key-overflow.ssz > public-key-overflow.out
    ${rv64.qemuRiscv64} ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      < versioned-hash-overflow.ssz > versioned-hash-overflow.out

    test "$(od -An -tx1 -N6 success.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 -N6 changed.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 rejected.out | tr -d ' \n')" = 5a53535a0100
    test "$(wc -c < success.out)" = 703
    cmp success.out repeated.out
    ! cmp -s success.out changed.out
    mkdir -p "$out"
    test "$(od -An -tx1 -N6 legacy-requests.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 -N6 legacy-payload.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 -N6 future-activation.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 -N6 extra-data-33.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 -N6 public-key-overflow.out | tr -d ' \n')" = 5a53535a0101
    test "$(od -An -tx1 -N6 versioned-hash-overflow.out | tr -d ' \n')" = 5a53535a0101
    cp minimal.ssz invalid.ssz block-number.ssz chain-id-zero.ssz legacy-requests.ssz \
      legacy-payload.ssz future-activation.ssz extra-data-33.ssz public-key-overflow.ssz \
      versioned-hash-overflow.ssz success.out rejected.out changed.out \
      chain-id-zero.out legacy-requests.out legacy-payload.out future-activation.out \
      extra-data-33.out public-key-overflow.out versioned-hash-overflow.out "$out/"
  '';

  zesuSszDecodeSourceProbe = pkgs.stdenv.mkDerivation {
    pname = "zesu-ssz-decode-source-probe";
    version = "e5f8c13";
    src = zesu;
    nativeBuildInputs = [ pkgs.zig pkgs.pkg-config ];
    buildInputs = [ pkgs.secp256k1 pkgs.openssl ];
    dontConfigure = true;
    dontFixup = true;
    buildPhase = ''
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      zig build ssz-decode-probe -Doptimize=ReleaseSafe -Dcrypto-prefix=${nativeCrypto}
    '';
    installPhase = ''
      mkdir -p "$out/bin"
      cp zig-out/bin/zesu-ssz-decode-probe "$out/bin/"
    '';
    doInstallCheck = true;
    installCheckPhase = ''
      export LD_LIBRARY_PATH=${nativeCrypto}/lib
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/minimal.ssz > native.out
      cmp native.out ${zesuSszDecodeSmoke}/success.out
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/chain-id-zero.ssz > native-zero.out
      cmp native-zero.out ${zesuSszDecodeSmoke}/chain-id-zero.out
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/legacy-requests.ssz > native-legacy.out
      cmp native-legacy.out ${zesuSszDecodeSmoke}/legacy-requests.out
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/legacy-payload.ssz > native-v3.out
      cmp native-v3.out ${zesuSszDecodeSmoke}/legacy-payload.out
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/future-activation.ssz > native-future.out
      cmp native-future.out ${zesuSszDecodeSmoke}/future-activation.out
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/extra-data-33.ssz > native-extra.out
      cmp native-extra.out ${zesuSszDecodeSmoke}/extra-data-33.out
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/public-key-overflow.ssz > native-keys.out
      cmp native-keys.out ${zesuSszDecodeSmoke}/public-key-overflow.out
      "$out/bin/zesu-ssz-decode-probe" < ${zesuSszDecodeSmoke}/versioned-hash-overflow.ssz > native-hashes.out
      cmp native-hashes.out ${zesuSszDecodeSmoke}/versioned-hash-overflow.out
    '';
  };
in
{
  public = {
    inherit zesuRv64Object zesuSszDecodeRv64Object zesuSszDecodeRv64Elf zesuSszDecodeSmoke
      zesuSszDecodeSourceProbe;
    zesu-rv64-object = zesuRv64Object;
    zesu-ssz-decode-rv64-object = zesuSszDecodeRv64Object;
    zesu-ssz-decode-rv64-elf = zesuSszDecodeRv64Elf;
    zesu-ssz-decode-smoke = zesuSszDecodeSmoke;
  };
}
