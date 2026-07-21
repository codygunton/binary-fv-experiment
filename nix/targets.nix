{ pkgs
, source
, repo
, reth
, zesu
, zesuRepaired
, rv64
}:
let
  inherit (rv64)
    cflags
    lib
    qemuRiscv64
    riscvBinutils
    riscvCc
    riscvNm
    riscvPkgs
    riscvReadelf;

  zesuProductionRevision = "aa6c94339987d278acb8b7fa409c864dbd3d05aa";
  zesuRepairedRevision = "96f1621468ba54755d653f19cbc9704e789be001";

  # Cargo's build-std mode insists that the Rust source and vendored dependency lock live
  # inside its sysroot. Keep that sysroot derivation separate from the target archive so
  # both the compiler and its source provenance stay pinned by nixpkgs.
  rustBuildStdSysroot = pkgs.symlinkJoin {
    name = "rustc-with-build-std-src";
    paths = [ pkgs.rustc.unwrapped ];
    postBuild = ''
      mkdir -p "$out/lib/rustlib/src"
      cp -rs ${pkgs.rustPlatform.rustcSrc} "$out/lib/rustlib/src/rust"
      chmod -R u+w "$out/lib/rustlib/src/rust/.cargo"
      rm "$out/lib/rustlib/src/rust/.cargo/config.toml"
      cat > "$out/lib/rustlib/src/rust/.cargo/config.toml" <<EOF
      [source.crates-io]
      replace-with = "vendored-sources"

      [source."git+https://github.com/rust-lang/team"]
      git = "https://github.com/rust-lang/team"
      replace-with = "vendored-sources"

      [source.vendored-sources]
      directory = "${pkgs.rustPlatform.rustVendorSrc}"
      EOF
    '';
  };
  rustcWithBuildStd = pkgs.rustc.override { sysroot = rustBuildStdSysroot; };

  rethProvenance = pkgs.runCommand "reth-v2.3.0-provenance" {
    nativeBuildInputs = [ pkgs.coreutils ];
  } ''
    actual="$(${pkgs.coreutils}/bin/sha256sum ${reth}/Cargo.lock | cut -d ' ' -f 1)"
    test "$actual" = "39867b4a9bae8c97872ce4f51ae184c13ba3db2c57b9c6772e31e83711866b97"
    mkdir -p "$out"
    printf '%s\n' "reth=9384bc53d8c0c77e59cac83fdaaf3b372c6d2216" > "$out/provenance.txt"
    printf '%s\n' "cargo-lock-sha256=$actual" >> "$out/provenance.txt"
  '';

  rethKeccakRust = pkgs.rustPlatform.buildRustPackage {
    pname = "reth-keccak-rustcrypto-rv64im";
    version = "2.3.0";
    src = repo + "/targets/keccak/reth-rustcrypto/wrapper";
    cargoHash = "sha256-MmGOI6g2PWXNbL55+Q+v6+OYIRBtjTbMT7D+OmyLoJQ=";
    nativeBuildInputs = [ pkgs.cargo rustcWithBuildStd rethProvenance ];
    RUSTC = "${rustcWithBuildStd}/bin/rustc";
    RUSTC_BOOTSTRAP = "1";
    RUSTFLAGS = "-C target-feature=+m,+zicclsm";
    doCheck = false;
    buildPhase = ''
      runHook preBuild
      test -f ${rethProvenance}/provenance.txt
      mkdir -p .cargo

      # cargoSetupHook vendors this wrapper's crates beside the source. build-std also
      # resolves Rust's own workspace crates, so combine the two immutable vendor trees
      # before replacing Cargo's wrapper-only source configuration.
      wrapper_vendor="$(find "$NIX_BUILD_TOP" -maxdepth 1 -type d -name '*-vendor' -print -quit)"
      test -n "$wrapper_vendor"
      wrapper_vendor="$wrapper_vendor/source-registry-0"
      test -d "$wrapper_vendor"
      mkdir -p combined-vendor
      for vendor in ${pkgs.rustPlatform.rustVendorSrc} "$wrapper_vendor"; do
        for directory in "$vendor"/*; do
          name="$(basename "$directory")"
          if [ "$name" != "Cargo.lock" ] && [ "$name" != ".cargo" ] \
            && [ ! -e "combined-vendor/$name" ]; then
            ln -s "$directory" "combined-vendor/$name"
          fi
        done
      done
      cat > .cargo/config.toml <<EOF
      [source.crates-io]
      replace-with = "merged-vendor"

      [source."git+https://github.com/rust-lang/team"]
      git = "https://github.com/rust-lang/team"
      replace-with = "merged-vendor"

      [source.merged-vendor]
      directory = "$(pwd)/combined-vendor"
      EOF
      cargo build --locked --release -Zbuild-std=core,compiler_builtins \
        --target riscv64im-unknown-none-elf
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p "$out/lib"
      cp target/riscv64im-unknown-none-elf/release/libreth_keccak_wrapper.a \
        "$out/lib/libreth_keccak_wrapper.a"
      runHook postInstall
    '';
  };

  rethKeccak = pkgs.stdenvNoCC.mkDerivation {
    pname = "reth-keccak-rv64im-zicclsm";
    version = "2.3.0";
    src = source;

    nativeBuildInputs = [
      pkgs.python3
      pkgs.qemu-user
      riscvPkgs.stdenv.cc
      riscvBinutils
    ];

    hardeningDisable = [ "all" ];
    dontConfigure = true;
    dontBuild = true;
    dontFixup = true;

    installPhase = ''
      runHook preInstall

      mkdir -p "$out/bin" "$out/obj" "$out/meta"
      export NIX_HARDENING_ENABLE=""
      cp ${rethProvenance}/provenance.txt "$out/meta/provenance.txt"

      ${riscvCc} ${cflags} -c ${repo}/targets/keccak/reth-rustcrypto/adapter/main.c \
        -o "$out/obj/reth-keccak-main.o"
      ${riscvCc} ${cflags} -c ${repo}/targets/common/riscv64_runtime.c \
        -o "$out/obj/riscv64_runtime.o"
      ${riscvCc} ${cflags} -c ${repo}/targets/common/riscv64_start.S \
        -o "$out/obj/riscv64_start.o"

      ${riscvCc} ${cflags} -nostdlib -static -no-pie \
        "$out/obj/riscv64_start.o" \
        "$out/obj/reth-keccak-main.o" \
        "${rethKeccakRust}/lib/libreth_keccak_wrapper.a" \
        "$out/obj/riscv64_runtime.o" \
        -lgcc \
        -Wl,--gc-sections \
        -Wl,-e,_start \
        -Wl,-Map,"$out/meta/reth-keccak.map" \
        -o "$out/bin/reth-keccak"

      printf '%s\n' reth_keccak256 main > "$out/meta/selected-symbols"
      ${riscvReadelf} -h "$out/bin/reth-keccak" > "$out/meta/elf-header.txt"
      ${riscvReadelf} -A "$out/bin/reth-keccak" > "$out/meta/elf-attributes.txt"
      ${riscvNm} -S --size-sort --radix=d "$out/bin/reth-keccak" > "$out/meta/symbols.txt"
      ${pkgs.python3}/bin/python ${repo}/targets/keccak/reth-rustcrypto/tests/check_vectors.py \
        --qemu ${qemuRiscv64} \
        --binary "$out/bin/reth-keccak" \
        --vectors ${repo}/targets/keccak/reth-rustcrypto/tests/vectors.json

      runHook postInstall
    '';
  };

  zesuProductionObject = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-production-rv64im-object";
    version = "aa6c943";
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
      cp zig-out/lib/zesu.o "$out/obj/zesu-production.o"
      ${riscvReadelf} -h "$out/obj/zesu-production.o" > "$out/meta/elf-header.txt"
      ${riscvReadelf} -A "$out/obj/zesu-production.o" > "$out/meta/elf-attributes.txt"
      ${riscvNm} -u "$out/obj/zesu-production.o" > "$out/meta/undefined-symbols.txt"
      printf '%s\n' "zesu=Consensys/zesu@${zesuProductionRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  zesuRawObject = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-raw-ssz-rv64im-object";
    version = "96f1621";
    src = zesuRepaired;
    nativeBuildInputs = [ pkgs.zig riscvBinutils ];
    dontConfigure = true;
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      zig build rv64im-raw-ssz-object -Doptimize=ReleaseSmall
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p "$out/obj" "$out/meta"
      cp zig-out/lib/zesu_raw_ssz_allocator.o "$out/obj/zesu-raw-ssz-allocator.o"
      cp zig-out/lib/zesu_raw_ssz.o "$out/obj/zesu-raw-ssz-decoder.o"
      cp zig-out/lib/zesu_raw_ssz_sink.o "$out/obj/zesu-raw-ssz-sink.o"
      ${riscvReadelf} -h "$out/obj/zesu-raw-ssz-allocator.o" \
        > "$out/meta/allocator-elf-header.txt"
      ${riscvReadelf} -A "$out/obj/zesu-raw-ssz-allocator.o" \
        > "$out/meta/allocator-elf-attributes.txt"
      ${riscvNm} -u "$out/obj/zesu-raw-ssz-allocator.o" \
        > "$out/meta/allocator-undefined-symbols.txt"
      ${riscvReadelf} -h "$out/obj/zesu-raw-ssz-decoder.o" \
        > "$out/meta/decoder-elf-header.txt"
      ${riscvReadelf} -A "$out/obj/zesu-raw-ssz-decoder.o" \
        > "$out/meta/decoder-elf-attributes.txt"
      ${riscvNm} -u "$out/obj/zesu-raw-ssz-decoder.o" \
        > "$out/meta/decoder-undefined-symbols.txt"
      ${riscvReadelf} -h "$out/obj/zesu-raw-ssz-sink.o" \
        > "$out/meta/sink-elf-header.txt"
      ${riscvReadelf} -A "$out/obj/zesu-raw-ssz-sink.o" \
        > "$out/meta/sink-elf-attributes.txt"
      ${riscvNm} -u "$out/obj/zesu-raw-ssz-sink.o" \
        > "$out/meta/sink-undefined-symbols.txt"
      ${riscvNm} -g "$out/obj/zesu-raw-ssz-decoder.o" | grep -F zesu_decode_raw
      ${riscvNm} -g "$out/obj/zesu-raw-ssz-decoder.o" | grep -F zesu_raw_result
      ${riscvNm} -g "$out/obj/zesu-raw-ssz-allocator.o" | grep -F zesu_raw_alloc
      grep -E '[[:space:]]U[[:space:]]+zesu_raw_alloc$' \
        "$out/meta/decoder-undefined-symbols.txt"
      grep -E '[[:space:]]U[[:space:]]+zesu_raw_result$' \
        "$out/meta/sink-undefined-symbols.txt"
      ! ${riscvReadelf} -S "$out/obj/zesu-raw-ssz-allocator.o" | grep -Ei '\\.lto|llvm\\.lto'
      ! ${riscvReadelf} -S "$out/obj/zesu-raw-ssz-decoder.o" | grep -Ei '\\.lto|llvm\\.lto'
      ! ${riscvReadelf} -S "$out/obj/zesu-raw-ssz-sink.o" | grep -Ei '\\.lto|llvm\\.lto'
      printf '%s\n' "zesu=codygunton/zesu@${zesuRepairedRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  # Evaluate the exact pinned Zig compiler's RV64 layout query. `@compileLog` deliberately fails
  # compilation after reporting the values, so this derivation turns that compiler output into the
  # Lean data module consumed by the proof while preserving the raw compiler transcript as evidence.
  zesuAbiManifest = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-raw-ssz-rv64-abi-manifest";
    version = "96f1621";
    src = zesuRepaired;
    nativeBuildInputs = [ pkgs.gawk pkgs.zig ];
    dontConfigure = true;
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      set +e
      zig build-obj -target riscv64-linux-musl --dep ssz_raw \
        -Mroot=${repo}/targets/ssz/zesu/abi_manifest.zig \
        -Mssz_raw=$PWD/src/stateless/stateless/ssz_raw.zig > abi.log 2>&1
      status=$?
      set -e
      test "$status" != 0
      grep -F 'Compile Log Output:' abi.log
      grep -F '@as(*const' abi.log
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p "$out"
      cp abi.log "$out/abi-manifest.log"
      {
        printf '%s\n' 'namespace ZesuSszAbi'
        printf '%s\n' '/-- Generated from the pinned Zig compiler targeting riscv64-linux-musl. -/'
        printf '%s\n' 'def manifest : Array (String × Nat) := #['
        ${pkgs.gawk}/bin/awk '
          /@as\(\*const/ {
            if (match($0, /"[^"]+"/)) {
              key = substr($0, RSTART + 1, RLENGTH - 2)
              if (match($0, /comptime_int, [0-9]+/)) {
                value = substr($0, RSTART + 14, RLENGTH - 14)
                printf "  (\"%s\", %s),\n", key, value
              }
            }
          }
        ' abi.log
        printf '%s\n' ']'
        printf '%s\n' 'end ZesuSszAbi'
      } > "$out/ZesuSszAbi.lean"
      runHook postInstall
    '';
  };

  # Host-only full-value formatter used by the strict three-way SSZ gate.
  # It imports only the lossless raw decoder and is never linked into the
  # RV64 parser/sink measurement composition.
  zesuValue = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-value";
    version = "96f1621";
    src = zesuRepaired;
    nativeBuildInputs = [ pkgs.zig ];
    dontConfigure = true;
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      zig build zesu-ssz-value -Doptimize=ReleaseSafe
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p "$out/bin" "$out/meta"
      cp zig-out/bin/zesu-ssz-value "$out/bin/zesu-ssz-value"
      printf '%s\n' "zesu=codygunton/zesu@${zesuRepairedRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  zesuSsz = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-rv64im-zicclsm";
    version = "96f1621";
    src = source;
    nativeBuildInputs = [
      pkgs.qemu-user
      riscvPkgs.stdenv.cc
      riscvBinutils
    ];
    hardeningDisable = [ "all" ];
    dontConfigure = true;
    dontBuild = true;
    dontFixup = true;

    installPhase = ''
      runHook preInstall
      mkdir -p "$out/bin" "$out/obj" "$out/meta"
      export NIX_HARDENING_ENABLE=""

      cp ${zesuRawObject}/obj/zesu-raw-ssz-allocator.o \
        "$out/obj/zesu-raw-ssz-allocator.o"
      cp ${zesuRawObject}/obj/zesu-raw-ssz-decoder.o \
        "$out/obj/zesu-raw-ssz-decoder.o"
      cp ${zesuRawObject}/obj/zesu-raw-ssz-sink.o \
        "$out/obj/zesu-raw-ssz-sink.o"
      ${riscvCc} ${cflags} -c ${repo}/targets/ssz/zesu/adapter/main.c \
        -o "$out/obj/zesu-ssz-main.o"
      ${riscvCc} ${cflags} -c ${repo}/targets/common/riscv64_runtime.c \
        -o "$out/obj/riscv64_runtime.o"
      ${riscvCc} ${cflags} -c ${repo}/targets/common/riscv64_start.S \
        -o "$out/obj/riscv64_start.o"
      ${riscvCc} ${cflags} -nostdlib -static -no-pie \
        "$out/obj/riscv64_start.o" \
        "$out/obj/zesu-ssz-main.o" \
        "$out/obj/zesu-raw-ssz-allocator.o" \
        "$out/obj/zesu-raw-ssz-decoder.o" \
        "$out/obj/zesu-raw-ssz-sink.o" \
        "$out/obj/riscv64_runtime.o" \
        -lgcc \
        -Wl,--gc-sections \
        -Wl,-e,_start \
        -Wl,-Map,"$out/meta/zesu-ssz.map" \
        -o "$out/bin/zesu-ssz"

      printf '%s\n' zesu_decode_raw main > "$out/meta/selected-symbols"
      ${riscvReadelf} -h "$out/bin/zesu-ssz" > "$out/meta/elf-header.txt"
      ${riscvReadelf} -A "$out/bin/zesu-ssz" > "$out/meta/elf-attributes.txt"
      ${riscvNm} -S --size-sort --radix=d "$out/bin/zesu-ssz" > "$out/meta/symbols.txt"
      ${riscvNm} -u "$out/obj/zesu-ssz-main.o" > "$out/meta/main-undefined-symbols.txt"
      ${riscvNm} -u "$out/obj/zesu-raw-ssz-decoder.o" \
        > "$out/meta/decoder-undefined-symbols.txt"
      ${riscvNm} -u "$out/obj/zesu-raw-ssz-sink.o" \
        > "$out/meta/sink-undefined-symbols.txt"
      grep -E '[[:space:]]U[[:space:]]+zesu_decode_raw$' \
        "$out/meta/main-undefined-symbols.txt"
      grep -E '[[:space:]]U[[:space:]]+zesu_raw_sink_checksum$' \
        "$out/meta/main-undefined-symbols.txt"
      grep -E '[[:space:]]U[[:space:]]+zesu_raw_alloc$' \
        "$out/meta/decoder-undefined-symbols.txt"
      grep -E '[[:space:]]U[[:space:]]+zesu_raw_result$' \
        "$out/meta/sink-undefined-symbols.txt"
      ! ${riscvReadelf} -S "$out/obj/zesu-raw-ssz-allocator.o" | grep -Ei '\\.lto|llvm\\.lto'
      ! ${riscvReadelf} -S "$out/obj/zesu-raw-ssz-decoder.o" | grep -Ei '\\.lto|llvm\\.lto'
      ! ${riscvReadelf} -S "$out/obj/zesu-raw-ssz-sink.o" | grep -Ei '\\.lto|llvm\\.lto'
      set +e
      result="$(${qemuRiscv64} "$out/bin/zesu-ssz" < /dev/null)"
      status=$?
      set -e
      test "$status" = 1
      test "$result" = invalid

      runHook postInstall
    '';
  };

  # The raw decoder's checksum sink is deliberately separate from the
  # parser object. Exercise the linked RV64 composition to ensure each
  # semantic field still reaches that sink and cannot be DCE'd away.
  zesuSinkObservability = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-sink-observability";
    version = "0.1.0";
    nativeBuildInputs = [ pkgs.python3 pkgs.qemu-user ];
    dontUnpack = true;
    dontConfigure = true;
    dontBuild = true;
    dontFixup = true;
    doCheck = true;

    checkPhase = ''
      runHook preCheck
      ${pkgs.python3}/bin/python -B \
        ${repo}/targets/ssz/zesu/tests/ssz_sink_observability.py \
        --qemu ${qemuRiscv64} \
        --binary ${zesuSsz}/bin/zesu-ssz
      runHook postCheck
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p "$out"
      printf '%s\n' passed > "$out/passed"
      runHook postInstall
    '';
  };

  # Zesu's host suite assumes a manually populated /usr/local. Preserve decoder behavior
  # while providing its crypto dependencies from pinned Nix derivations.
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

  zesuNativeCrypto = pkgs.symlinkJoin {
    name = "zesu-native-crypto";
    paths = [ pkgs.blst mcl pkgs.secp256k1 pkgs.openssl.dev pkgs.openssl.out ];
  };

  zesuFixtures = pkgs.fetchurl {
    url = "https://github.com/ethereum/execution-specs/releases/download/tests-zkevm%40v0.5.0/fixtures_zkevm.tar.gz";
    hash = "sha256-a1/W3qd8xepR39w1sDvcpBh1km4XrSbz6+v5hBA4o2Y=";
  };

  zesuNativeSuite = pkgs.stdenv.mkDerivation {
    pname = "zesu-native-suite";
    version = "aa6c943-96f1621";
    src = zesu;
    nativeBuildInputs = [
      pkgs.gnumake
      pkgs.gnutar
      pkgs.gzip
      pkgs.gmp
      pkgs.pkg-config
      pkgs.secp256k1
      pkgs.openssl
      pkgs.stdenv.cc
      pkgs.zig
    ];
    buildPhase = ":";
    doCheck = true;
    checkPhase = ''
      export LD_LIBRARY_PATH="${zesuNativeCrypto}/lib"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global"

      prepare_suite_source() {
        substituteInPlace build.zig \
          --replace-fail 'step.root_module.addLibraryPath(.{ .cwd_relative = "/usr/local/lib" });' \
          'step.root_module.addLibraryPath(.{ .cwd_relative = std.fs.path.dirname(mcl).? });'
        # The pinned zkeVM release contains a 264.3 MiB JSON fixture. This changes only the
        # test runner's input limit, not production decoder behavior.
        substituteInPlace tools/zkevm_test/main.zig \
          --replace-fail '.limited(256 * 1024 * 1024)' \
          '.limited(512 * 1024 * 1024)'
      }

      install_fixtures() {
        mkdir -p spec-tests/fixtures/zkevm
        tar xzf ${zesuFixtures} --strip-components=1 -C spec-tests/fixtures/zkevm
      }

      run_suite() {
        label="$1"
        export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-$label"
        zig build test -Dcrypto-prefix="${zesuNativeCrypto}"
        zig build zkevm-tests -Dcrypto-prefix="${zesuNativeCrypto}"
      }

      prepare_suite_source
      install_fixtures
      run_suite production

      repaired_source="$TMPDIR/repaired-source"
      cp -a ${zesuRepaired} "$repaired_source"
      chmod -R u+w "$repaired_source"
      cd "$repaired_source"
      prepare_suite_source
      install_fixtures
      run_suite repaired
    '';
    installPhase = ''
      mkdir -p "$out"
      printf '%s\n' production repaired > "$out/passed"
      printf '%s\n' "production=Consensys/zesu@${zesuProductionRevision}" > "$out/provenance.txt"
      printf '%s\n' "repaired=codygunton/zesu@${zesuRepairedRevision}" >> "$out/provenance.txt"
    '';
  };

  rethKeccakRun = pkgs.writeShellApplication {
    name = "reth-keccak";
    runtimeInputs = [ pkgs.qemu-user ];
    text = ''
      exec qemu-riscv64 ${rethKeccak}/bin/reth-keccak "$@"
    '';
  };

  zesuSszRun = pkgs.writeShellApplication {
    name = "zesu-ssz";
    runtimeInputs = [ pkgs.qemu-user ];
    text = ''
      exec qemu-riscv64 ${zesuSsz}/bin/zesu-ssz "$@"
    '';
  };
in
{
  public = {
    inherit
      rethKeccak
      rethKeccakRun
      zesuNativeSuite
      zesuProductionObject
      zesuRawObject
      zesuAbiManifest
      zesuSinkObservability
      zesuSsz
      zesuSszRun
      zesuValue;

    reth-keccak = rethKeccak;
    zesu-value = zesuValue;
    zesu-ssz = zesuSsz;
    zesu-abi-manifest = zesuAbiManifest;
    zesu-sink-observability = zesuSinkObservability;
    zesu-native-suite = zesuNativeSuite;
  };

  internal = {
    inherit rethKeccakRust;
  };
}
