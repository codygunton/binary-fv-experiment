{
  description = "Reproducible RV64 binary evaluation for baseline and Ethereum candidates";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    tiny-sha3 = {
      url = "github:mjosaarinen/tiny_sha3/dcbb3192047c2a721f5f851db591871d428036a9";
      flake = false;
    };

    miniz = {
      url = "github:richgel999/miniz/77d0dce8627735138c51770d1799a1ef48f2117d";
      flake = false;
    };

    # Candidate and audit sources are pinned independently of PR #2.
    reth = {
      url = "github:paradigmxyz/reth/9384bc53d8c0c77e59cac83fdaaf3b372c6d2216";
      flake = false;
    };

    zesu = {
      url = "github:Consensys/zesu/aa6c94339987d278acb8b7fa409c864dbd3d05aa";
      flake = false;
    };

    scrollFv = {
      url = "github:trailofbits/scroll-fv/0c3927ba4d6773b4cfd1d949cba342268b104d91";
      flake = false;
    };

    etheorem = {
      url = "github:etheorem/etheorem/032ab6c6d67186ba60b734e0f2c44ba1bb8b6fb0";
      flake = false;
    };

    executionSpecs = {
      url = "github:ethereum/execution-specs/bd8c673552d957dbe9c9f3f2656b87201f5ae646";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, tiny-sha3, miniz, reth, zesu, scrollFv, etheorem, executionSpecs }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system:
          let
            pkgs = import nixpkgs { inherit system; };
          in
          f system pkgs);
    in
    {
      packages = forAllSystems (system: pkgs:
        let
          lib = pkgs.lib;
          riscvPkgs = pkgs.pkgsCross.riscv64;
          riscvBinutils = riscvPkgs.buildPackages.binutils;
          riscvTargetPrefix = riscvPkgs.stdenv.cc.targetPrefix;
          riscvCc = "${riscvPkgs.stdenv.cc}/bin/${riscvTargetPrefix}gcc";
          riscvObjdump = "${riscvBinutils}/bin/${riscvTargetPrefix}objdump";
          riscvNm = "${riscvBinutils}/bin/${riscvTargetPrefix}nm";
          riscvReadelf = "${riscvBinutils}/bin/${riscvTargetPrefix}readelf";
          riscvSize = "${riscvBinutils}/bin/${riscvTargetPrefix}size";
          riscvAr = "${riscvBinutils}/bin/${riscvTargetPrefix}ar";
          qemuRiscv64 = "${pkgs.qemu-user}/bin/qemu-riscv64";
          riscvTarget = "RV64IM_Zicclsm";
          riscvArch = "rv64im_zicclsm";
          riscvAbi = "lp64";
          commonCFlags = [
            "-Os"
            "-g0"
            "-DNDEBUG"
            "-march=${riscvArch}"
            "-mabi=${riscvAbi}"
            "-ffreestanding"
            "-fno-builtin"
            "-ffunction-sections"
            "-fdata-sections"
            "-fno-asynchronous-unwind-tables"
            "-fno-unwind-tables"
            "-fno-stack-protector"
            "-fomit-frame-pointer"
            "-fno-pic"
            "-fno-pie"
          ];
          cflags = lib.concatStringsSep " " commonCFlags;
          sha3SampleMessage = "sha3-sample-message";
          sha3SampleDigest = "f8b2abe65645474af551ae4523f3c5948d9897c9f46c08a390ef88d6777507ba";

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
            src = ./reth-keccak;
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

          mkBinary =
            { name
            , srcRoot
            , sourceFile
            , entrypoint
            , includes ? [ ]
            , extraCFlags ? [ ]
            , selectedSymbols
            }:
            pkgs.stdenvNoCC.mkDerivation {
              pname = "sha-fv-${name}-rv64im-zicclsm";
              version = "0.1.0";
              src = self;

              nativeBuildInputs = [
                riscvPkgs.stdenv.cc
                riscvBinutils
              ];

              hardeningDisable = [ "all" ];
              dontConfigure = true;
              dontBuild = true;
              dontFixup = true;

              installPhase =
                let
                  includeFlags = lib.concatMapStringsSep " " (include: "-I${include}") includes;
                  targetCFlags = lib.concatStringsSep " " (commonCFlags ++ extraCFlags);
                in
                ''
                  runHook preInstall

                  mkdir -p "$out/bin" "$out/obj" "$out/meta"
                  export NIX_HARDENING_ENABLE=""

                  ${riscvCc} ${targetCFlags} ${includeFlags} \
                    -I${srcRoot} \
                    -c ${srcRoot}/${sourceFile} \
                    -o "$out/obj/${name}.o"

                  ${riscvCc} ${targetCFlags} ${includeFlags} \
                    -I${srcRoot} \
                    -c ${entrypoint} \
                    -o "$out/obj/${name}-main.o"

                  ${riscvCc} ${cflags} \
                    -c ${./harness/riscv64_runtime.c} \
                    -o "$out/obj/riscv64_runtime.o"

                  ${riscvCc} ${cflags} \
                    -c ${./harness/riscv64_start.S} \
                    -o "$out/obj/riscv64_start.o"

                  ${riscvCc} ${cflags} -nostdlib -static -no-pie \
                    "$out/obj/riscv64_start.o" \
                    "$out/obj/${name}-main.o" \
                    "$out/obj/${name}.o" \
                    "$out/obj/riscv64_runtime.o" \
                    -lgcc \
                    -Wl,--gc-sections \
                    -Wl,-e,_start \
                    -o "$out/bin/${name}"

                  printf '%s\n' ${lib.escapeShellArgs selectedSymbols} > "$out/meta/selected-symbols"
                  ${riscvReadelf} -h "$out/bin/${name}" > "$out/meta/elf-header.txt"
                  ${riscvReadelf} -A "$out/bin/${name}" > "$out/meta/elf-attributes.txt"

                  runHook postInstall
                '';
            };

          sha3 = mkBinary {
            name = "sha3";
            srcRoot = tiny-sha3;
            sourceFile = "sha3.c";
            entrypoint = ./harness/sha3.c;
            selectedSymbols = [
              "sha3_keccakf"
              "sha3_init"
              "sha3_update"
              "sha3_final"
              "sha3"
              "main"
            ];
          };

          tinfl = mkBinary {
            name = "tinfl";
            srcRoot = miniz;
            sourceFile = "miniz_tinfl.c";
            entrypoint = ./harness/tinfl.c;
            includes = [ ./include ];
            extraCFlags = [
              "-DMINIZ_NO_TIME"
              "-DMINIZ_NO_STDIO"
              "-DMINIZ_NO_MALLOC"
              "-DMINIZ_NO_ARCHIVE_APIS"
              "-DMINIZ_NO_DEFLATE_APIS"
              "-DMINIZ_NO_ZLIB_COMPATIBLE_NAMES"
            ];
            selectedSymbols = [
              "tinfl_decompress"
              "tinfl_decompress_mem_to_mem"
              "main"
            ];
          };

          rethKeccak = pkgs.stdenvNoCC.mkDerivation {
            pname = "reth-keccak-rv64im-zicclsm";
            version = "2.3.0";
            src = self;

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

              ${riscvCc} ${cflags} -c ${./harness/reth_keccak.c} \
                -o "$out/obj/reth-keccak-main.o"
              ${riscvCc} ${cflags} -c ${./harness/riscv64_runtime.c} \
                -o "$out/obj/riscv64_runtime.o"
              ${riscvCc} ${cflags} -c ${./harness/riscv64_start.S} \
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
              ${pkgs.python3}/bin/python ${./tools/check_reth_keccak.py} \
                --qemu ${qemuRiscv64} \
                --binary "$out/bin/reth-keccak" \
                --vectors ${./tests/reth-keccak-vectors.json}

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
              printf '%s\n' "zesu=aa6c94339987d278acb8b7fa409c864dbd3d05aa" > "$out/meta/provenance.txt"
              printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
              runHook postInstall
            '';
          };

          zesuRawObject = pkgs.stdenvNoCC.mkDerivation {
            pname = "zesu-raw-ssz-rv64im-object";
            version = "aa6c943";
            src = zesu;
            patches = [ ./patches/zesu-decode-raw.patch ];
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
              printf '%s\n' "zesu=aa6c94339987d278acb8b7fa409c864dbd3d05aa" > "$out/meta/provenance.txt"
              printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
              runHook postInstall
            '';
          };

          # Host-only full-value formatter used by the strict three-way SSZ gate.
          # It imports only the lossless raw decoder and is never linked into the
          # RV64 parser/sink measurement composition.
          zesuValue = pkgs.stdenvNoCC.mkDerivation {
            pname = "zesu-ssz-value";
            version = "aa6c943";
            src = zesu;
            patches = [ ./patches/zesu-decode-raw.patch ];
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
              printf '%s\n' "zesu=aa6c94339987d278acb8b7fa409c864dbd3d05aa" > "$out/meta/provenance.txt"
              printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
              runHook postInstall
            '';
          };

          zesuSsz = pkgs.stdenvNoCC.mkDerivation {
            pname = "zesu-ssz-rv64im-zicclsm";
            version = "aa6c943";
            src = self;
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
              ${riscvCc} ${cflags} -c ${./harness/zesu_ssz.c} \
                -o "$out/obj/zesu-ssz-main.o"
              ${riscvCc} ${cflags} -c ${./harness/riscv64_runtime.c} \
                -o "$out/obj/riscv64_runtime.o"
              ${riscvCc} ${cflags} -c ${./harness/riscv64_start.S} \
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
                ${./tests}/ssz_sink_observability.py \
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
            version = "aa6c943";
            src = zesu;
            nativeBuildInputs = [
              pkgs.gnumake
              pkgs.gnutar
              pkgs.gzip
              pkgs.gmp
              pkgs.patch
              pkgs.pkg-config
              pkgs.secp256k1
              pkgs.openssl
              pkgs.stdenv.cc
              pkgs.zig
            ];
            postPatch = ''
              substituteInPlace build.zig \
                --replace-fail 'step.root_module.addLibraryPath(.{ .cwd_relative = "/usr/local/lib" });' \
                'step.root_module.addLibraryPath(.{ .cwd_relative = std.fs.path.dirname(mcl).? });'
              # The pinned zkeVM release contains a 264.3 MiB JSON fixture. This changes only the
              # test runner's input limit, not production decoder behavior.
              substituteInPlace tools/zkevm_test/main.zig \
                --replace-fail '.limited(256 * 1024 * 1024)' \
                '.limited(512 * 1024 * 1024)'
            '';
            buildPhase = ":";
            doCheck = true;
            checkPhase = ''
              export LD_LIBRARY_PATH="${zesuNativeCrypto}/lib"
              export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global"

              mkdir -p spec-tests/fixtures/zkevm
              tar xzf ${zesuFixtures} --strip-components=1 -C spec-tests/fixtures/zkevm

              run_suite() {
                label="$1"
                export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-$label"
                zig build test -Dcrypto-prefix="${zesuNativeCrypto}"
                zig build zkevm-tests -Dcrypto-prefix="${zesuNativeCrypto}"
              }

              run_suite production

              production_source="$PWD"
              patched_source="$TMPDIR/patched-source"
              cp -a "$production_source" "$patched_source"
              cd "$patched_source"
              patch --batch --fuzz=0 -p1 -i ${./patches/zesu-decode-raw.patch}
              grep -F 'pub fn decodeRaw(' src/stateless/stateless/ssz.zig
              grep -F 'pub fn decode(' src/stateless/stateless/ssz.zig
              run_suite extracted-raw
            '';
            installPhase = ''
              mkdir -p "$out"
              printf '%s\n' production extracted-raw > "$out/passed"
            '';
          };

          stats = pkgs.stdenvNoCC.mkDerivation {
            pname = "sha-fv-binary-stats-rv64im-zicclsm";
            version = "0.1.0";

            nativeBuildInputs = [
              pkgs.coreutils
              pkgs.gawk
              pkgs.gnused
              pkgs.python3
              pkgs.qemu-user
              riscvBinutils
            ];

            dontUnpack = true;
            dontConfigure = true;
            dontBuild = true;
            dontFixup = true;

            installPhase = ''
              runHook preInstall

              mkdir -p \
                "$out/analysis" \
                "$out/bin" \
                "$out/objdump" \
                "$out/rv64/bin" \
                "$out/rv64/meta" \
                "$out/rv64/obj"

              cp ${sha3}/bin/sha3 "$out/rv64/bin/sha3"
              cp ${sha3}/obj/sha3.o "$out/rv64/obj/sha3.o"
              cp ${sha3}/obj/sha3-main.o "$out/rv64/obj/sha3-main.o"
              cp ${sha3}/meta/elf-attributes.txt "$out/rv64/meta/sha3-elf-attributes.txt"
              cp ${sha3}/meta/selected-symbols "$out/rv64/meta/sha3-selected-symbols.txt"

              cp ${tinfl}/bin/tinfl "$out/rv64/bin/tinfl"
              cp ${tinfl}/obj/tinfl.o "$out/rv64/obj/tinfl.o"
              cp ${tinfl}/obj/tinfl-main.o "$out/rv64/obj/tinfl-main.o"
              cp ${tinfl}/meta/elf-attributes.txt "$out/rv64/meta/tinfl-elf-attributes.txt"
              cp ${tinfl}/meta/selected-symbols "$out/rv64/meta/tinfl-selected-symbols.txt"

              cp ${rethKeccak}/bin/reth-keccak "$out/rv64/bin/reth-keccak"
              cp ${rethKeccakRust}/lib/libreth_keccak_wrapper.a \
                "$out/rv64/obj/reth-keccak-rustcrypto.a"
              cp ${rethKeccak}/obj/reth-keccak-main.o "$out/rv64/obj/reth-keccak-main.o"
              cp ${rethKeccak}/meta/elf-attributes.txt \
                "$out/rv64/meta/reth-keccak-elf-attributes.txt"
              cp ${rethKeccak}/meta/selected-symbols \
                "$out/rv64/meta/reth-keccak-selected-symbols.txt"
              cp ${rethKeccak}/meta/reth-keccak.map "$out/rv64/meta/reth-keccak.map"
              cp ${rethKeccak}/meta/symbols.txt "$out/rv64/meta/reth-keccak-symbols.txt"
              cp ${rethKeccak}/meta/provenance.txt "$out/rv64/meta/reth-keccak-provenance.txt"

              cp ${zesuSsz}/bin/zesu-ssz "$out/rv64/bin/zesu-ssz"
              cp ${zesuSsz}/obj/zesu-raw-ssz-allocator.o \
                "$out/rv64/obj/zesu-raw-ssz-allocator.o"
              cp ${zesuSsz}/obj/zesu-raw-ssz-decoder.o \
                "$out/rv64/obj/zesu-raw-ssz-decoder.o"
              cp ${zesuSsz}/obj/zesu-raw-ssz-sink.o \
                "$out/rv64/obj/zesu-raw-ssz-sink.o"
              cp ${zesuSsz}/obj/zesu-ssz-main.o "$out/rv64/obj/zesu-ssz-main.o"
              cp ${zesuSsz}/meta/elf-attributes.txt \
                "$out/rv64/meta/zesu-ssz-elf-attributes.txt"
              cp ${zesuSsz}/meta/selected-symbols \
                "$out/rv64/meta/zesu-ssz-selected-symbols.txt"
              cp ${zesuSsz}/meta/zesu-ssz.map "$out/rv64/meta/zesu-ssz.map"
              cp ${zesuSsz}/meta/symbols.txt "$out/rv64/meta/zesu-ssz-symbols.txt"
              cp ${zesuRawObject}/meta/provenance.txt \
                "$out/rv64/meta/zesu-raw-ssz-provenance.txt"
              for raw_object in allocator decoder sink; do
                cp "${zesuRawObject}/meta/$raw_object-elf-header.txt" \
                  "$out/rv64/meta/zesu-raw-ssz-$raw_object-elf-header.txt"
                cp "${zesuRawObject}/meta/$raw_object-elf-attributes.txt" \
                  "$out/rv64/meta/zesu-raw-ssz-$raw_object-elf-attributes.txt"
                cp "${zesuRawObject}/meta/$raw_object-undefined-symbols.txt" \
                  "$out/rv64/meta/zesu-raw-ssz-$raw_object-undefined-symbols.txt"
              done
              printf '%s\n' sha3 > "$out/rv64/meta/sha3-protocol-selected-symbols.txt"
              printf '%s\n' tinfl_decompress_mem_to_mem \
                > "$out/rv64/meta/tinfl-protocol-selected-symbols.txt"
              printf '%s\n' reth_keccak256 \
                > "$out/rv64/meta/reth-keccak-protocol-selected-symbols.txt"
              printf '%s\n' zesu_decode_raw > "$out/rv64/meta/zesu-ssz-parser-selected-symbols.txt"

              count_symbol_instructions() {
                local file="$1"
                local symbol="$2"
                ${riscvObjdump} -d --disassemble="$symbol" "$file" |
                  awk '/^[[:space:]]+[0-9a-f]+:/ { n++ } END { print n + 0 }'
              }

              selected_instruction_total() {
                local file="$1"
                local symbols_file="$2"
                local total=0
                local count
                local symbol
                while IFS= read -r symbol; do
                  count="$(count_symbol_instructions "$file" "$symbol")"
                  total=$((total + count))
                done < "$symbols_file"
                printf '%s\n' "$total"
              }

              branchish_total() {
                local file="$1"
                local symbols_file="$2"
                local tmp
                tmp="$(mktemp)"
                local symbol
                while IFS= read -r symbol; do
                  ${riscvObjdump} -d --disassemble="$symbol" "$file" >> "$tmp"
                done < "$symbols_file"
                awk '
                  /^[[:space:]]+[0-9a-f]+:/ {
                    nfields = split($0, tabbed, "\t")
                    instr = tabbed[nfields]
                    sub(/^[[:space:]]+/, "", instr)
                    split(instr, a, /[[:space:]]+/)
                    m = a[1]
                    if (m ~ /^b/) branch++
                    else if (m == "j" || m == "jr" || m == "jal" || m == "jalr") branch++
                    else if (m == "call" || m == "tail") call++
                    else if (m == "ret") ret++
                  }
                  END { print branch + call + ret + 0 }
                ' "$tmp"
                rm -f "$tmp"
              }

              text_size() {
                ${riscvSize} "$1" | awk 'NR == 2 { print $1 }'
              }

              archive_text_size() {
                local archive="$1"
                local unpack
                unpack="$(mktemp -d)"
                (
                  cd "$unpack"
                  ${riscvAr} x "$archive"
                  for member in *; do
                    test -f "$member" || continue
                    ${riscvSize} "$member" | awk 'NR == 2 { print $1 }'
                  done
                ) | awk '{ total += $1 } END { print total + 0 }'
                rm -rf "$unpack"
              }

              object_text_size() {
                case "$1" in
                  *.a) archive_text_size "$1" ;;
                  *) text_size "$1" ;;
                esac
              }

              file_size() {
                stat -c '%s' "$1"
              }

              objdump_line_count() {
                ${riscvObjdump} -d "$1" | wc -l | awk '{ print $1 }'
              }

              objdump_instruction_line_count() {
                ${riscvObjdump} -d "$1" |
                  awk '/^[[:space:]]+[0-9a-f]+:/ { n++ } END { print n + 0 }'
              }

              {
                printf 'role\tartifact\ttext_bytes\tfile_bytes\n'
                for raw_object in allocator decoder sink; do
                  object="$out/rv64/obj/zesu-raw-ssz-$raw_object.o"
                  printf '%s\t%s\t%s\t%s\n' \
                    "$raw_object" "$(basename "$object")" \
                    "$(text_size "$object")" "$(file_size "$object")"
                done
              } > "$out/rv64/meta/zesu-ssz-raw-objects.tsv"

              analyze_target() {
                local target="$1"
                local binary="$2"
                local entry="$3"
                shift 3
                ${pkgs.python3}/bin/python ${./tools/analyze_rv64.py} "$binary" \
                  --objdump ${riscvObjdump} \
                  --entry "$entry" \
                  --target "$target ${riscvTarget}" \
                  --json "$out/analysis/$target.json" \
                  --markdown "$out/analysis/$target.md" \
                  "$@"
              }

              json_value() {
                ${pkgs.python3}/bin/python -c 'import json, sys; value = json.load(open(sys.argv[1]))[sys.argv[2]]; print("" if value is None else value)' "$1" "$2"
              }

              json_compact() {
                ${pkgs.python3}/bin/python -c 'import json, sys; print(json.dumps(json.load(open(sys.argv[1]))[sys.argv[2]], sort_keys=True, separators=(",", ":")))' "$1" "$2"
              }

              json_length() {
                ${pkgs.python3}/bin/python -c 'import json, sys; print(len(json.load(open(sys.argv[1]))[sys.argv[2]]))' "$1" "$2"
              }

              json_owner_instructions() {
                ${pkgs.python3}/bin/python -c 'import json, sys; report = json.load(open(sys.argv[1])); print(report["ownership"].get(sys.argv[2], {}).get("instructions", 0))' "$1" "$2"
              }

              json_owner_function_count() {
                ${pkgs.python3}/bin/python -c 'import json, sys; report = json.load(open(sys.argv[1])); print(report["ownership"].get(sys.argv[2], {}).get("function_count", 0))' "$1" "$2"
              }

              json_call_depth() {
                ${pkgs.python3}/bin/python -c 'import json, sys; report = json.load(open(sys.argv[1])); print("recursive" if report["recursive_direct_calls"] else report["maximum_direct_call_depth"])' "$1"
              }

              append_target() {
                local target="$1"
                local source="$2"
                local object_label="$3"
                local object="$4"
                local binary="$5"
                local selected_symbols="$6"
                local entry_symbol="$7"
                local analysis_scope="$8"
                local analysis="$out/analysis/$target.json"
                local object_text
                local linked_text
                local selected_instrs
                local branchish
                local full_instrs
                local reachable_instrs
                local protocol_owned_instrs
                local protocol_owned_functions
                local reachable_functions
                local basic_blocks
                local cfg_edges
                local conditional_branches
                local direct_calls
                local loop_sccs
                local maximum_call_depth
                local opcode_classes
                local forbidden_count
                local objdump_lines
                local objdump_instr_lines

                object_text="$(object_text_size "$object")"
                linked_text="$(text_size "$binary")"
                selected_instrs="$(selected_instruction_total "$binary" "$selected_symbols")"
                branchish="$(branchish_total "$binary" "$selected_symbols")"
                full_instrs="$(json_value "$analysis" full_instruction_count)"
                reachable_instrs="$(json_value "$analysis" reachable_instruction_count)"
                protocol_owned_instrs="$(json_owner_instructions "$analysis" protocol)"
                protocol_owned_functions="$(json_owner_function_count "$analysis" protocol)"
                reachable_functions="$(json_value "$analysis" reachable_function_count)"
                basic_blocks="$(json_value "$analysis" basic_blocks)"
                cfg_edges="$(json_value "$analysis" cfg_edges)"
                conditional_branches="$(json_value "$analysis" conditional_branches)"
                direct_calls="$(json_value "$analysis" direct_calls)"
                loop_sccs="$(json_value "$analysis" loop_sccs)"
                maximum_call_depth="$(json_call_depth "$analysis")"
                opcode_classes="$(json_compact "$analysis" opcode_classes)"
                forbidden_count="$(json_length "$analysis" forbidden_reachable_instructions)"
                objdump_lines="$(objdump_line_count "$binary")"
                objdump_instr_lines="$(objdump_instruction_line_count "$binary")"

                printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
                  "$target" "$analysis_scope" "$entry_symbol" "$source" "${riscvTarget}" \
                  "$object_label" "$object_text" "$linked_text" "$selected_instrs" "$branchish" \
                  "$full_instrs" "$reachable_instrs" "$protocol_owned_instrs" "$protocol_owned_functions" \
                  "$reachable_functions" \
                  "$basic_blocks" "$cfg_edges" "$conditional_branches" "$direct_calls" "$loop_sccs" \
                  "$maximum_call_depth" "$opcode_classes" "$forbidden_count" "$objdump_lines" \
                  "$objdump_instr_lines" "$(file_size "$object")" "$(file_size "$binary")" \
                  "analysis/$target.json" >> "$out/stats.tsv"

                printf '| `%s` | `%s` | `%s` | %s | %s B | %s B | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n' \
                  "$target" "$analysis_scope" "$entry_symbol" "$object_label" "$object_text" "$linked_text" \
                  "$full_instrs" "$reachable_instrs" "$protocol_owned_instrs" "$reachable_functions" \
                  "$protocol_owned_functions" \
                  "$basic_blocks" "$cfg_edges" "$conditional_branches" "$direct_calls" "$loop_sccs" \
                  >> "$out/stats.md"
              }

              ${riscvObjdump} -d "$out/rv64/bin/sha3" > "$out/objdump/sha3.txt"
              ${riscvObjdump} -d "$out/rv64/bin/tinfl" > "$out/objdump/tinfl.txt"
              ${riscvObjdump} -d "$out/rv64/bin/reth-keccak" > "$out/objdump/reth-keccak.txt"
              ${riscvObjdump} -d "$out/rv64/bin/zesu-ssz" > "$out/objdump/zesu-ssz.txt"
              ${riscvObjdump} -d --disassemble=sha3 "$out/rv64/bin/sha3" \
                > "$out/objdump/sha3-protocol.txt"
              ${riscvObjdump} -d --disassemble=tinfl_decompress_mem_to_mem "$out/rv64/bin/tinfl" \
                > "$out/objdump/tinfl-protocol.txt"
              ${riscvObjdump} -d --disassemble=reth_keccak256 "$out/rv64/bin/reth-keccak" \
                > "$out/objdump/reth-keccak-protocol.txt"
              ${riscvObjdump} -d --disassemble=zesu_decode_raw "$out/rv64/bin/zesu-ssz" \
                > "$out/objdump/zesu-ssz-parser.txt"

              # Retain each freestanding harness composition for context. The
              # protocol-entry analyses below are the uniformly rooted metrics
              # used for target-selection comparisons.
              analyze_target sha3 "$out/rv64/bin/sha3" _start \
                --owner 'sha3*=protocol' \
                --owner '*keccak*=protocol' \
                --owner 'main=harness' \
                --owner '_start=runtime' \
                --owner '*mem*=runtime' \
                --owner '*=runtime'
              analyze_target tinfl "$out/rv64/bin/tinfl" _start \
                --owner 'tinfl*=protocol' \
                --owner 'main=harness' \
                --owner '_start=runtime' \
                --owner '*mem*=runtime' \
                --owner '*=runtime'
              analyze_target reth-keccak "$out/rv64/bin/reth-keccak" _start \
                --owner 'reth_keccak256=protocol' \
                --owner '*Keccak*=protocol' \
                --owner '*keccak*=protocol' \
                --owner '*sha3*=protocol' \
                --owner 'main=harness' \
                --owner '_start=runtime' \
                --owner '*mem*=runtime' \
                --owner '_R*=rust-runtime' \
                --owner '*=rust-runtime'
              # Keep the complete harness/allocator/decoder/sink composition as
              # a distinct `_start`-rooted analysis. The protocol-entry comparison
              # below is decision-facing and does not replace this artifact.
              analyze_target zesu-ssz "$out/rv64/bin/zesu-ssz" _start \
                --owner 'zesu_raw_sink_checksum=adapter' \
                --owner 'zesu_raw_result=adapter' \
                --owner 'zesu_raw_error=adapter' \
                --owner 'zesu_raw_alloc=allocator' \
                --owner 'zesu_decode_raw=protocol' \
                --owner '*ssz*=protocol' \
                --owner '*Ssz*=protocol' \
                --owner '*decode*=protocol' \
                --owner '*Decode*=protocol' \
                --owner '*rlp*=rlp' \
                --owner '*Rlp*=rlp' \
                --owner 'main=harness' \
                --owner '_start=runtime' \
                --owner '*mem*=runtime' \
                --owner '*alloc*=allocator' \
                --owner '*Alloc*=allocator' \
                --owner '*=zig-runtime'

              # Every decision-facing metric starts at the exported protocol
              # boundary in its linked ELF and shares the corresponding full
              # composition ownership map above.
              analyze_target sha3-protocol "$out/rv64/bin/sha3" sha3 \
                --owner 'sha3*=protocol' \
                --owner '*keccak*=protocol' \
                --owner 'main=harness' \
                --owner '_start=runtime' \
                --owner '*mem*=runtime' \
                --owner '*=runtime'
              analyze_target tinfl-protocol "$out/rv64/bin/tinfl" tinfl_decompress_mem_to_mem \
                --owner 'tinfl*=protocol' \
                --owner 'main=harness' \
                --owner '_start=runtime' \
                --owner '*mem*=runtime' \
                --owner '*=runtime'
              analyze_target reth-keccak-protocol "$out/rv64/bin/reth-keccak" reth_keccak256 \
                --owner 'reth_keccak256=protocol' \
                --owner '*Keccak*=protocol' \
                --owner '*keccak*=protocol' \
                --owner '*sha3*=protocol' \
                --owner 'main=harness' \
                --owner '_start=runtime' \
                --owner '*mem*=runtime' \
                --owner '_R*=rust-runtime' \
                --owner '*=rust-runtime'

              # Zesu's protocol entry publishes its raw result for a separate
              # anti-DCE sink. Allocator vtable calls remain explicit unresolved
              # indirect calls, never protocol instructions.
              analyze_target zesu-ssz-parser "$out/rv64/bin/zesu-ssz" zesu_decode_raw \
                --owner 'zesu_raw_sink_checksum=adapter' \
                --owner 'zesu_raw_result=adapter' \
                --owner 'zesu_raw_error=adapter' \
                --owner 'zesu_raw_alloc=allocator' \
                --owner 'zesu_decode_raw=protocol' \
                --owner '*ssz*=protocol' \
                --owner '*Ssz*=protocol' \
                --owner '*decode*=protocol' \
                --owner '*Decode*=protocol' \
                --owner '*mem*=runtime' \
                --owner '*alloc*=allocator' \
                --owner '*Alloc*=allocator' \
                --owner '*=zig-runtime'

              sha3_output="$(${qemuRiscv64} "$out/rv64/bin/sha3" ${lib.escapeShellArg sha3SampleMessage})"
              if [ "$sha3_output" != "${sha3SampleDigest}" ]; then
                echo "unexpected SHA-3 digest for ${sha3SampleMessage}: $sha3_output" >&2
                exit 1
              fi
              ${qemuRiscv64} "$out/rv64/bin/tinfl"

              reth_output="$(${qemuRiscv64} "$out/rv64/bin/reth-keccak" 616263)"
              test "$reth_output" = 4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

              set +e
              zesu_output="$(${qemuRiscv64} "$out/rv64/bin/zesu-ssz" < /dev/null)"
              zesu_status=$?
              set -e
              test "$zesu_status" = 1
              test "$zesu_output" = invalid

              ${riscvSize} \
                "$out/rv64/obj/sha3.o" \
                "$out/rv64/obj/tinfl.o" \
                "$out/rv64/obj/reth-keccak-rustcrypto.a" \
                "$out/rv64/obj/zesu-raw-ssz-allocator.o" \
                "$out/rv64/obj/zesu-raw-ssz-decoder.o" \
                "$out/rv64/obj/zesu-raw-ssz-sink.o" \
                "$out/rv64/bin/sha3" \
                "$out/rv64/bin/tinfl" \
                "$out/rv64/bin/reth-keccak" \
                "$out/rv64/bin/zesu-ssz" > "$out/size.txt"

              ${riscvNm} -S --size-sort --radix=d \
                "$out/rv64/obj/sha3.o" \
                "$out/rv64/obj/tinfl.o" \
                "$out/rv64/obj/reth-keccak-rustcrypto.a" \
                "$out/rv64/obj/zesu-raw-ssz-allocator.o" \
                "$out/rv64/obj/zesu-raw-ssz-decoder.o" \
                "$out/rv64/obj/zesu-raw-ssz-sink.o" \
                "$out/rv64/bin/sha3" \
                "$out/rv64/bin/tinfl" \
                "$out/rv64/bin/reth-keccak" \
                "$out/rv64/bin/zesu-ssz" > "$out/symbols.txt"

              {
                echo "tool,value"
                printf 'target,%s\n' '${riscvTarget}'
                printf 'march,%s\n' '${riscvArch}'
                printf 'mabi,%s\n' '${riscvAbi}'
                printf 'cc,%s\n' "$(${riscvCc} --version | head -n 1)"
                printf 'size,%s\n' "$(${riscvSize} --version | head -n 1)"
                printf 'nm,%s\n' "$(${riscvNm} --version | head -n 1)"
                printf 'objdump,%s\n' "$(${riscvObjdump} --version | head -n 1)"
                printf 'qemu,%s\n' "$(${qemuRiscv64} --version | head -n 1)"
              } > "$out/toolchain.csv"

              cat > "$out/stats.tsv" <<EOF
              target	analysis_scope	entry_symbol	source	arch	object_artifact	object_text	linked_text	selected_symbol_instructions	branchish	full_instructions	reachable_instructions	protocol_owned_reachable_instructions	protocol_owned_reachable_functions	reachable_functions	basic_blocks	cfg_edges	conditional_branches	direct_calls	loop_sccs	maximum_direct_call_depth	opcode_classes	forbidden_reachable_instructions	linked_objdump_lines	linked_objdump_instruction_lines	file_size_object	file_size_linked	analysis_json
              EOF

              cat > "$out/stats.md" <<EOF
              # RV64 Target Evaluation Stats

              ## Inputs

              - SHA-3: \`mjosaarinen/tiny_sha3\` at \`dcbb3192047c2a721f5f851db591871d428036a9\`
              - DEFLATE: \`richgel999/miniz\` at \`77d0dce8627735138c51770d1799a1ef48f2117d\`
              - Reth provenance: \`paradigmxyz/reth\` at \`9384bc53d8c0c77e59cac83fdaaf3b372c6d2216\`
              - Zesu: \`Consensys/zesu\` at \`aa6c94339987d278acb8b7fa409c864dbd3d05aa\`

              ## Toolchain

              \`\`\`text
              target ${riscvTarget}
              march ${riscvArch}
              mabi ${riscvAbi}
              $(${riscvCc} --version | head -n 1)
              $(${riscvSize} --version | head -n 1)
              $(${qemuRiscv64} --version | head -n 1)
              \`\`\`

              ## ${riscvTarget}

              ## Decision-facing protocol-entry comparison

              All selection rows use the exported protocol root in the linked ELF: \`sha3\`,
              \`tinfl_decompress_mem_to_mem\`, \`reth_keccak256\`, or \`zesu_decode_raw\`.
              In \`stats.tsv\`, filter \`analysis_scope=protocol-entry\` for the uniformly rooted
              inputs to the size and structural gates. The selected-symbol columns are retained
              only for continuity with the original SHA/miniz measurements.

              | Target | Scope | Entry symbol | Measured artifact | Object \`.text\` | Linked \`.text\` | Full instrs | Reachable instrs | Protocol reachable | Reachable funcs | Protocol funcs | Blocks | CFG edges | Conditional branches | Calls | Loop SCCs |
              |---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
              EOF

              append_target sha3-protocol \
                'mjosaarinen/tiny_sha3:sha3.c (protocol entry)' \
                'sha3.o' \
                "$out/rv64/obj/sha3.o" \
                "$out/rv64/bin/sha3" \
                "$out/rv64/meta/sha3-protocol-selected-symbols.txt" \
                sha3 \
                protocol-entry
              append_target tinfl-protocol \
                'richgel999/miniz:miniz_tinfl.c (protocol entry)' \
                'tinfl.o' \
                "$out/rv64/obj/tinfl.o" \
                "$out/rv64/bin/tinfl" \
                "$out/rv64/meta/tinfl-protocol-selected-symbols.txt" \
                tinfl_decompress_mem_to_mem \
                protocol-entry
              append_target reth-keccak-protocol \
                'Reth RustCrypto Keccak-256 wrapper (protocol entry)' \
                'libreth_keccak_wrapper.a' \
                "$out/rv64/obj/reth-keccak-rustcrypto.a" \
                "$out/rv64/bin/reth-keccak" \
                "$out/rv64/meta/reth-keccak-protocol-selected-symbols.txt" \
                reth_keccak256 \
                protocol-entry
              append_target zesu-ssz-parser \
                'Zesu raw parser rooted at zesu_decode_raw' \
                'zesu-raw-ssz-decoder.o' \
                "$out/rv64/obj/zesu-raw-ssz-decoder.o" \
                "$out/rv64/bin/zesu-ssz" \
                "$out/rv64/meta/zesu-ssz-parser-selected-symbols.txt" \
                zesu_decode_raw \
                protocol-entry

              cat >> "$out/stats.md" <<EOF

              ## Full \`_start\` composition context

              These retained context rows include each freestanding harness composition. They do
              not feed the decision gates; use the protocol-entry rows above instead.

              | Target | Scope | Entry symbol | Measured artifact | Object \`.text\` | Linked \`.text\` | Full instrs | Reachable instrs | Protocol reachable | Reachable funcs | Protocol funcs | Blocks | CFG edges | Conditional branches | Calls | Loop SCCs |
              |---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
              EOF

              append_target sha3 \
                'mjosaarinen/tiny_sha3:sha3.c' \
                'sha3.o' \
                "$out/rv64/obj/sha3.o" \
                "$out/rv64/bin/sha3" \
                "$out/rv64/meta/sha3-selected-symbols.txt" \
                _start \
                full-composition
              append_target tinfl \
                'richgel999/miniz:miniz_tinfl.c' \
                'tinfl.o' \
                "$out/rv64/obj/tinfl.o" \
                "$out/rv64/bin/tinfl" \
                "$out/rv64/meta/tinfl-selected-symbols.txt" \
                _start \
                full-composition
              append_target reth-keccak \
                'Reth RustCrypto Keccak-256 wrapper' \
                'libreth_keccak_wrapper.a' \
                "$out/rv64/obj/reth-keccak-rustcrypto.a" \
                "$out/rv64/bin/reth-keccak" \
                "$out/rv64/meta/reth-keccak-selected-symbols.txt" \
                _start \
                full-composition
              append_target zesu-ssz \
                'Zesu full harness + allocator + decoder + sink composition' \
                'zesu-ssz (full linked ELF)' \
                "$out/rv64/bin/zesu-ssz" \
                "$out/rv64/bin/zesu-ssz" \
                "$out/rv64/meta/zesu-ssz-selected-symbols.txt" \
                _start \
                full-composition

              cat >> "$out/stats.md" <<EOF

              The measured-artifact column identifies the protocol object (or Rust static archive)
              for compact targets and the decoder object for Zesu's protocol entry; \`zesu-ssz\`
              deliberately names the complete linked ELF. Direct reachability is conservative:
              the analyzer follows direct-call fallthroughs even when a callee is noreturn, so the
              Reth protocol root can retain explicitly labeled harness or runtime code. Ownership
              maps are shared with the matching full-composition rows and are never stripped based
              on inferred behavior.

              ## Structural analysis

              Each \`analysis/<target>.json\` records full and reachable instructions, reachable
              functions, basic blocks, CFG edges, conditional branches, direct calls, loop SCCs,
              maximum direct-call depth, opcode classes, ISA violations, unresolved indirect calls,
              and ownership buckets. The matching Markdown files render the core metrics and ISA
              gate. Complete linked \`objdump -d\` output is in \`objdump/\`; entry-symbol
              disassemblies are \`objdump/sha3-protocol.txt\`, \`objdump/tinfl-protocol.txt\`,
              \`objdump/reth-keccak-protocol.txt\`, and \`objdump/zesu-ssz-parser.txt\`. Raw size
              and symbol output is in \`size.txt\` and \`symbols.txt\`.

              ## Sanity

              SHA-3 was run under \`qemu-riscv64\` with message \`${sha3SampleMessage}\` and produced
              \`${sha3SampleDigest}\`. \`tinfl\` ran successfully, Reth Keccak-256 produced the
              independent Ethereum Keccak-256 vector for \`abc\`, and the raw Zesu harness rejected
              empty input with its expected \`invalid\` exit.
              EOF

              cat > "$out/bin/show-stats" <<EOF
              #!${pkgs.runtimeShell}
              cat "$out/stats.md"
              EOF
              chmod +x "$out/bin/show-stats"

              runHook postInstall
            '';
          };

          sha3Run = pkgs.writeShellApplication {
            name = "sha3";
            runtimeInputs = [ pkgs.qemu-user ];
            text = ''
              exec qemu-riscv64 ${sha3}/bin/sha3 "$@"
            '';
          };

          tinflRun = pkgs.writeShellApplication {
            name = "tinfl";
            runtimeInputs = [ pkgs.qemu-user ];
            text = ''
              exec qemu-riscv64 ${tinfl}/bin/tinfl "$@"
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

          dump = pkgs.writeShellApplication {
            name = "dump";
            text = ''
              if [ "$#" -eq 0 ]; then
                target=sha3
              else
                target="$1"
                shift
              fi
              if [ "$#" -ne 0 ]; then
                echo "usage: dump [sha3|tinfl|reth-keccak|zesu-ssz]" >&2
                exit 64
              fi
              case "$target" in
                sha3) binary=${sha3}/bin/sha3 ;;
                tinfl) binary=${tinfl}/bin/tinfl ;;
                reth-keccak) binary=${rethKeccak}/bin/reth-keccak ;;
                zesu-ssz) binary=${zesuSsz}/bin/zesu-ssz ;;
                *)
                  echo "unknown target: $target" >&2
                  echo "usage: dump [sha3|tinfl|reth-keccak|zesu-ssz]" >&2
                  exit 64
                  ;;
              esac
              exec ${riscvObjdump} -d "$binary"
            '';
          };
        in
        {
          inherit sha3 tinfl rethKeccak zesuProductionObject zesuRawObject zesuValue zesuSsz
            zesuSinkObservability zesuNativeSuite stats dump sha3Run tinflRun rethKeccakRun zesuSszRun;
          reth-keccak = rethKeccak;
          zesu-value = zesuValue;
          zesu-ssz = zesuSsz;
          zesu-sink-observability = zesuSinkObservability;
          zesu-native-suite = zesuNativeSuite;
          default = stats;
        });

      checks = forAllSystems (system: pkgs: {
        inherit (self.packages.${system}) sha3 tinfl rethKeccak zesuProductionObject zesuRawObject
          zesuValue zesuSsz zesuSinkObservability zesuNativeSuite stats dump;
        default = self.packages.${system}.stats;
      });

      apps = forAllSystems (system: pkgs: {
        sha3 = {
          type = "app";
          program = "${self.packages.${system}.sha3Run}/bin/sha3";
          meta.description = "Run the RV64IM_Zicclsm SHA-3 binary under qemu-riscv64";
        };
        tinfl = {
          type = "app";
          program = "${self.packages.${system}.tinflRun}/bin/tinfl";
          meta.description = "Run the RV64IM_Zicclsm miniz tinfl binary under qemu-riscv64";
        };
        reth-keccak = {
          type = "app";
          program = "${self.packages.${system}.rethKeccakRun}/bin/reth-keccak";
          meta.description = "Run the RV64IM_Zicclsm Reth RustCrypto Keccak-256 candidate";
        };
        zesu-ssz = {
          type = "app";
          program = "${self.packages.${system}.zesuSszRun}/bin/zesu-ssz";
          meta.description = "Run the RV64IM_Zicclsm Zesu raw SSZ decoder candidate";
        };
        stats = {
          type = "app";
          program = "${self.packages.${system}.stats}/bin/show-stats";
          meta.description = "Print reproducible RV64IM_Zicclsm stats for all four evaluation targets";
        };
        dump = {
          type = "app";
          program = "${self.packages.${system}.dump}/bin/dump";
          meta.description = "Print RISC-V objdump -d for sha3, tinfl, reth-keccak, or zesu-ssz";
        };
        default = self.apps.${system}.stats;
      });

      devShells = forAllSystems (system: pkgs:
        let
          riscvPkgs = pkgs.pkgsCross.riscv64;
          riscvBinutils = riscvPkgs.buildPackages.binutils;
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.coreutils
              pkgs.gawk
              pkgs.gnused
              pkgs.qemu-user
              riscvPkgs.stdenv.cc
              riscvBinutils
            ];
            shellHook = ''
              echo "Run: nix build .#sha3 --out-link build/sha3, nix run .#sha3, or nix run .#dump -- TARGET"
            '';
          };
        });
    };
}
