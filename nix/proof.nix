{ etheorem, executionSpecs, pkgs, repo, rv64, sailRiscv, targets }:
let
  zesuSsz = targets.public.zesuSsz;
  zesuAbiManifest = targets.public.zesuAbiManifest;
  elflingProgram = targets.public.elflingProgram;
  machineRegions = targets.public.machineRegions;
  machineRegionsUi = targets.public.machineRegionsUi;
  elflingDecoderLlvmIr = targets.public.elflingDecoderLlvmIr;

  pinnedLean = pkgs.stdenvNoCC.mkDerivation {
    pname = "lean4";
    version = "4.26.0-nightly-2025-11-18";
    src = pkgs.fetchurl {
      url = "https://github.com/leanprover/lean4-nightly/releases/download/nightly-2025-11-18/lean-4.26.0-nightly-2025-11-18-linux.tar.zst";
      hash = "sha256-JSY4OYzDiI0CIdyZnw6uRpR9MytV6g7b77f4IQwpEXQ=";
    };

    nativeBuildInputs = [ pkgs.autoPatchelfHook pkgs.zstd ];
    buildInputs = [ pkgs.stdenv.cc.cc pkgs.zlib ];

    unpackPhase = ''
      mkdir source
      tar --use-compress-program=unzstd -xf "$src" -C source --strip-components=1
      sourceRoot=source
    '';

    installPhase = ''
      mkdir -p "$out"
      cp -a . "$out"
    '';
  };

  replSource = pkgs.fetchFromGitHub {
    owner = "leanprover-community";
    repo = "repl";
    rev = "a9a6f5bac483d65d08f6226e0ed653f03c479fb7";
    hash = "sha256-+8iF01UVXerfvRPUPDGk9L7CpPXUxrZMxvBG2CUC6PE=";
  };

  sailRiscvLean = pkgs.stdenv.mkDerivation {
    pname = "sail-riscv-lean-rv64";
    version = "0.12";
    src = sailRiscv;

    nativeBuildInputs = [
      pkgs.cmake
      pkgs.ninja
      pkgs.ocamlPackages.sail
      pkgs.pkg-config
      pkgs.z3
    ];
    buildInputs = [ pkgs.gmp ];

    postPatch = ''
      substituteInPlace handwritten_support/RiscvExtrasExecutable.lean \
        --replace-fail 'import Sail.Sail' \
        'import LeanRV64DExecutable.Sail.Sail'

      find model -name '*.sail' -type f -exec sed -i \
        -e 's/\<Vector\>/VectorPayload/g' \
        -e 's/"VectorPayload"/"Vector"/g' {} +

      substituteInPlace model/postlude/insts_end.sail \
        --replace-fail '// End definitions' \
        $'// Omitted optional modules are disabled in the RV64IM model.\nfunction clause currentlyEnabled(_) = false\n\n// End definitions'
    '';

    cmakeFlags = [
      "-DDOWNLOAD_CLI11=OFF"
      "-DDOWNLOAD_JSONCONS=OFF"
      "-DSAIL_MODULES=main;I_insts;M_insts"
    ];

    buildPhase = ''
      runHook preBuild
      cmake --build . --target generated_lean_executable_rv64d
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      cp -r model/Lean_RV64D_executable "$out"
      runHook postInstall
    '';
  };

  zesuSszElfLean = pkgs.runCommand "binary-fv-zesu-ssz-elf-lean" {
    nativeBuildInputs = [ pkgs.coreutils pkgs.gawk ];
  } ''
    mkdir -p "$out"
    {
      printf '%s\n' 'namespace ZesuSszElf'
      printf '\n'
      printf '%s\n' 'set_option maxRecDepth 100000'
      printf '%s\n' '/-- Generated from the canonical Nix-built Zesu SSZ ELF. -/'
      ${pkgs.coreutils}/bin/od -An -v -tu1 ${zesuSsz}/bin/zesu-ssz |
        ${pkgs.gawk}/bin/awk '
          {
            for (i = 1; i <= NF; i++) {
              if (count % 512 == 0) {
                if (count != 0) printf "]\n\n"
                printf "def bytes_chunk_%d : ByteArray := ByteArray.mk #[\n", count / 512
              }
              if (count % 12 == 0) printf "  "
              printf "0x%02x, ", $i
              count++
              if (count % 12 == 0) printf "\n"
            }
          }
          END {
            if (count % 12 != 0) printf "\n"
            printf "]\n\n"
            printf "def bytes : ByteArray := "
            for (i = 0; i <= (count - 1) / 512; i++) {
              if (i != 0) printf " ++ "
              printf "bytes_chunk_%d", i
            }
            printf "\n"
          }
        '
      printf '\n'
      printf '%s\n' 'end ZesuSszElf'
    } > "$out/ZesuSszElf.lean"
  '';

  # The SSZ proof imports the executable SizzLean decoder, but only its pure wire-format closure.
  # Keep the source-level pins here: `SizzLean`'s normal Lake package also pulls its SHA/OpenSSL
  # packages, which the decoder does not need and the BinaryFv proof must not link.
  sizzLeanClosure = pkgs.runCommand "binary-fv-sizzlean-closure" {
    nativeBuildInputs = [ pkgs.coreutils pkgs.gnused pkgs.gnugrep ];
  } ''
    copy_checked() {
      source="$1"
      expected="$2"
      destination="$3"
      actual="$(${pkgs.coreutils}/bin/sha256sum "$source" | cut -d ' ' -f 1)"
      test "$actual" = "$expected"
      cp "$source" "$destination"
    }

    mkdir -p "$out/SizzLean/Spec" "$out/SizzLean/Proofs"
    sizzlean_root=${etheorem}/packages/SizzLean/SizzLean
    spec_root="$sizzlean_root/Spec"
    copy_checked "$spec_root/Type.lean" \
      ef7fd929a536cf157808cb4ace0255e3992dda566f93b77737166c3fb9139711 \
      "$out/SizzLean/Spec/Type.lean"
    copy_checked "$spec_root/Interp.lean" \
      f23160310811f477fb7c367e6c4c5186d302fe027447a414c25cde9486dfc52b \
      "$out/SizzLean/Spec/Interp.lean"
    copy_checked "$spec_root/Constants.lean" \
      8042328b192f32697ce2f9fbda5bd91cb15c746601c4c9c946f96d7e5fb78b96 \
      "$out/SizzLean/Spec/Constants.lean"
    copy_checked "$spec_root/SSZError.lean" \
      0e8ddfb73dc7ac7d6a56a2943e950051abd9310b25465e2f415c8a64327c4448 \
      "$out/SizzLean/Spec/SSZError.lean"
    copy_checked "$spec_root/Serialize.lean" \
      d830cb74ded4cddbba87e4400ebaef71060f527317c5783d9a4fe9d02e7c0ae2 \
      "$out/SizzLean/Spec/Serialize.lean"
    copy_checked "$spec_root/Deserialize.lean" \
      db05b7d663445dc79e563ef0095482544ff950a7b51fd89e14fcb301b4830ef5 \
      "$out/SizzLean/Spec/Deserialize.lean"
    copy_checked "$spec_root/BasicSupported.lean" \
      5c50a2609d3891ba32016b0dbea3af684e0161ca0960977ebe4e8fecd86719e0 \
      "$out/SizzLean/Spec/BasicSupported.lean"
    copy_checked "$spec_root/Supported.lean" \
      50f32f78c5c0190812b480cf4e749fe9462a416da7667e82eb918db46f123bcc \
      "$out/SizzLean/Spec/Supported.lean"
    copy_checked "$spec_root/MaxByteLength.lean" \
      95529cf63920db116500d12e8d7cf9e1eab6d0d37f21a714d143d8ab4dbd818d \
      "$out/SizzLean/Spec/MaxByteLength.lean"
    copy_checked "$sizzlean_root/Proofs/BitPack.lean" \
      903cb8a62cac4f8a2444ec8b1ab7d270bb2561f7801f79e3fa0c4bc4cfd91cc5 \
      "$out/SizzLean/Proofs/BitPack.lean"
    copy_checked "$sizzlean_root/Proofs/Bool.lean" \
      4f28e9300e5d582a986fc81398dfb1ba289f1e43551f0fba6791953229dafacf \
      "$out/SizzLean/Proofs/Bool.lean"
    copy_checked "$sizzlean_root/Proofs/ContainerFixed.lean" \
      a4cfbbe8e33e9aaf8a2664e7b98a18425b5763b5bc8ee83f352e3c2673cf5f17 \
      "$out/SizzLean/Proofs/ContainerFixed.lean"
    copy_checked "$sizzlean_root/Proofs/FixedElems.lean" \
      1173b8b1dc05a9b799872b4e1044e3debb3558e7228ef441367f23a2977f417c \
      "$out/SizzLean/Proofs/FixedElems.lean"
    copy_checked "$sizzlean_root/Proofs/ListFixed.lean" \
      5912c1ce7e664cf4064d53e6e2a45b4c460b03d436a68f0fad05c6c46753c4f2 \
      "$out/SizzLean/Proofs/ListFixed.lean"
    copy_checked "$sizzlean_root/Proofs/SerializeSize.lean" \
      22da51a02f5845b648d1ecf37efa754df8afc42963314318ccf76b221ee1d16f \
      "$out/SizzLean/Proofs/SerializeSize.lean"
    copy_checked "$sizzlean_root/Proofs/Simp.lean" \
      ef266efca1c8730900c4b186383f0b2cac0677e6a608460cc9c670a61f3296e1 \
      "$out/SizzLean/Proofs/Simp.lean"
    copy_checked "$sizzlean_root/Proofs/SimpAttrs.lean" \
      63006416cad34b6e65dc7a60a5cf62765c994e5fd806bb881abcbd62139d72ca \
      "$out/SizzLean/Proofs/SimpAttrs.lean"
    copy_checked "$sizzlean_root/Proofs/SizeBound.lean" \
      a45050a4d9fed9c67f5e6da7a131854666e791048bf5e0c58423db16e493d60b \
      "$out/SizzLean/Proofs/SizeBound.lean"
    copy_checked "$sizzlean_root/Proofs/UInt.lean" \
      629894b6385041763094118c1a16a2383fa4cb3f5af5f6f0f2ae693ef6b0cdae \
      "$out/SizzLean/Proofs/UInt.lean"
    copy_checked "$sizzlean_root/Proofs/VectorFixed.lean" \
      1c7c7e11451beb845705769f2ddb073b87666ee9c01323a336d364f489a5a890 \
      "$out/SizzLean/Proofs/VectorFixed.lean"

    # The pinned proof files target SizzLean's Lean release, which provides this lemma. Restate it
    # for this project's pinned nightly and import it only where upstream names it.
    ${pkgs.coreutils}/bin/cat > "$out/SizzLean/Compat.lean" <<'COMPAT'
theorem ByteArray.size_push (bytes : ByteArray) (byte : UInt8) :
    (bytes.push byte).size = bytes.size + 1 := by
  cases bytes
  exact Array.size_push ..
COMPAT
    ${pkgs.gnused}/bin/sed -i '1i import SizzLean.Compat' "$out/SizzLean/Proofs/UInt.lean"
    ${pkgs.gnused}/bin/sed -i '1i import SizzLean.Compat' "$out/SizzLean/Proofs/BitPack.lean"

    # The offset-correspondence proofs use the pinned decoder's two offset-table walkers. Widen only their
    # visibility after checking the pristine source hash above; their definitions are unchanged.
    deserialize="$out/SizzLean/Spec/Deserialize.lean"
    test "$(${pkgs.gnugrep}/bin/grep -c -x -F 'private def extractFieldOffsets (b : ByteArray) :' "$deserialize")" = 1
    test "$(${pkgs.gnugrep}/bin/grep -c -x -F 'private def extractCollOffsets (b : ByteArray) :' "$deserialize")" = 1
    ${pkgs.gnused}/bin/sed -i \
      -e 's|^private def extractFieldOffsets (b : ByteArray) :$|def extractFieldOffsets (b : ByteArray) :|' \
      -e 's|^private def extractCollOffsets (b : ByteArray) :$|def extractCollOffsets (b : ByteArray) :|' \
      "$deserialize"
    test "$(${pkgs.gnugrep}/bin/grep -c -x -F 'def extractFieldOffsets (b : ByteArray) :' "$deserialize")" = 1
    test "$(${pkgs.gnugrep}/bin/grep -c -x -F 'def extractCollOffsets (b : ByteArray) :' "$deserialize")" = 1
    ${pkgs.coreutils}/bin/printf '%s\n' \
      etheorem=032ab6c6d67186ba60b734e0f2c44ba1bb8b6fb0 \
      SizzLean/Spec/Type.lean=ef7fd929a536cf157808cb4ace0255e3992dda566f93b77737166c3fb9139711 \
      SizzLean/Spec/Interp.lean=f23160310811f477fb7c367e6c4c5186d302fe027447a414c25cde9486dfc52b \
      SizzLean/Spec/Constants.lean=8042328b192f32697ce2f9fbda5bd91cb15c746601c4c9c946f96d7e5fb78b96 \
      SizzLean/Spec/SSZError.lean=0e8ddfb73dc7ac7d6a56a2943e950051abd9310b25465e2f415c8a64327c4448 \
      SizzLean/Spec/Serialize.lean=d830cb74ded4cddbba87e4400ebaef71060f527317c5783d9a4fe9d02e7c0ae2 \
      SizzLean/Spec/Deserialize.lean=db05b7d663445dc79e563ef0095482544ff950a7b51fd89e14fcb301b4830ef5 \
      SizzLean/Spec/BasicSupported.lean=5c50a2609d3891ba32016b0dbea3af684e0161ca0960977ebe4e8fecd86719e0 \
      SizzLean/Spec/Supported.lean=50f32f78c5c0190812b480cf4e749fe9462a416da7667e82eb918db46f123bcc \
      SizzLean/Spec/MaxByteLength.lean=95529cf63920db116500d12e8d7cf9e1eab6d0d37f21a714d143d8ab4dbd818d \
      proof-closure=size-bound \
      patch=offset-walkers-public-visibility-only \
      > "$out/provenance.txt"
  '';

  binaryFvLean = pkgs.runCommand "binary-fv-lean" {
    nativeBuildInputs = [ pinnedLean pkgs.coreutils pkgs.git pkgs.jq pkgs.python3 ];
  } ''
    cp -R ${repo} source
    chmod -R u+w source
    cd source

    mkdir -p build .lake/packages/repl "$TMPDIR/home"
    ln -s ${sailRiscvLean} build/sail-riscv-lean
    ln -s ${sizzLeanClosure} build/sizzlean-lean
    ln -s ${zesuSszElfLean} build/zesu-ssz-elf-lean
    ln -s ${zesuAbiManifest} build/zesu-abi-lean
    ln -s ${elflingProgram} build/elfling-program-lean
    ln -s ${machineRegions} build/machine-regions-lean
    cp -a ${replSource}/. .lake/packages/repl/
    chmod -R u+w .lake/packages/repl
    ${pkgs.jq}/bin/jq '
      .packages |= map(
        if .name == "repl" then
          {
            type: "path",
            scope: .scope,
            name: .name,
            manifestFile: .manifestFile,
            inherited: .inherited,
            dir: ".lake/packages/repl",
            configFile: .configFile
          }
        else . end
      )
    ' lake-manifest.json > lake-manifest.nix.json
    mv lake-manifest.nix.json lake-manifest.json
    substituteInPlace lakefile.lean \
      --replace-fail 'require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.26.0"' \
      'require repl from ".lake/packages/repl"'

    export HOME="$TMPDIR/home"

    # Layer audit. The RISC-V and Binary layers are generic over the binary under analysis; a
    # dependency on the SSZ target would make them a lie. A docstring cannot enforce this, so audit
    # the import graph: no generic module may import the target umbrella or anything beneath it.
    # Prose that motivates a generic rule by naming the Zesu artifact is not a dependency and is
    # deliberately not matched -- the violation is the import, not the spelling.
    layerViolations=$(grep -rn "^import BinaryFv\.Zesu" BinaryFv/RiscV/ BinaryFv/Binary/ \
      BinaryFv/RiscV.lean BinaryFv/Binary.lean 2>/dev/null || true)
    if [ -n "$layerViolations" ]; then
      echo "Layer violation: the RISC-V/Binary layers must not import the Zesu target." >&2
      echo "$layerViolations" >&2
      exit 1
    fi

    # The approved fixed-artifact native_decide exception covers closed facts about the pinned ELF.
    # Those are SSZ-target facts by construction, so no generic module may use native_decide.
    nativeInGeneric=$(grep -rn "native_decide" BinaryFv/RiscV/ BinaryFv/Binary/ 2>/dev/null || true)
    if [ -n "$nativeInGeneric" ]; then
      echo "native_decide is not permitted in the generic RISC-V/Binary layers." >&2
      echo "$nativeInGeneric" >&2
      exit 1
    fi

    python3 tools/check_lean_trust.py

    mkdir -p "$out/profiles"
    # Profile the compliance theorem's import closure, not the separate generated-data evidence.
    lake build BinaryFv.Zesu.Root 2>&1 | tee "$out/root-build.log"
    lake env lean BinaryFv/Zesu/TrustAudit.lean
    python3 tools/lean_profile.py --build-log "$out/root-build.log" \
      --out "$out/profiles" report > "$out/profile.md"
    # Traced captures are best-effort evidence, never the bar: `--jobs 1` keeps peak memory to one
    # traced elaboration (four in parallel exhausted the 16 GB CI runner and the job was
    # memory-killed), the 45 s threshold limits tracing to the few genuinely hot modules, and a
    # capture failure downgrades to a logged warning while the ranked timing table above — the
    # per-PR metric — still comes from the untraced build log.
    if ! python3 tools/lean_profile.py --build-log "$out/root-build.log" \
        --out "$out/profiles" capture --threshold 45 --jobs 1; then
      echo "warning: trace.profiler capture failed; continuing without traced profiles" >&2
    fi
    if find "$out/profiles" -name '*.json' -print -quit | grep -q .; then
      python3 tools/lean_profile.py --out "$out/profiles" merge
    fi

    # Serial supporting-target build. Do not build the `BinaryFv` umbrella here: it contains modules
    # outside `root_compliance` and currently has a known duplicate generated register wrapper.
    # The proof gate above and manifest exporter below compile their exact import closures.
    # This Lake has no job-count flag; its build pool is the Lean task pool, so
    # `LEAN_NUM_THREADS=1` is the serialization knob (verified: six 3 s modules build in 3.6 s
    # on the default pool and 19.6 s under this variable).
    LEAN_NUM_THREADS=1 lake build repl GeneratedProgram BinaryFv.Binary.ProgramImageTest \
      2>&1 | tee "$out/full-build.log"

    # Zesu production-binary validation remains diagnostic-only and is outside `root_compliance`.
    # Preserve its failure log without making the proof/manifest artifact depend on unrelated test
    # modules (currently one such module has a known duplicate generated register wrapper).
    if ! LEAN_NUM_THREADS=1 lake build ZesuVerificationTests > "$out/zesu-verification-tests.log" 2>&1; then
      echo "warning: diagnostic ZesuVerificationTests target failed; see zesu-verification-tests.log" >&2
    fi

    # Export only records whose exact-PC and composition proofs elaborated above.  The marker keeps
    # ordinary Lean diagnostics out of the JSON artifact.
    lake env lean tools/export_level4_machine_proof_manifests.lean \
      | sed -n 's/^MACHINE_PROOF_MANIFEST_JSON=//p' \
      > "$out/level4-machine-proof-manifests.json"
    jq -e '.schemaVersion == 1 and .ownerInstructionCount == 172' \
      "$out/level4-machine-proof-manifests.json" >/dev/null
  '';

  # Executable Lean rendering of the pinned SSZ specification. This is a test oracle, separate from
  # the RV64 production ELF observed by the Level 4 evidence gate.
  sszOracle = pkgs.runCommand "ssz-oracle" {
    nativeBuildInputs = [ pinnedLean pkgs.autoPatchelfHook pkgs.coreutils ];
    buildInputs = [ pkgs.stdenv.cc.cc ];
  } ''
    cp -R ${repo} source
    chmod -R u+w source
    cd source
    cp tools/ssz-oracle/Main.lean SszOracle.lean
    mkdir -p build "$out/bin"
    ln -s ${sizzLeanClosure} build/sizzlean-lean
    rm lake-manifest.json
    cat > lakefile.lean <<'LAKE'
    import Lake
    open Lake DSL
    package sszOracle
    lean_lib SizzLeanPinned where
      srcDir := "build/sizzlean-lean"
      roots := #[`SizzLean.Spec.Type, `SizzLean.Spec.Interp, `SizzLean.Spec.Constants,
        `SizzLean.Spec.SSZError, `SizzLean.Spec.Serialize, `SizzLean.Spec.Deserialize,
        `SizzLean.Spec.BasicSupported, `SizzLean.Spec.Supported, `SizzLean.Spec.MaxByteLength]
    lean_lib SszOracleSpec where
      roots := #[`BinaryFv.Specs.SSZ.AmsterdamV4]
    lean_exe ssz_oracle where
      root := `SszOracle
    LAKE
    export HOME="$TMPDIR/home"
    mkdir -p "$HOME"
    lake update
    lake build ssz_oracle
    cp .lake/build/bin/ssz_oracle "$out/bin/ssz_oracle"
    autoPatchelf "$out"
  '';

  ethereumTypes = pkgs.python3Packages.buildPythonPackage rec {
    pname = "ethereum-types";
    version = "0.4.1";
    pyproject = true;
    src = pkgs.fetchurl {
      url = "https://files.pythonhosted.org/packages/e5/bf/6c15ea3372a19b4df9d47ba08d32ad0751c059c31c7f15842cf12e5736bd/ethereum_types-0.4.1.tar.gz";
      hash = "sha256-wO7kRkxC7YIX38knQA25gVfMiwklLs76cDF2SW2+O00=";
    };
    build-system = [ pkgs.python3Packages.hatchling ];
    dependencies = with pkgs.python3Packages; [ mypy-extensions typing-extensions ];
    doCheck = false;
  };

  ethereumRlp = pkgs.python3Packages.buildPythonPackage rec {
    pname = "ethereum-rlp";
    version = "0.1.6";
    pyproject = true;
    src = pkgs.fetchurl {
      url = "https://files.pythonhosted.org/packages/54/55/1fab3dea8f912459751cb39ad4500e165344963af2dbd5fa699befe3e8d4/ethereum_rlp-0.1.6.tar.gz";
      hash = "sha256-7eNvU7U8jaIfGSWaZ27th5CVDUfwtCy5KKyKPFYigvM=";
    };
    build-system = [ pkgs.python3Packages.setuptools ];
    dependencies = [ ethereumTypes pkgs.python3Packages.typing-extensions ];
    doCheck = false;
  };

  ethRemerkleable = pkgs.python3Packages.buildPythonPackage rec {
    pname = "eth-remerkleable";
    version = "0.1.29";
    pyproject = true;
    src = pkgs.fetchurl {
      url = "https://files.pythonhosted.org/packages/37/16/b91f3fc0c46f8ff597f26fbbbc1d8fbe7ab8d5103e00546417455298b449/eth_remerkleable-0.1.29.tar.gz";
      hash = "sha256-JBiwCM10cdD1qzflqXhO9BhOUDGS5vOMIj/iW3y7ysM=";
    };
    build-system = [ pkgs.python3Packages.setuptools ];
    doCheck = false;
  };

  executionSpecsPython = pkgs.python3.withPackages (pythonPackages: [
    pythonPackages.coincurve pythonPackages.cryptography pythonPackages.pycryptodome
    pythonPackages.py-ecc pythonPackages.pydantic ethereumTypes ethereumRlp ethRemerkleable
  ]);

  level4ContractEvidence =
    let
      tests = builtins.path {
        path = repo + "/verification-target/zesu/tests";
        name = "zesu-level4-contract-evidence-tests";
      };
      trace = builtins.path {
        path = repo + "/verification-target/zesu/trace";
        name = "zesu-level4-contract-evidence-trace";
      };
    in pkgs.runCommand "zesu-level4-contract-evidence" {
      nativeBuildInputs = [ executionSpecsPython pkgs.gcc pkgs.glib pkgs.pkg-config pkgs.qemu-user pkgs.util-linux ];
    } ''
      set -euo pipefail
      cp -R ${tests} tests
      cp -R ${trace} trace
      chmod -R u+w tests trace
      gcc -shared -fPIC -O2 -o trace/qemu_trace_plugin.so trace/qemu_trace_plugin.c \
        -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0)
      export PYTHONPATH=${executionSpecs}/src
      python3 tests/level4_contract_evidence.py \
        --inventory ${machineRegions}/level4-boundaries.json \
        --reference-python ${executionSpecsPython}/bin/python3 \
        --reference-program tests/ssz_value_reference.py \
        --lean-binary ${sszOracle}/bin/ssz_oracle \
        --zesu-value-binary ${targets.public.zesuValue}/bin/zesu-ssz-value \
        --qemu ${rv64.qemuRiscv64} --plugin trace/qemu_trace_plugin.so \
        --rv64-binary ${zesuSsz}/bin/zesu-ssz --out-json "$out/report.json"
    '';

  machineProofMapUi = pkgs.runCommand "zesu-machine-regions-proof-map-ui" {
    nativeBuildInputs = [ pkgs.coreutils pkgs.diffutils pkgs.jq pkgs.python3 ];
  } ''
    set -euo pipefail
    mkdir -p source/tools/proof-map source/lean run1 run2 "$out"
    cp -R ${machineRegionsUi}/. "$out/"
    cp ${machineRegions}/level4-boundaries.json "$out/"
    cp ${binaryFvLean}/level4-machine-proof-manifests.json "$out/"
    cp ${level4ContractEvidence}/report.json "$out/level4-contract-evidence.json"
    cp ${repo}/tools/generate_proof_map.py source/tools/
    cp ${repo}/tools/generate_proof_map_test.py source/tools/
    cp ${repo}/tools/analyze_machine_proof_corridors.py source/tools/
    cp ${repo}/tools/analyze_machine_proof_corridors_test.py source/tools/
    cp ${repo}/tools/proof-map/level4-authoring.json source/tools/proof-map/
    cp -R ${repo}/BinaryFv/Zesu/MachineExecution/. source/lean/
    cd source
    python3 -m unittest tools/analyze_machine_proof_corridors_test.py tools/generate_proof_map_test.py
    generate() {
      python3 tools/generate_proof_map.py \
        --machine-regions ${machineRegions}/machine-regions.json \
        --level4-boundaries ${machineRegions}/level4-boundaries.json \
        --manifests ${binaryFvLean}/level4-machine-proof-manifests.json \
        --authoring tools/proof-map/level4-authoring.json \
        --lean-root lean \
        --analyzer tools/analyze_machine_proof_corridors.py \
        --llvm-ir ${elflingDecoderLlvmIr}/decoder.ll \
        --out "$1/proof-map.json"
    }
    generate ../run1
    generate ../run2
    cmp -s ../run1/proof-map.json ../run2/proof-map.json \
      || { echo "PROOF MAP GENERATOR NON-DETERMINISTIC" >&2; exit 1; }
    jq -e '.schemaVersion == 1 and (.instructions | length) == 172 and
      .formalCoverage.localPcCount == 32 and .compilerProvenance.state == "explanatory-only"' \
      ../run1/proof-map.json >/dev/null
    cp ../run1/proof-map.json "$out/"
  '';

  devShell = pkgs.mkShell {
    inputsFrom = [ rv64.devShell ];
    packages = [
      pkgs.cmake
      pkgs.elan
      pkgs.git
      pkgs.gmp
      pkgs.ninja
      pkgs.ocamlPackages.sail
      pkgs.pkg-config
      pkgs.z3
    ];
  };
in
{
  public = {
    inherit binaryFvLean level4ContractEvidence machineProofMapUi sailRiscvLean sizzLeanClosure
      sszOracle zesuSszElfLean;

    binary-fv-lean = binaryFvLean;
    machine-regions-ui = machineProofMapUi;
    sail-riscv-lean = sailRiscvLean;
    sizzlean-lean = sizzLeanClosure;
    ssz-oracle = sszOracle;
    ssz-level4-contract-evidence = level4ContractEvidence;
    zesu-ssz-elf-lean = zesuSszElfLean;
  };

  inherit devShell;
}
