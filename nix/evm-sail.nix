{ binaryFvLean, evmSail, evmSailCompiler, leanSail, pkgs, repo, zesuSszDecodeSmoke
, zesuSszDecodeCfg, zesuSszDecodeLevel1Manifest, zesuSszDecodeLevel2Manifest, zesuCfgUi }:
let
  customSail = pkgs.ocamlPackages.sail.overrideAttrs (_old: {
    pname = "sail-evm-sail";
    version = "0.20.2-evm-sail-25cc260d";
    src = evmSailCompiler;
    patches = [ ];
  });

  lean429 = pkgs.stdenvNoCC.mkDerivation {
    pname = "lean4";
    version = "4.29.0";
    src = pkgs.fetchurl {
      url = "https://releases.lean-lang.org/lean4/v4.29.0/lean-4.29.0-linux.tar.zst";
      hash = "sha256-CJ9+UT7T6UNtGR9JhjMMC1OAnIa1mX9et/JVUMN0+kg=";
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

  leanExtraction = pkgs.stdenvNoCC.mkDerivation {
    pname = "evm-sail-lean-extraction";
    version = "d0e4aabd";
    src = evmSail;

    nativeBuildInputs = [
      customSail
      lean429
      pkgs.git
      pkgs.gnumake
      pkgs.z3
    ];

    dontConfigure = true;

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR/home"
      mkdir -p "$HOME" extractions/lean/src/.lake/packages/Sail
      cp -R ${leanSail}/. extractions/lean/src/.lake/packages/Sail/
      chmod -R u+w extractions/lean/src/.lake

      make extract-lean \
        SAIL=${customSail}/bin/sail \
        LAKE=${lean429}/bin/lake \
        LEAN_SAIL_LIB="$PWD/extractions/lean/src/.lake/packages/Sail" \
        LEAN_SAIL_LIB_REQUIRE=.lake/packages/Sail

      cd extractions/lean/src
      ${lean429}/bin/lake update Sail
      ${lean429}/bin/lake build
      ${lean429}/bin/lake env lean ${../tests/evm-sail/DecodeSmoke.lean}
      test -s Evm/Lib/Ssz/StatelessInput.lean
      grep -q '^def decode_stateless_input_ref ' Evm/Lib/Ssz/StatelessInput.lean
      grep -q '^def decode_stateless_input ' Evm/Lib/Ssz/StatelessInput.lean
      runHook postBuild
    '';

    installPhase = ''
      mkdir -p "$out"
      cp -R . "$out/"
    '';
  };

  combinedImport = pkgs.runCommand "binary-fv-evm-sail-combined-import" {
    nativeBuildInputs = [ lean429 pkgs.python3 ];
  } ''
    cp -R ${binaryFvLean}/lean compiled
    chmod -R u+w compiled
    mkdir -p compiled/BinaryFv/Specs/SSZ
    mkdir -p compiled/BinaryFv/Zesu/{Contracts,DecodedValue,Elflings,Entrypoints/SszDecodeRoot}
    mkdir -p compiled/BinaryFv/RiscV/Logic
    mkdir -p compiled/BinaryFv/RiscV/Model
    mkdir -p compiled/BinaryFv/RiscV/Execution
    mkdir -p compiled/BinaryFv/RiscV/Proof
    mkdir -p compiled/BinaryFv/RiscV/Elfling
    mkdir -p compiled/BinaryFv/RiscV/Instruction
    mkdir -p compiled/BinaryFv/Binary
    mkdir -p compiled/BinaryFv/ProofProgress
    export LEAN_PATH=$PWD/compiled:${leanExtraction}/.lake/build/lib/lean:${leanExtraction}/.lake/packages/Sail/.lake/build/lib/lean
    cp ${repo}/BinaryFv/Specs/SSZ/Decode.lean Decode.lean
    cp ${repo}/BinaryFv/Zesu/DecodedValue/Observers.lean Observers.lean
    cp ${repo}/BinaryFv/Zesu/DecodedValue/Encoder.lean Encoder.lean
    cp ${repo}/BinaryFv/Zesu/DecodedValue/Representation.lean Representation.lean
    cp ${repo}/BinaryFv/Zesu/DecodedValue/CodecRoundtrip.lean CodecRoundtrip.lean
    cp ${repo}/BinaryFv/Zesu/Contracts/KnownBugs.lean KnownBugs.lean
    cp ${repo}/BinaryFv/Zesu/Contracts/DecodedResultRelation.lean DecodedResultRelation.lean
    cp ${repo}/BinaryFv/Zesu/Contracts/CanonicalOutcome.lean CanonicalOutcome.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level1Boundary.lean Level1Boundary.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level1Contracts.lean Level1Contracts.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level2Contracts.lean Level2Contracts.lean
    cp ${repo}/BinaryFv/Zesu/MachineExecution/Level2RuntimeLeaves.lean Level2RuntimeLeaves.lean
    cp ${repo}/BinaryFv/Zesu/MachineExecution/MemcpyProof.lean MemcpyProof.lean
    cp ${repo}/BinaryFv/Zesu/MachineExecution/InstructionClassSteps.lean InstructionClassSteps.lean
    cp ${repo}/BinaryFv/Zesu/MachineExecution/Level1DecodeInputSteps.lean Level1DecodeInputSteps.lean
    cp ${repo}/BinaryFv/Zesu/MachineExecution/Level1WriteContracts.lean Level1WriteContracts.lean
    cp ${repo}/BinaryFv/Zesu/MachineExecution/Level1WriteSuccessSteps.lean Level1WriteSuccessSteps.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level2Refinement.lean Level2Refinement.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level0Contract.lean Level0Contract.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Executable.lean Executable.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/ExecutableCorrectness.lean ExecutableCorrectness.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/InitialState.lean InitialState.lean
    cp ${repo}/BinaryFv/Zesu/Root.lean ZesuRoot.lean
    cp ${repo}/BinaryFv/Zesu/TrustAudit.lean TrustAudit.lean
    cp ${repo}/BinaryFv/Zesu/Elflings/GeneratedLevel1.lean GeneratedLevel1.lean
    cp ${repo}/BinaryFv/Zesu/Elflings/GeneratedLevel2.lean GeneratedLevel2.lean
    cp ${repo}/BinaryFv/Zesu/Contracts/Machine.lean Machine.lean
    cp ${repo}/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/HostExecution.lean HostExecution.lean
    cp ${repo}/BinaryFv/RiscV/Logic/MemoryWriteFrame.lean MemoryWriteFrame.lean
    cp ${repo}/BinaryFv/RiscV/Logic/RegisterAgree.lean RegisterAgree.lean
    cp ${repo}/BinaryFv/RiscV/Logic/LoadedImage.lean LoadedImage.lean
    cp ${repo}/BinaryFv/RiscV/Logic/SepLogic.lean SepLogic.lean
    cp ${repo}/BinaryFv/RiscV/Logic/Trace.lean Trace.lean
    cp ${repo}/BinaryFv/RiscV/Logic/LoopInduction.lean LoopInduction.lean
    cp ${repo}/BinaryFv/RiscV/Logic/BlockStep.lean BlockStep.lean
    cp ${repo}/BinaryFv/RiscV/Logic/MemFrame.lean MemFrame.lean
    cp ${repo}/BinaryFv/RiscV/Logic/SentinelTrace.lean SentinelTrace.lean
    cp ${repo}/BinaryFv/RiscV/Instruction/DecodeTactic.lean DecodeTactic.lean
    cp ${repo}/BinaryFv/RiscV/Execution/ImageLoad.lean ImageLoad.lean
    cp ${repo}/BinaryFv/RiscV/Execution/MemoryIo.lean MemoryIo.lean
    cp ${repo}/BinaryFv/RiscV/Proof/ImageLoadCorrectness.lean ImageLoadCorrectness.lean
    cp ${repo}/BinaryFv/RiscV/Step/RegisterWrite.lean RegisterWrite.lean
    cp ${repo}/BinaryFv/RiscV/Elfling/FunctionTrace.lean FunctionTrace.lean
    cp ${repo}/BinaryFv/RiscV/Elfling/Boundary.lean Boundary.lean
    cp ${repo}/BinaryFv/RiscV/Elfling/Contract.lean ElflingContract.lean
    cp ${repo}/BinaryFv/RiscV/Elfling/ProgramGeometry.lean ProgramGeometry.lean
    cp ${repo}/BinaryFv/RiscV/Elfling/SequentialSplice.lean SequentialSplice.lean
    cp ${repo}/BinaryFv/ProofProgress/OwnedPc.lean OwnedPc.lean
    cp ${repo}/BinaryFv/RiscV/Elfling/Seg.lean Seg.lean
    cp ${repo}/BinaryFv/RiscV/Instruction/Execute/Load.lean Load.lean
    cp ${repo}/BinaryFv/RiscV/Instruction/Execute/StoreByte.lean StoreByte.lean
    cp ${repo}/BinaryFv/RiscV/Instruction/Execute/Memory.lean Memory.lean
    cp ${repo}/BinaryFv/Binary/Address.lean BinaryAddress.lean
    cp ${repo}/BinaryFv/RiscV/Model/Address.lean RiscVAddress.lean
    cp ${repo}/BinaryFv/RiscV/Model/State.lean RiscVState.lean
    cp ${repo}/tests/evm-sail/CombinedImportSmoke.lean CombinedImportSmoke.lean
    cp ${repo}/tests/evm-sail/ObservationSmoke.lean ObservationSmoke.lean
    cp ${repo}/tests/evm-sail/DifferentialSmoke.lean DifferentialSmoke.lean
    cp ${repo}/tests/evm-sail/EndpointExecutionSmoke.lean EndpointExecutionSmoke.lean
    substituteInPlace ObservationSmoke.lean \
      --replace-fail '@SUCCESS@' '${zesuSszDecodeSmoke}/success.out' \
      --replace-fail '@FAILURE@' '${zesuSszDecodeSmoke}/rejected.out' \
      --replace-fail '@CHANGED@' '${zesuSszDecodeSmoke}/changed.out'
    substituteInPlace DifferentialSmoke.lean \
      --replace-fail '@INPUT@' '${zesuSszDecodeSmoke}/minimal.ssz' \
      --replace-fail '@SUCCESS@' '${zesuSszDecodeSmoke}/success.out' \
      --replace-fail '@CHANGED@' '${zesuSszDecodeSmoke}/changed.out' \
      --replace-fail '@ZERO_INPUT@' '${zesuSszDecodeSmoke}/chain-id-zero.ssz' \
      --replace-fail '@ZERO_SUCCESS@' '${zesuSszDecodeSmoke}/chain-id-zero.out' \
      --replace-fail '@LEGACY_INPUT@' '${zesuSszDecodeSmoke}/legacy-requests.ssz' \
      --replace-fail '@LEGACY_SUCCESS@' '${zesuSszDecodeSmoke}/legacy-requests.out' \
      --replace-fail '@V3_INPUT@' '${zesuSszDecodeSmoke}/legacy-payload.ssz' \
      --replace-fail '@V3_SUCCESS@' '${zesuSszDecodeSmoke}/legacy-payload.out' \
      --replace-fail '@FUTURE_INPUT@' '${zesuSszDecodeSmoke}/future-activation.ssz' \
      --replace-fail '@FUTURE_SUCCESS@' '${zesuSszDecodeSmoke}/future-activation.out' \
      --replace-fail '@EXTRA_INPUT@' '${zesuSszDecodeSmoke}/extra-data-33.ssz' \
      --replace-fail '@EXTRA_SUCCESS@' '${zesuSszDecodeSmoke}/extra-data-33.out' \
      --replace-fail '@KEYS_INPUT@' '${zesuSszDecodeSmoke}/public-key-overflow.ssz' \
      --replace-fail '@KEYS_SUCCESS@' '${zesuSszDecodeSmoke}/public-key-overflow.out' \
      --replace-fail '@HASHES_INPUT@' '${zesuSszDecodeSmoke}/versioned-hash-overflow.ssz' \
      --replace-fail '@HASHES_SUCCESS@' '${zesuSszDecodeSmoke}/versioned-hash-overflow.out'
    substituteInPlace EndpointExecutionSmoke.lean \
      --replace-fail '@INPUT@' '${zesuSszDecodeSmoke}/minimal.ssz'
    lean -o compiled/BinaryFv/Specs/SSZ/Decode.olean Decode.lean
    lean -o compiled/BinaryFv/Zesu/DecodedValue/Observers.olean Observers.lean
    lean -o compiled/BinaryFv/Zesu/DecodedValue/Encoder.olean Encoder.lean
    lean -o compiled/BinaryFv/Zesu/DecodedValue/Representation.olean Representation.lean
    lean -o compiled/BinaryFv/Zesu/DecodedValue/CodecRoundtrip.olean CodecRoundtrip.lean
    lean -o compiled/BinaryFv/Zesu/Contracts/KnownBugs.olean KnownBugs.lean
    lean -o compiled/BinaryFv/Zesu/Contracts/DecodedResultRelation.olean DecodedResultRelation.lean
    lean -o compiled/BinaryFv/Zesu/Contracts/CanonicalOutcome.olean CanonicalOutcome.lean
    lean -o compiled/BinaryFv/Zesu/Elflings/GeneratedLevel1.olean GeneratedLevel1.lean
    lean -o compiled/BinaryFv/Zesu/Elflings/GeneratedLevel2.olean GeneratedLevel2.lean
    lean -o compiled/BinaryFv/Zesu/Contracts/Machine.olean Machine.lean
    lean -o compiled/BinaryFv/Binary/Address.olean BinaryAddress.lean
    lean -o compiled/BinaryFv/RiscV/Model/Address.olean RiscVAddress.lean
    lean -o compiled/BinaryFv/RiscV/Model/State.olean RiscVState.lean
    lean -o compiled/BinaryFv/RiscV/Logic/LoadedImage.olean LoadedImage.lean
    lean -o compiled/BinaryFv/RiscV/Logic/MemoryWriteFrame.olean MemoryWriteFrame.lean
    lean -o compiled/BinaryFv/RiscV/Logic/RegisterAgree.olean RegisterAgree.lean
    lean -o compiled/BinaryFv/RiscV/Logic/SepLogic.olean SepLogic.lean
    lean -o compiled/BinaryFv/RiscV/Logic/Trace.olean Trace.lean
    lean -o compiled/BinaryFv/RiscV/Instruction/Execute/Load.olean Load.lean
    lean -o compiled/BinaryFv/RiscV/Instruction/Execute/StoreByte.olean StoreByte.lean
    lean -o compiled/BinaryFv/RiscV/Instruction/Execute/Memory.olean Memory.lean
    lean -o compiled/BinaryFv/RiscV/Logic/LoopInduction.olean LoopInduction.lean
    lean -o compiled/BinaryFv/RiscV/Logic/BlockStep.olean BlockStep.lean
    lean -o compiled/BinaryFv/RiscV/Logic/MemFrame.olean MemFrame.lean
    lean -o compiled/BinaryFv/RiscV/Logic/SentinelTrace.olean SentinelTrace.lean
    lean -o compiled/BinaryFv/RiscV/Instruction/DecodeTactic.olean DecodeTactic.lean
    lean -o compiled/BinaryFv/RiscV/Execution/ImageLoad.olean ImageLoad.lean
    lean -o compiled/BinaryFv/RiscV/Execution/MemoryIo.olean MemoryIo.lean
    lean -o compiled/BinaryFv/RiscV/Proof/ImageLoadCorrectness.olean ImageLoadCorrectness.lean
    lean -o compiled/BinaryFv/RiscV/Step/RegisterWrite.olean RegisterWrite.lean
    lean -o compiled/BinaryFv/RiscV/Elfling/FunctionTrace.olean FunctionTrace.lean
    lean -o compiled/BinaryFv/RiscV/Elfling/Boundary.olean Boundary.lean
    lean -o compiled/BinaryFv/RiscV/Elfling/Contract.olean ElflingContract.lean
    lean -o compiled/BinaryFv/RiscV/Elfling/ProgramGeometry.olean ProgramGeometry.lean
    lean -o compiled/BinaryFv/RiscV/Elfling/SequentialSplice.olean SequentialSplice.lean
    lean -o compiled/BinaryFv/ProofProgress/OwnedPc.olean OwnedPc.lean
    lean -o compiled/BinaryFv/RiscV/Elfling/Seg.olean Seg.lean
    lean -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/HostExecution.olean HostExecution.lean
    lean -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level1Boundary.olean Level1Boundary.lean
    lean -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level1Contracts.olean Level1Contracts.lean
    lean -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level2Contracts.olean Level2Contracts.lean
    lean -o compiled/BinaryFv/Zesu/MachineExecution/InstructionClassSteps.olean InstructionClassSteps.lean
    lean -o compiled/BinaryFv/Zesu/MachineExecution/Level2RuntimeLeaves.olean Level2RuntimeLeaves.lean
    lean -o compiled/BinaryFv/Zesu/MachineExecution/MemcpyProof.olean MemcpyProof.lean
    lean -o compiled/BinaryFv/Zesu/MachineExecution/Level1DecodeInputSteps.olean Level1DecodeInputSteps.lean
    lean -o compiled/BinaryFv/Zesu/MachineExecution/Level1WriteContracts.olean Level1WriteContracts.lean
    lean -o compiled/BinaryFv/Zesu/MachineExecution/Level1WriteSuccessSteps.olean Level1WriteSuccessSteps.lean
    lean -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level2Refinement.olean Level2Refinement.lean
    lean -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Level0Contract.olean Level0Contract.lean
    lean --tstack=4000000 -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/Executable.olean Executable.lean
    lean --tstack=4000000 -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/ExecutableCorrectness.olean ExecutableCorrectness.lean
    lean --tstack=4000000 -o compiled/BinaryFv/Zesu/Entrypoints/SszDecodeRoot/InitialState.olean InitialState.lean
    lean --tstack=4000000 -o compiled/BinaryFv/Zesu/Root.olean ZesuRoot.lean
    lean --tstack=4000000 -o compiled/BinaryFv/Zesu/TrustAudit.olean TrustAudit.lean 2>&1 | tee trust-audit.log
    python ${repo}/tools/check_root_axioms.py trust-audit.log
    lean CombinedImportSmoke.lean
    lean ObservationSmoke.lean
    lean --tstack=65536 DifferentialSmoke.lean
    lean --tstack=4000000 EndpointExecutionSmoke.lean
    lean ${repo}/tools/RootProofDependencies.lean > root-dependencies.tsv
    mkdir -p "$out"
    cp root-dependencies.tsv "$out/"
  '';

  hlevel2Baseline = pkgs.runCommand "zesu-hlevel2-proof-baseline" {
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    mkdir -p "$out"
    python ${repo}/tools/build_hlevel2_baseline.py \
      --dependencies ${combinedImport}/root-dependencies.tsv \
      --source-root ${repo} \
      --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
      --flame ${zesuSszDecodeCfg}/flame.json \
      --level1 ${zesuSszDecodeLevel1Manifest}/level1-manifest.json \
      --level2 ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
      --output "$out/hlevel2-baseline.json"
    python ${repo}/tools/test_hlevel2_baseline.py \
      ${combinedImport}/root-dependencies.tsv ${repo} \
      ${zesuSszDecodeCfg}/zesu-cfg.json ${zesuSszDecodeCfg}/flame.json \
      ${zesuSszDecodeLevel1Manifest}/level1-manifest.json \
      ${zesuSszDecodeLevel2Manifest}/level2-manifest.json
  '';

  hlevel2Ui = pkgs.runCommand "zesu-rv64-cfg-ui-hlevel2" {
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    cp -R ${zesuCfgUi} "$out"
    chmod -R u+w "$out"
    cp ${hlevel2Baseline}/hlevel2-baseline.json "$out/"
    python ${repo}/tools/build_ssz_proof_map.py \
      --cfg "$out/zesu-cfg.json" --flame "$out/flame.json" \
      --manifest "$out/level1-manifest.json" --evidence "$out/level1-evidence.json" \
      --bindings "$out/level1-boundary-bindings.json" \
      --level2-manifest "$out/level2-manifest.json" \
      --level2-evidence "$out/level2-evidence.json" \
      --level2-bindings "$out/level2-boundary-bindings.json" \
      --hlevel2-baseline "$out/hlevel2-baseline.json" \
      --output "$out/proof-map.json" --flame-progress-output "$out/flame-progress.json"
    python ${repo}/tools/test_ssz_proof_map.py \
      "$out/zesu-cfg.json" "$out/flame.json" "$out/level1-manifest.json" \
      "$out/level1-evidence.json" "$out/level1-boundary-bindings.json" \
      "$out/level2-manifest.json" "$out/level2-evidence.json" \
      "$out/level2-boundary-bindings.json" "$out/hlevel2-baseline.json"
  '';
in
{
  public = {
    evmSailCompiler = customSail;
    evmSailLeanExtraction = leanExtraction;
    binaryFvEvmSailCombinedImport = combinedImport;
    zesuHlevel2ProofBaseline = hlevel2Baseline;
    zesuCfgUi = hlevel2Ui;
  };
}
