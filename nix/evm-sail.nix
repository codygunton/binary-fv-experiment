{ binaryFvLean, evmSail, evmSailCompiler, leanSail, pkgs, repo, zesuSszDecodeSmoke }:
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
    nativeBuildInputs = [ lean429 ];
  } ''
    cp -R ${binaryFvLean}/lean compiled
    chmod -R u+w compiled
    mkdir -p compiled/BinaryFv/Ssz
    mkdir -p compiled/BinaryFv/Ssz/Generated
    mkdir -p compiled/BinaryFv/RiscV/Logic
    mkdir -p compiled/BinaryFv/RiscV/Model
    mkdir -p compiled/BinaryFv/Binary
    export LEAN_PATH=$PWD/compiled:${leanExtraction}/.lake/build/lib/lean:${leanExtraction}/.lake/packages/Sail/.lake/build/lib/lean
    cp ${repo}/BinaryFv/Ssz/Specification.lean Specification.lean
    cp ${repo}/BinaryFv/Ssz/ZesuObservation.lean ZesuObservation.lean
    cp ${repo}/BinaryFv/Ssz/ZigRepresentation.lean ZigRepresentation.lean
    cp ${repo}/BinaryFv/Ssz/Relation.lean Relation.lean
    cp ${repo}/BinaryFv/Ssz/Level1Boundary.lean Level1Boundary.lean
    cp ${repo}/BinaryFv/Ssz/Level1Contracts.lean Level1Contracts.lean
    cp ${repo}/BinaryFv/Ssz/Generated/Level1.lean Level1Generated.lean
    cp ${repo}/BinaryFv/Ssz/MachineContract.lean MachineContract.lean
    cp ${repo}/BinaryFv/Ssz/HostExecution.lean HostExecution.lean
    cp ${repo}/BinaryFv/RiscV/Logic/MemoryWriteFrame.lean MemoryWriteFrame.lean
    cp ${repo}/BinaryFv/RiscV/Logic/RegisterAgree.lean RegisterAgree.lean
    cp ${repo}/BinaryFv/RiscV/Logic/LoadedImage.lean LoadedImage.lean
    cp ${repo}/BinaryFv/Binary/Address.lean BinaryAddress.lean
    cp ${repo}/BinaryFv/RiscV/Model/Address.lean RiscVAddress.lean
    cp ${repo}/BinaryFv/RiscV/Model/State.lean RiscVState.lean
    cp ${repo}/tests/evm-sail/CombinedImportSmoke.lean CombinedImportSmoke.lean
    cp ${repo}/tests/evm-sail/ObservationSmoke.lean ObservationSmoke.lean
    cp ${repo}/tests/evm-sail/DifferentialSmoke.lean DifferentialSmoke.lean
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
    lean -o compiled/BinaryFv/Ssz/Specification.olean Specification.lean
    lean -o compiled/BinaryFv/Ssz/ZesuObservation.olean ZesuObservation.lean
    lean -o compiled/BinaryFv/Ssz/ZigRepresentation.olean ZigRepresentation.lean
    lean -o compiled/BinaryFv/Ssz/Relation.olean Relation.lean
    lean -o compiled/BinaryFv/Ssz/Generated/Level1.olean Level1Generated.lean
    lean -o compiled/BinaryFv/Ssz/MachineContract.olean MachineContract.lean
    lean -o compiled/BinaryFv/Binary/Address.olean BinaryAddress.lean
    lean -o compiled/BinaryFv/RiscV/Model/Address.olean RiscVAddress.lean
    lean -o compiled/BinaryFv/RiscV/Model/State.olean RiscVState.lean
    lean -o compiled/BinaryFv/RiscV/Logic/LoadedImage.olean LoadedImage.lean
    lean -o compiled/BinaryFv/RiscV/Logic/MemoryWriteFrame.olean MemoryWriteFrame.lean
    lean -o compiled/BinaryFv/RiscV/Logic/RegisterAgree.olean RegisterAgree.lean
    lean -o compiled/BinaryFv/Ssz/HostExecution.olean HostExecution.lean
    lean -o compiled/BinaryFv/Ssz/Level1Boundary.olean Level1Boundary.lean
    lean -o compiled/BinaryFv/Ssz/Level1Contracts.olean Level1Contracts.lean
    lean CombinedImportSmoke.lean
    lean ObservationSmoke.lean
    lean DifferentialSmoke.lean
    touch "$out"
  '';
in
{
  public = {
    evmSailCompiler = customSail;
    evmSailLeanExtraction = leanExtraction;
    binaryFvEvmSailCombinedImport = combinedImport;
  };
}
