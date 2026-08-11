{ binaryFvLean, evmSail, evmSailCompiler, leanSail, pkgs, repo }:
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
    export LEAN_PATH=${binaryFvLean}/lean:${leanExtraction}/.lake/build/lib/lean:${leanExtraction}/.lake/packages/Sail/.lake/build/lib/lean
    lean ${repo}/tests/evm-sail/CombinedImportSmoke.lean
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
