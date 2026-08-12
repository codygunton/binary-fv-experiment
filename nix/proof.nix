{ leanSail, pkgs, repo, rv64, sailRiscv, zesuSszDecodeRv64Elf }:
let
  pinnedLean = pkgs.stdenvNoCC.mkDerivation {
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

  replSource = pkgs.fetchFromGitHub {
    owner = "leanprover-community";
    repo = "repl";
    rev = "495777293cb9cc3c62787a8c11393da1a9dd9505";
    hash = "sha256-0e3QHntg1kFAVVL6pQ9HH8zW8sxW0pYK2xG6ed3j6Qc=";
  };

  sailRiscvGenerated = pkgs.stdenv.mkDerivation {
    pname = "sail-riscv-lean-rv64";
    version = "0.12";
    src = sailRiscv;
    nativeBuildInputs = [ pkgs.cmake pkgs.ninja pkgs.ocamlPackages.sail pkgs.pkg-config pkgs.z3 ];
    buildInputs = [ pkgs.gmp ];
    postPatch = ''
      substituteInPlace handwritten_support/RiscvExtrasExecutable.lean \
        --replace-fail 'import Sail.Sail' 'import LeanRV64DExecutable.Sail.Sail'
      find model -name '*.sail' -type f -exec sed -i \
        -e 's/\<Vector\>/VectorPayload/g' -e 's/"VectorPayload"/"Vector"/g' {} +
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
    installPhase = ''cp -r model/Lean_RV64D_executable "$out"'';
  };

  sailRiscvLean = pkgs.runCommand "sail-riscv-lean-rv64-4.29" { } ''
    cp -R ${sailRiscvGenerated} "$out"
    chmod -R u+w "$out"
    rm -rf "$out/LeanRV64DExecutable/Sail"
    mkdir "$out/Sail"
    cp ${leanSail}/Sail.lean "$out/Sail.lean"
    cp ${leanSail}/Sail/{Attr,BitVec,IntRange,Sail}.lean "$out/Sail/"
    find "$out/LeanRV64DExecutable" -name '*.lean' -type f -exec sed -i \
      's/import LeanRV64DExecutable\.Sail\./import Sail./g' {} +
    substituteInPlace "$out/LeanRV64DExecutable/HexBitsSigned.lean" \
      --replace-fail '(parse_hex_bits n (String.drop str 1))' \
        '(parse_hex_bits n (String.drop str 1).toString)' \
      --replace-fail '(valid_hex_bits n (String.drop str 1))' \
        '(valid_hex_bits n (String.drop str 1).toString)'
  '';

  zesuSszDecodeProgramImageLean = pkgs.runCommand "zesu-ssz-decode-program-image-lean" {
    nativeBuildInputs = [ (pkgs.python3.withPackages (ps: [ ps.pyelftools ])) ];
  } ''
    mkdir -p "$out"
    python ${repo}/tools/generate_program_image_lean.py \
      --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      --expected-sha256 3e13afeae5719e10c65a89ea1b8a9afdb60b360e7e18faa81c31a71a44dcd8fb \
      --output "$out/ZesuSszDecodeProgramImage.lean"
  '';

  binaryFvLean = pkgs.runCommand "binary-fv-lean" {
    nativeBuildInputs = [ pinnedLean pkgs.coreutils pkgs.jq ];
  } ''
    cp -R ${repo} source
    chmod -R u+w source
    cd source
    mkdir -p build .lake/packages/repl "$TMPDIR/home"
    ln -s ${sailRiscvLean} build/sail-riscv-lean
    cp ${zesuSszDecodeProgramImageLean}/ZesuSszDecodeProgramImage.lean .
    cp -a ${replSource}/. .lake/packages/repl/
    chmod -R u+w .lake/packages/repl
    ${pkgs.jq}/bin/jq '
      .packages |= map(if .name == "repl" then
        { type: "path", scope: .scope, name: .name, manifestFile: .manifestFile,
          inherited: .inherited, dir: ".lake/packages/repl", configFile: .configFile }
        else . end)
    ' lake-manifest.json > lake-manifest.nix.json
    mv lake-manifest.nix.json lake-manifest.json
    substituteInPlace lakefile.lean \
      --replace-fail 'require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.29.0"' \
      'require repl from ".lake/packages/repl"'
    export HOME="$TMPDIR/home"
    lake build Sail BinaryFv BinaryFvZesuArtifactsImage BinaryFv.Zesu.MachineExecution.Level0MainSteps \
      BinaryFv.RiscV.Step.RegisterWrite
    mkdir -p "$out"
    cp -R .lake/build/lib/lean "$out/"
  '';

  devShell = pkgs.mkShell {
    inputsFrom = [ rv64.devShell ];
    packages = [ pkgs.cmake pkgs.elan pkgs.git pkgs.gmp pkgs.ninja pkgs.ocamlPackages.sail pkgs.pkg-config pkgs.z3 ];
  };
in
{
  public = {
    inherit binaryFvLean sailRiscvLean;
    binary-fv-lean = binaryFvLean;
    sail-riscv-lean = sailRiscvLean;
  };
  inherit devShell;
}
