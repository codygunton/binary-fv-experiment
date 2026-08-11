{ pkgs, repo, rv64, sailRiscv }:
let
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

  binaryFvLean = pkgs.runCommand "binary-fv-lean" {
    nativeBuildInputs = [ pinnedLean pkgs.coreutils pkgs.jq ];
  } ''
    cp -R ${repo} source
    chmod -R u+w source
    cd source
    mkdir -p build .lake/packages/repl "$TMPDIR/home"
    ln -s ${sailRiscvLean} build/sail-riscv-lean
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
      --replace-fail 'require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.26.0"' \
      'require repl from ".lake/packages/repl"'
    export HOME="$TMPDIR/home"
    lake build BinaryFv
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
