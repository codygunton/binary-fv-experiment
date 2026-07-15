{ pkgs, repo, rv64, sailRiscv, scrollFv, targets }:
let
  rethKeccak = targets.public.rethKeccak;

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

  rethKeccakElfLean = pkgs.runCommand "binary-fv-reth-keccak-elf-lean" {
    nativeBuildInputs = [ pkgs.coreutils pkgs.gawk ];
  } ''
    mkdir -p "$out"
    {
      printf '%s\n' 'namespace BinaryFv.Keccak.RethKeccakElf'
      printf '\n'
      printf '%s\n' 'set_option maxRecDepth 100000'
      printf '%s\n' '/-- Generated from the canonical Nix-built Reth RustCrypto Keccak ELF. -/'
      printf '%s\n' 'def bytes : ByteArray := ByteArray.mk #['
      ${pkgs.coreutils}/bin/od -An -v -tu1 ${rethKeccak}/bin/reth-keccak |
        ${pkgs.gawk}/bin/awk '
          {
            for (i = 1; i <= NF; i++) {
              if (count % 12 == 0) {
                printf "  "
              }
              printf "0x%02x, ", $i
              count++
              if (count % 12 == 0) {
                printf "\n"
              }
            }
          }
          END {
            if (count % 12 != 0) {
              printf "\n"
            }
          }
        '
      printf '%s\n' ']'
      printf '\n'
      printf '%s\n' 'end BinaryFv.Keccak.RethKeccakElf'
    } > "$out/RethKeccakElf.lean"
  '';

  keccakSpecLean = pkgs.runCommand "binary-fv-keccak-spec-lean" {
    nativeBuildInputs = [ pkgs.coreutils ];
  } ''
    actual="$(${pkgs.coreutils}/bin/sha256sum ${scrollFv}/Spec/Keccak/Keccak256.lean | cut -d ' ' -f 1)"
    test "$actual" = "76d306102ccee991f08adca3e1597fc4362ce1e05b0a3cfabb2724927c133885"
    mkdir -p "$out/Spec/Keccak"
    cp ${scrollFv}/Spec/Keccak/Keccak256.lean "$out/Spec/Keccak/Keccak256.lean"
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
    inherit keccakSpecLean rethKeccakElfLean sailRiscvLean;

    keccak-spec-lean = keccakSpecLean;
    reth-keccak-elf-lean = rethKeccakElfLean;
    sail-riscv-lean = sailRiscvLean;
  };

  inherit devShell;
}
