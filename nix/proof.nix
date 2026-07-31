{ etheorem, pkgs, repo, rv64, sailRiscv, targets }:
let
  zesuSsz = targets.public.zesuSsz;
  zesuAbiManifest = targets.public.zesuAbiManifest;
  elflingProgram = targets.public.elflingProgram;

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
  sszSpecLean = pkgs.runCommand "binary-fv-ssz-spec-lean" {
    nativeBuildInputs = [ pkgs.coreutils ];
  } ''
    copy_checked() {
      source="$1"
      expected="$2"
      destination="$3"
      actual="$(${pkgs.coreutils}/bin/sha256sum "$source" | cut -d ' ' -f 1)"
      test "$actual" = "$expected"
      cp "$source" "$destination"
    }

    mkdir -p "$out/SizzLean/Spec" "$out/SszBridge"
    spec_root=${etheorem}/packages/SizzLean/SizzLean/Spec
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
    copy_checked ${repo}/targets/ssz/zesu/spec/SszBridge/Core.lean \
      0b408b5d7a463cf854b57cabfead2f7e521f7384d276f3438b1d49af81049a32 \
      "$out/SszBridge/Core.lean"

    ${pkgs.coreutils}/bin/printf '%s\n' \
      etheorem=032ab6c6d67186ba60b734e0f2c44ba1bb8b6fb0 \
      SizzLean/Spec/Type.lean=ef7fd929a536cf157808cb4ace0255e3992dda566f93b77737166c3fb9139711 \
      SizzLean/Spec/Interp.lean=f23160310811f477fb7c367e6c4c5186d302fe027447a414c25cde9486dfc52b \
      SizzLean/Spec/Constants.lean=8042328b192f32697ce2f9fbda5bd91cb15c746601c4c9c946f96d7e5fb78b96 \
      SizzLean/Spec/SSZError.lean=0e8ddfb73dc7ac7d6a56a2943e950051abd9310b25465e2f415c8a64327c4448 \
      SizzLean/Spec/Serialize.lean=d830cb74ded4cddbba87e4400ebaef71060f527317c5783d9a4fe9d02e7c0ae2 \
      SizzLean/Spec/Deserialize.lean=db05b7d663445dc79e563ef0095482544ff950a7b51fd89e14fcb301b4830ef5 \
      SszBridge/Core.lean=0b408b5d7a463cf854b57cabfead2f7e521f7384d276f3438b1d49af81049a32 \
      > "$out/provenance.txt"
  '';

  binaryFvLean = pkgs.runCommand "binary-fv-lean" {
    nativeBuildInputs = [ pinnedLean pkgs.coreutils pkgs.git pkgs.jq ];
  } ''
    cp -R ${repo} source
    chmod -R u+w source
    cd source

    mkdir -p build .lake/packages/repl "$TMPDIR/home"
    ln -s ${sailRiscvLean} build/sail-riscv-lean
    ln -s ${sszSpecLean} build/ssz-spec-lean
    ln -s ${zesuSszElfLean} build/zesu-ssz-elf-lean
    ln -s ${zesuAbiManifest} build/zesu-abi-lean
    ln -s ${elflingProgram} build/elfling-program-lean
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
    layerViolations=$(grep -rn "^import BinaryFv\.SSZ" BinaryFv/RiscV/ BinaryFv/Binary/ \
      BinaryFv/RiscV.lean BinaryFv/Binary.lean 2>/dev/null || true)
    if [ -n "$layerViolations" ]; then
      echo "Layer violation: the RISC-V/Binary layers must not import the SSZ target." >&2
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

    # Exactly four SSZ scaffolds are authorized. Keep the check declaration-scoped by pinning both
    # the file and the count; all helper proofs remain sorry-free.
    #
    # The four are the two root runner/API bridges in `Zesu/Root.lean` and the two live-trace
    # holes in `Entrypoints/ZesuDecodeRaw/Execution.lean`. The allowlist previously named only
    # `Zesu/Root.lean` and asserted a count of 1 there, which predated the root scaffold being split
    # into two theorems plus two trace obligations — so this audit rejected its own tree. Pinning
    # both files with exact counts is strictly tighter than the previous rule, not looser: the
    # Execution.lean holes were formerly unlisted and are now explicitly bounded.
    sorrySites=$(grep -Rnw --include='*.lean' -e '^[[:space:]]*sorry[[:space:]]*$' BinaryFv/ || true)
    unexpectedSorries=$(printf '%s\n' "$sorrySites" | grep -v -E \
      '^BinaryFv/Zesu/Root\.lean:[0-9]+:.*sorry$|^BinaryFv/Zesu/Entrypoints/ZesuDecodeRaw/Execution\.lean:[0-9]+:.*sorry$' \
      || true)
    if [ -n "$unexpectedSorries" ]; then
      echo "Only the declaration-allowlisted SSZ root scaffolds may contain sorry." >&2
      echo "$unexpectedSorries" >&2
      exit 1
    fi
    test "$(printf '%s\n' "$sorrySites" | grep -c '^BinaryFv/Zesu/Root\.lean:')" = 2
    test "$(printf '%s\n' "$sorrySites" | grep -c '^BinaryFv/Zesu/Entrypoints/ZesuDecodeRaw/Execution\.lean:')" = 2

    lake build repl BinaryFv GeneratedProgram BinaryFv.Binary.ProgramImageTest
    touch "$out"
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
    inherit binaryFvLean sailRiscvLean sszSpecLean zesuSszElfLean;

    binary-fv-lean = binaryFvLean;
    sail-riscv-lean = sailRiscvLean;
    ssz-spec-lean = sszSpecLean;
    zesu-ssz-elf-lean = zesuSszElfLean;
  };

  inherit devShell;
}
