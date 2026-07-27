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
  #
  # The pin also carries upstream's *proofs* about that closure — `Spec/BasicSupported.lean`,
  # `Spec/Supported.lean`, `Spec/MaxByteLength.lean`, and all of `Proofs/`. The exclusion above is
  # about the Lake package's SHA/OpenSSL dependencies, and `Proofs/` has none: its only non-SizzLean
  # imports are `Std.Tactic.BVDecide` and `Lean.Meta.Tactic.Simp.RegisterCommand`. Pinning them is
  # what stops Row D re-deriving `decode_encode` (serialize-then-deserialize is the identity on the
  # `BasicSupported` shapes), `serialize_injective`, and `encode_size_le_max` from scratch. Every
  # file is copied under the same SHA discipline as the spec files and listed in `provenance.txt`,
  # so an upstream edit fails the build rather than silently changing what the proof rests on.
  #
  # Note the trust consequence, which is deliberate and stated rather than discovered later:
  # upstream's multi-byte integer arms are closed with `bv_decide`, so any theorem reached through
  # `decode_encode` carries `Lean.ofReduceBool`/`Lean.trustCompiler`. That is the same axiom class
  # the pinned-artifact `native_decide` facts already put in the root, not a new one.
  sszSpecLean = pkgs.runCommand "binary-fv-ssz-spec-lean" {
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

    mkdir -p "$out/SizzLean/Spec" "$out/SizzLean/Proofs" "$out/SszBridge"
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
    copy_checked "$sizzlean_root/Proofs/Injective.lean" \
      f71f759814cc027455af8ae645c3e99594853470e2ecc4143239f4bd8413e091 \
      "$out/SizzLean/Proofs/Injective.lean"
    copy_checked "$sizzlean_root/Proofs/ListFixed.lean" \
      5912c1ce7e664cf4064d53e6e2a45b4c460b03d436a68f0fad05c6c46753c4f2 \
      "$out/SizzLean/Proofs/ListFixed.lean"
    copy_checked "$sizzlean_root/Proofs/Roundtrip.lean" \
      d3faad1aa57b43b07717a7f564d8ce9a30790b6a5a4ed9092961d323ed810e50 \
      "$out/SizzLean/Proofs/Roundtrip.lean"
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
    # ------------------------------------------------------------------------------------------
    # THE COMPLETE LIST OF EDITS MADE TO PINNED UPSTREAM FILES. Three, in two groups.
    #
    # Kept together deliberately: the divergence from upstream is a property of the pin as a whole,
    # and a reader who has to assemble it from three places in this file will miss one. Every entry
    # is also named in `provenance.txt`, which travels with the artifact.
    #
    # Group 1 — TOOLCHAIN (2 edits). `Proofs/UInt.lean` and `Proofs/BitPack.lean` name
    # `ByteArray.size_push` in `simp only` lists. That lemma exists in upstream's pinned
    # `leanprover/lean4:v4.29.1` and not in this project's nightly, so the two files do not
    # elaborate here — nothing to do with their content. The fix is one lemma, restated in
    # `SizzLean/Compat.lean` below, plus one inserted `import` line in each of those two files.
    #
    # Group 2 — VISIBILITY (1 edit, 2 declarations). `Spec/Deserialize.lean` marks its offset-table
    # walkers `private`: `extractFieldOffsets` (line 135) and `extractCollOffsets` (line 156).
    # Row D's canonicality proofs have to *reduce* through both — `zeroFirstOffsetAliasRejected`
    # needs the zero-count equation of the collection walker, and the oracle half of
    # `forkErrorOrderingDiffers` needs the field walker — and a `private` definition can neither be
    # named nor unfolded from here. The precedent is upstream's own: `Deserialize.lean:169` records
    # that the bit-packing definitions are "Public defs (not `private`) so the Layer 2 bit-packing
    # inverse proof in `Proofs/BitPack.lean` can reach them" — the identical situation one layer up.
    #
    # WHY ALL THREE ARE SAFE, and it is the same argument. None can change what any definition
    # denotes: an added import and a widened visibility are both inert with respect to meaning, so
    # no proof can say something different because of them. The pristine SHA is still checked
    # *before* every edit, so an upstream change still fails the build. What these patches cannot do
    # is hide a change to what the proofs say. Any edit that would alter a definition's *content* is
    # out of scope and stops for the user.
    #
    # The visibility edit is guarded rather than trusted, because a silent no-op sed on a pinned
    # source is exactly the failure that would leave the build green and the proofs unreachable:
    # each declaration is matched by its FULL text and asserted present before the edit and absent
    # after, SEPARATELY so that hitting one declaration twice cannot satisfy both; and the file's
    # `private` count is asserted to go from exactly 10 to exactly 8. Any other number means the
    # file is not what this derivation thinks it is, and the build fails rather than guessing.
    # ------------------------------------------------------------------------------------------
    ${pkgs.coreutils}/bin/cat > "$out/SizzLean/Compat.lean" <<'COMPAT'
/-!
# Toolchain compatibility for the pinned upstream proofs

`ByteArray.size_push` is present in the Lean release `etheorem` pins and absent from the nightly this
project pins. `SizzLean/Proofs/{UInt,BitPack}.lean` name it in `simp only` lists, so it is restated
here and imported by exactly those two files. This module is added by `nix/proof.nix`; it is not
upstream content.
-/

theorem ByteArray.size_push (bytes : ByteArray) (byte : UInt8) :
    (bytes.push byte).size = bytes.size + 1 := by
  cases bytes
  exact Array.size_push ..
COMPAT
    ${pkgs.gnused}/bin/sed -i '1i import SizzLean.Compat' "$out/SizzLean/Proofs/UInt.lean"
    ${pkgs.gnused}/bin/sed -i '1i import SizzLean.Compat' "$out/SizzLean/Proofs/BitPack.lean"

    # Group 2, the visibility widening. See the block above for why it is safe and why it is
    # guarded. `count_private` tolerates a zero match (`grep` exits 1) so the assertion reports the
    # count rather than aborting on the grep itself.
    deserialize="$out/SizzLean/Spec/Deserialize.lean"
    count_private() {
      { ${pkgs.gnugrep}/bin/grep -o 'private' "$1" || true; } | ${pkgs.coreutils}/bin/wc -l
    }
    count_line() {
      { ${pkgs.gnugrep}/bin/grep -c -x -F "$2" "$1" || true; } | ${pkgs.coreutils}/bin/tail -n 1
    }

    # Pre-edit: both declarations present, once each, and the file has exactly ten `private`s.
    test "$(count_line "$deserialize" 'private def extractFieldOffsets (b : ByteArray) :')" = 1
    test "$(count_line "$deserialize" 'private def extractCollOffsets (b : ByteArray) :')" = 1
    test "$(count_private "$deserialize")" = 10

    ${pkgs.gnused}/bin/sed -i \
      's|^private def extractFieldOffsets (b : ByteArray) :$|def extractFieldOffsets (b : ByteArray) :|' \
      "$deserialize"
    ${pkgs.gnused}/bin/sed -i \
      's|^private def extractCollOffsets (b : ByteArray) :$|def extractCollOffsets (b : ByteArray) :|' \
      "$deserialize"

    # Post-edit: each `private` form gone and each public form present, asserted separately so that
    # rewriting one declaration twice cannot pass for rewriting both; then the count is exactly two
    # lower. Ten to eight, and nothing else.
    test "$(count_line "$deserialize" 'private def extractFieldOffsets (b : ByteArray) :')" = 0
    test "$(count_line "$deserialize" 'private def extractCollOffsets (b : ByteArray) :')" = 0
    test "$(count_line "$deserialize" 'def extractFieldOffsets (b : ByteArray) :')" = 1
    test "$(count_line "$deserialize" 'def extractCollOffsets (b : ByteArray) :')" = 1
    test "$(count_private "$deserialize")" = 8

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
      SizzLean/Spec/BasicSupported.lean=5c50a2609d3891ba32016b0dbea3af684e0161ca0960977ebe4e8fecd86719e0 \
      SizzLean/Spec/Supported.lean=50f32f78c5c0190812b480cf4e749fe9462a416da7667e82eb918db46f123bcc \
      SizzLean/Spec/MaxByteLength.lean=95529cf63920db116500d12e8d7cf9e1eab6d0d37f21a714d143d8ab4dbd818d \
      SizzLean/Proofs/BitPack.lean=903cb8a62cac4f8a2444ec8b1ab7d270bb2561f7801f79e3fa0c4bc4cfd91cc5 \
      SizzLean/Proofs/Bool.lean=4f28e9300e5d582a986fc81398dfb1ba289f1e43551f0fba6791953229dafacf \
      SizzLean/Proofs/ContainerFixed.lean=a4cfbbe8e33e9aaf8a2664e7b98a18425b5763b5bc8ee83f352e3c2673cf5f17 \
      SizzLean/Proofs/FixedElems.lean=1173b8b1dc05a9b799872b4e1044e3debb3558e7228ef441367f23a2977f417c \
      SizzLean/Proofs/Injective.lean=f71f759814cc027455af8ae645c3e99594853470e2ecc4143239f4bd8413e091 \
      SizzLean/Proofs/ListFixed.lean=5912c1ce7e664cf4064d53e6e2a45b4c460b03d436a68f0fad05c6c46753c4f2 \
      SizzLean/Proofs/Roundtrip.lean=d3faad1aa57b43b07717a7f564d8ce9a30790b6a5a4ed9092961d323ed810e50 \
      SizzLean/Proofs/SerializeSize.lean=22da51a02f5845b648d1ecf37efa754df8afc42963314318ccf76b221ee1d16f \
      SizzLean/Proofs/Simp.lean=ef266efca1c8730900c4b186383f0b2cac0677e6a608460cc9c670a61f3296e1 \
      SizzLean/Proofs/SimpAttrs.lean=63006416cad34b6e65dc7a60a5cf62765c994e5fd806bb881abcbd62139d72ca \
      SizzLean/Proofs/SizeBound.lean=a45050a4d9fed9c67f5e6da7a131854666e791048bf5e0c58423db16e493d60b \
      SizzLean/Proofs/UInt.lean=629894b6385041763094118c1a16a2383fa4cb3f5af5f6f0f2ae693ef6b0cdae \
      SizzLean/Proofs/VectorFixed.lean=1c7c7e11451beb845705769f2ddb073b87666ee9c01323a336d364f489a5a890 \
      SszBridge/Core.lean=0b408b5d7a463cf854b57cabfead2f7e521f7384d276f3438b1d49af81049a32 \
      > "$out/provenance.txt"

    # The hashes above are the *upstream* provenance claim: what was fetched and verified. Three of
    # the shipped files are not byte-identical to it, so record that here rather than leaving an
    # auditor to hash the tree, find three mismatches, and have nothing in this file to explain
    # them. The dangerous reading is the other one — that the shipped files are pristine when they
    # are not — so the patches are named in the artifact that travels, not only in this derivation.
    {
      ${pkgs.coreutils}/bin/printf '%s\n' \
        'patch=SizzLean/Compat.lean is added by nix/proof.nix and is NOT upstream content' \
        'patch=SizzLean/Proofs/UInt.lean has one inserted first line: import SizzLean.Compat' \
        'patch=SizzLean/Proofs/BitPack.lean has one inserted first line: import SizzLean.Compat' \
        'patch-reason=ByteArray.size_push exists in the Lean release etheorem pins and not in this project pinned nightly' \
        'patch=SizzLean/Spec/Deserialize.lean drops the private modifier on exactly two declarations: extractFieldOffsets (upstream line 135) and extractCollOffsets (upstream line 156)' \
        'patch-reason=Row D canonicality proofs must reduce through both offset-table walkers, and a private definition can neither be named nor unfolded from outside the module' \
        'patch-guard=each declaration matched by full text and asserted present before and absent after, separately; file private count asserted to go from exactly 10 to exactly 8' \
        'patch-scope=visibility only: no definition body, signature or name is altered, so nothing any proof denotes can change'
      for patched in SizzLean/Compat.lean SizzLean/Proofs/UInt.lean SizzLean/Proofs/BitPack.lean \
        SizzLean/Spec/Deserialize.lean; do
        ${pkgs.coreutils}/bin/printf 'as-shipped/%s=%s\n' "$patched" \
          "$(${pkgs.coreutils}/bin/sha256sum "$out/$patched" | cut -d ' ' -f 1)"
      done
    } >> "$out/provenance.txt"
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

    # Exactly two SSZ scaffolds are authorized. Keep the check declaration-scoped by pinning both
    # the file and the count; all helper proofs remain sorry-free.
    #
    # The SSZ two are the live-trace obligations in `Entrypoints/ZesuDecodeRaw/Execution.lean`:
    # producing a complete run of the wrapper from a spec acceptance, and from a spec rejection.
    #
    # `SSZ/Root.lean` is deliberately NOT on this allowlist any more. It used to hold two scaffolds
    # bridging a trace witness to the public API; Row D's runner made that bridge a real proof
    # (`executeDecode_accepted_of_run` / `executeDecode_rejected_of_run`), so the root now derives
    # its two lemmas and contains no `sorry` at all. Dropping the file from the allowlist rather than
    # setting its count to zero is the stricter choice: a future `sorry` there fails as *unexpected*
    # instead of silently fitting under a budget.
    sorrySites=$(grep -Rnw --include='*.lean' -e '^[[:space:]]*sorry[[:space:]]*$' BinaryFv/ || true)
    unexpectedSorries=$(printf '%s\n' "$sorrySites" | grep -v -E \
      '^BinaryFv/SSZ/Zesu/Entrypoints/ZesuDecodeRaw/Execution\.lean:[0-9]+:.*sorry$' \
      || true)
    if [ -n "$unexpectedSorries" ]; then
      echo "Only the declaration-allowlisted SSZ live-trace scaffolds may contain sorry." >&2
      echo "$unexpectedSorries" >&2
      exit 1
    fi
    test "$(printf '%s\n' "$sorrySites" | grep -c '^BinaryFv/SSZ/Zesu/Entrypoints/ZesuDecodeRaw/Execution\.lean:')" = 2

    # Validation-import guard. The Row B `Validation/` modules are falsification evidence, never proof
    # premises: no file OUTSIDE `Validation/` may import one, so no root theorem (nor the `BinaryFv`
    # umbrella) can transitively depend on the probe's meaning-agreement checks. The Validation modules
    # still build below (reusing this toolchain), but nothing in the theorem graph imports them.
    validationLeaks=$(grep -rn --include='*.lean' "^import BinaryFv\..*\.Validation\." BinaryFv/ 2>/dev/null \
      | grep -v "^BinaryFv/SSZ/Zesu/Validation/" || true)
    if [ -n "$validationLeaks" ]; then
      echo "Validation-import guard: no proof module may import a Validation module." >&2
      echo "$validationLeaks" >&2
      exit 1
    fi

    lake build repl BinaryFv GeneratedProgram BinaryFv.Binary.ProgramImageTest

    # Row B validation, co-located ONLY to reuse this derivation's fully-built toolchain (the module
    # imports the Sail-entangled contracts chain, so a standalone check would rebuild the whole tree).
    # It is NOT part of the theorem graph — the audits above enforce that the root theorems never
    # import `Validation`. Building it forces the kernel-checked (`native_decide`) agreement of the
    # handwritten `meaningDecode` with both the pinned oracle and the corpus expectation; any
    # disagreement fails the build. This is falsification evidence, never a proof premise.
    lake build BinaryFv.SSZ.Zesu.Validation.MeaningAgreement
    # Per-routine meaning agreement (Row B item 3): native_decide that each typed leaf vector's
    # handwritten meaning equals its expected value/error — the Lean side of the probe's
    # `--routine-vectors` check. Also outside the theorem graph.
    lake build BinaryFv.SSZ.Zesu.Validation.RoutineMeaningVectors
    # Row C diagnostic checker: native_decide that, for the decodeOptionalBlobSchedule function instance, the
    # Lean checker reproduces the Python oracle on the present/absent/malformed production-ELF evidence,
    # the present arm is a GO, the actual loaded slice decodes to the recorded fields under
    # meaningOptionalBlobSchedule, and each of the eight evidence corruptions flips a check. Also outside
    # the theorem graph (the validation-import guard above forbids any proof module from importing it).
    lake build BinaryFv.SSZ.Zesu.Validation.BinaryFunctionInstanceCheck
    # Row C SCALED checker: native_decide that, for EVERY function instance in program.json, the Lean checker
    # reproduces the Python oracle (`checker_agrees_with_oracle`) on the production-ELF evidence; that the
    # six structural/effect gating checks pass on every covered function instance (`gating_checks_hold`); that no
    # check ever fails — results are pass or explicit gap (`no_gating_failures`); that every function instance's
    # generated entry predicate is SATISFIED by its captured entry state, including the eight loop-derived
    # withdrawal offsets (`entry_predicates_satisfiable_on_captured_states`, `derived_rows_hold`); that
    # each arm's whole-run allocation ledger and every allocating function instance's slice of it are exactly the
    # sequence the fixture requires (`arm_ledgers_hold`, `allocating_function_instances_match_expected_ledger`);
    # and that mutating the sampled evidence — a derived row's index/stride/constant/register, or the
    # ledger's event count, order, size, alignment or returned block — flips the responsible check.
    # Coverage is per function instance, gaps explicit.
    # Also outside the theorem graph (validation-import guard forbids any proof module from importing it).
    lake build BinaryFv.SSZ.Zesu.Validation.ScaleFunctionInstanceCheck
    # Row D executable runner: native_decide that RUNNING the pinned binary in the Sail model — entry
    # state, steps to the return sentinel, both exported accessors, and the full value observation —
    # gives the same answer as the SSZ oracle on every corpus case, field for field on the accepted
    # ones (`runner_agrees_with_spec`); and that the failure modes stay apart under real execution: a
    # short budget is fuel exhaustion, a misplaced observer is a malformed result, and a refused
    # SECOND call — which returns 0 with `alreadyDecoded`, exactly as a rejection returns 0 — is a bad
    # return, never a rejection. This is the executable-test item of D2; the bad-artifact and
    # oversized-input cases are proved universally in `Runner.lean` instead of sampled here.
    # Also outside the theorem graph (validation-import guard forbids any proof module from importing it).
    lake build BinaryFv.SSZ.Zesu.Validation.RunnerExecution
    # Row D observer sensitivity: the correspondence proof shows the observer reads back what the
    # representation says is there, but not that it LOOKS at every field — an observer ignoring
    # `parentHash` would still satisfy it. So this corrupts one byte per layout family (fixed field,
    # optional tag/payload, slice pointer/length, list count/base, nested base) in the memory a real
    # accepted decode left behind, and checks each corruption moves the observation. The control is
    # the payload of an ABSENT optional, which must NOT move it — that is what the representation
    # promises about it, and it proves the checks detect real dependence rather than noise.
    # Also outside the theorem graph (validation-import guard forbids any proof module from importing it).
    lake build BinaryFv.SSZ.Zesu.Validation.ObserverMutation
    touch "$out"
  '';

  # Row B oracle runner, built standalone. The runner root `ContractRunner` imports only the Sail-free
  # `SszBridge.Core`, so `lake build ssz_contract_runner` compiles just that small closure on top of
  # the (cached) prebuilt spec libs — it does NOT rebuild the theorem tree, and it never carries a
  # theorem as a premise. The prebuilt libs are linked only to satisfy lake's whole-file config eval.
  sszContractRunner = pkgs.runCommand "ssz-contract-runner" {
    nativeBuildInputs = [ pinnedLean pkgs.coreutils pkgs.git pkgs.jq pkgs.patchelf ];
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
    lake build ssz_contract_runner
    mkdir -p "$out/bin"
    cp .lake/build/bin/ssz_contract_runner "$out/bin/ssz_contract_runner"

    # lake links the exe against the host dynamic linker (`/lib64/ld-linux-x86-64.so.2`), which is
    # absent from a Nix build sandbox, so any derivation that *runs* the runner (the agreement check)
    # would get ENOENT on exec. It is statically linked against Lean and needs only glibc, so repoint
    # the interpreter and rpath at the pinned glibc to make it runnable in a pure sandbox.
    patchelf \
      --set-interpreter "${pkgs.glibc}/lib/ld-linux-x86-64.so.2" \
      --set-rpath "${pkgs.glibc}/lib" \
      "$out/bin/ssz_contract_runner"
  '';

  # Row B full differential in CI: the pinned oracle runner and the host source probe must both agree
  # with the corpus expectation, and with each other, on ALL 49 cases — including the ~1 MiB collision
  # fixtures that `native_decide` omits. This closes the oracle-side residual that the kernel check
  # leaves open on the large cases (see DECISIONS.md); the value fidelity of those cases stays covered
  # by the preserved three-way `ssz-value-v1` audit.
  sszContractAgreement = pkgs.runCommand "ssz-contract-agreement" {
    nativeBuildInputs = [ pkgs.python3 pkgs.coreutils ];
  } ''
    set -euo pipefail
    mkdir -p "$out"
    python3 ${repo}/targets/ssz/zesu/tests/ssz_contract_agreement.py \
      --corpus-generator ${repo}/targets/ssz/zesu/tests/ssz_contract_corpus.py \
      --fixtures ${repo}/targets/ssz/zesu/tests/ssz_differential_audit.py \
      --lean-runner ${sszContractRunner}/bin/ssz_contract_runner \
      --zesu-probe ${targets.public.zesuContractProbe}/bin/ssz-contract-probe \
      --corpus-out "$out/corpus.jsonl" | tee "$out/agreement.txt"
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
    inherit binaryFvLean sailRiscvLean sszSpecLean zesuSszElfLean
      sszContractRunner sszContractAgreement;

    binary-fv-lean = binaryFvLean;
    sail-riscv-lean = sailRiscvLean;
    ssz-spec-lean = sszSpecLean;
    zesu-ssz-elf-lean = zesuSszElfLean;
    ssz-contract-runner = sszContractRunner;
    ssz-contract-agreement = sszContractAgreement;
  };

  inherit devShell;
}
