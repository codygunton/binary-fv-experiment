{ pkgs
, source
, repo
, zesu
, zesuRepaired
, rv64
}:
let
  inherit (rv64)
    cflags
    lib
    qemuRiscv64
    riscvBinutils
    riscvCc
    riscvNm
    riscvObjdump
    riscvPkgs
    riscvReadelf;

  zesuProductionRevision = "aa6c94339987d278acb8b7fa409c864dbd3d05aa";
  zesuRepairedRevision = "96f1621468ba54755d653f19cbc9704e789be001";

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
      printf '%s\n' "zesu=Consensys/zesu@${zesuProductionRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  zesuRawObject = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-raw-ssz-rv64im-object";
    version = "96f1621";
    src = zesuRepaired;
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
      printf '%s\n' "zesu=codygunton/zesu@${zesuRepairedRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  # DWARF sidecar for the raw-SSZ objects. Identical to `zesuRawObject` in pinned source, Zig
  # compiler, target, code model, and optimization, changing only `.strip = false` on the three
  # object root modules so debug information is retained (`ReleaseSmall` strips by default). The
  # equivalence gate below proves the sidecar is the *same compilation* as the canonical object —
  # every allocatable section byte-identical, matching RISC-V ISA attributes, relocations, and
  # symbols, and the decoder `.text` pinned to its SHA-256 — so the sidecar's DWARF validly
  # describes the canonical bytes. A wrong sidecar can only fail this build, never establish a false
  # source mapping. The DWARF is untrusted until this derivation succeeds.
  zesuRawSidecar = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-raw-ssz-rv64im-sidecar";
    version = "96f1621";
    src = zesuRepaired;
    nativeBuildInputs = [
      pkgs.zig
      riscvBinutils
      pkgs.coreutils
      pkgs.diffutils
      pkgs.gawk
      pkgs.gnused
      pkgs.gnugrep
    ];
    dontConfigure = true;
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"

      # Retain DWARF by disabling strip on exactly the three raw-SSZ object root modules; nothing
      # else changes. `--replace-fail` makes source drift a build error rather than a silent no-op.
      substituteInPlace build.zig \
        --replace-fail '.root_source_file = b.path("src/zkvm/raw_allocator.zig"),' \
          '.root_source_file = b.path("src/zkvm/raw_allocator.zig"), .strip = false,'
      substituteInPlace build.zig \
        --replace-fail '.root_source_file = b.path("src/zkvm/raw_decoder_root.zig"),' \
          '.root_source_file = b.path("src/zkvm/raw_decoder_root.zig"), .strip = false,'
      substituteInPlace build.zig \
        --replace-fail '.root_source_file = b.path("src/zkvm/raw_sink.zig"),' \
          '.root_source_file = b.path("src/zkvm/raw_sink.zig"), .strip = false,'

      zig build rv64im-raw-ssz-object -Doptimize=ReleaseSmall
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p "$out/obj" "$out/meta"
      cp zig-out/lib/zesu_raw_ssz_allocator.o "$out/obj/zesu-raw-ssz-allocator.o"
      cp zig-out/lib/zesu_raw_ssz.o           "$out/obj/zesu-raw-ssz-decoder.o"
      cp zig-out/lib/zesu_raw_ssz_sink.o      "$out/obj/zesu-raw-ssz-sink.o"

      export READELF=${riscvReadelf}
      export EXPECT_TEXT_SHA=f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b
      bash ${repo}/targets/ssz/zesu/tests/sidecar_equivalence.sh \
        ${zesuRawObject}/obj "$out/obj" | tee "$out/meta/equivalence.txt"

      printf '%s\n' "zesu=codygunton/zesu@${zesuRepairedRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      printf '%s\n' "decoder-text-sha256=f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b" \
        >> "$out/meta/provenance.txt"
      ${riscvReadelf} -SW "$out/obj/zesu-raw-ssz-decoder.o" > "$out/meta/decoder-sections.txt"
      runHook postInstall
    '';
  };

  # DWARF sidecar for the C runtime object (`memcpy`/`memmove`, plus `memset`/`memcmp`). The canonical
  # runtime is compiled `-g0` (stripped); this compiles the SAME source with the SAME `riscvCc` and
  # cflags, only appending `-g` (which overrides the earlier `-g0`), and enforces that every emitted
  # `.text.*` function-section is byte-identical to the stripped compile — so `-g` added only DWARF
  # and changed no codegen. Symbols must never define a proof region: the runtime routines' regions
  # come from these DWARF subprogram ranges, not from the symbols' (value,size). If `-g` ever changes
  # the runtime `.text`, this derivation FAILS rather than silently substituting a symbol-boundary
  # region — a documented exception would then be a deliberate, reviewed decision.
  zesuRuntimeSidecar = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-runtime-sidecar";
    version = "96f1621";
    dontUnpack = true;
    dontConfigure = true;
    dontFixup = true;
    hardeningDisable = [ "all" ];
    nativeBuildInputs = [
      riscvPkgs.stdenv.cc
      riscvBinutils
      pkgs.zig
      pkgs.coreutils
      pkgs.diffutils
      pkgs.gnugrep
    ];

    buildPhase = ''
      runHook preBuild
      export NIX_HARDENING_ENABLE=""
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      ${riscvCc} ${cflags} -c ${repo}/targets/common/riscv64_runtime.c -o canonical.o
      ${riscvCc} ${cflags} -g -c ${repo}/targets/common/riscv64_runtime.c -o sidecar.o
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p "$out/obj" "$out/meta"

      ${riscvReadelf} -SW sidecar.o | grep -q '\.debug_info' \
        || { echo "RUNTIME SIDECAR FAILURE: no DWARF in -g runtime object" >&2; exit 1; }
      if ${riscvReadelf} -SW canonical.o | grep -q '\.debug_info'; then
        echo "RUNTIME SIDECAR FAILURE: canonical (-g0) runtime unexpectedly carries DWARF" >&2; exit 1
      fi

      for S in .text.memcpy .text.memmove .text.memset .text.memcmp; do
        zig objcopy -O binary --only-section="$S" canonical.o "c$S.bin"
        zig objcopy -O binary --only-section="$S" sidecar.o  "s$S.bin"
        cmp -s "c$S.bin" "s$S.bin" \
          || { echo "RUNTIME SIDECAR FAILURE: $S bytes differ — -g changed codegen; STOP (do not fall back to symbol-boundary regions)" >&2; exit 1; }
        # The sidecar must describe the EXACT runtime object linked into the canonical ELF, not merely
        # another fresh compile: compare against ${zesuSsz}/obj/riscv64_runtime.o, the actual link
        # input, closing the "compared only with a fresh compile" gap (review blocker #5).
        zig objcopy -O binary --only-section="$S" ${zesuSsz}/obj/riscv64_runtime.o "l$S.bin"
        cmp -s "s$S.bin" "l$S.bin" \
          || { echo "RUNTIME SIDECAR FAILURE: $S differs from the canonical link input (zesuSsz runtime object); STOP" >&2; exit 1; }
      done

      cp sidecar.o "$out/obj/riscv64_runtime.o"
      ${riscvReadelf} -SW  "$out/obj/riscv64_runtime.o" > "$out/meta/runtime-sections.txt"
      ${riscvReadelf} -sW  "$out/obj/riscv64_runtime.o" | grep -E 'memcpy|memmove' > "$out/meta/runtime-symbols.txt"
      printf 'runtime=targets/common/riscv64_runtime.c\n' > "$out/meta/provenance.txt"
      printf 'gcc=%s\n' "$(${riscvCc} --version | head -1)" >> "$out/meta/provenance.txt"
      echo "OK: -g runtime .text.{memcpy,memmove,memset,memcmp} byte-identical to canonical AND to the zesuSsz link input; DWARF retained" \
        | tee "$out/meta/equivalence.txt"
      runHook postInstall
    '';
  };

  # Deterministic ELF/DWARF/CFG -> Elfling Program generator (milestone 4). Reads the validated DWARF
  # sidecars, maps to canonical PCs, resolves readArray widths from DWARF call_line -> pinned source,
  # matches occurrences to the live catalog, folds glue into the nearest cataloged ancestor, and emits
  # deterministic JSON, a generated Lean `Program`, and a Markdown source/function/CFG index.
  #
  # Filtered inputs: only the generator script (via builtins.path, not the whole repo), the validated
  # sidecars, and the pinned source — so editing handwritten proofs never rebuilds it. Determinism is
  # an acceptance criterion: it runs twice and FAILS unless every artifact is byte-identical.
  elflingGeneratorScript = builtins.path {
    path = repo + "/tools/generate_elfling_program.py";
    name = "generate_elfling_program.py";
  };
  elflingProgram = pkgs.runCommand "elfling-program" {
    nativeBuildInputs = [ pkgs.python3 pkgs.coreutils pkgs.diffutils ];
  } ''
    gen() {
      python3 ${elflingGeneratorScript} \
        --readelf ${riscvReadelf} \
        --decoder ${zesuRawSidecar}/obj/zesu-raw-ssz-decoder.o \
        --allocator ${zesuRawSidecar}/obj/zesu-raw-ssz-allocator.o \
        --sink ${zesuRawSidecar}/obj/zesu-raw-ssz-sink.o \
        --runtime ${zesuRuntimeSidecar}/obj/riscv64_runtime.o \
        --source ${zesuRepaired} \
        --runtime-c ${builtins.path { path = repo + "/targets/common/riscv64_runtime.c"; name = "riscv64_runtime.c"; }} \
        --map ${zesuSsz}/meta/zesu-ssz.map \
        --elf ${zesuSsz}/bin/zesu-ssz \
        --objdump ${riscvObjdump} \
        --out-json "$1/program.json" \
        --out-lean "$1/GeneratedProgram.lean" \
        --out-md "$1/program.md" \
        --out-globals "$1/DecoderGlobals.lean"
    }
    mkdir -p run1 run2 "$out"
    gen run1
    gen run2
    for f in program.json GeneratedProgram.lean program.md DecoderGlobals.lean; do
      cmp -s "run1/$f" "run2/$f" \
        || { echo "GENERATOR NON-DETERMINISTIC: $f differs between two runs" >&2; exit 1; }
    done
    cp run1/program.json run1/GeneratedProgram.lean run1/program.md run1/DecoderGlobals.lean "$out/"
    printf '%s\n' "two independent runs produced byte-identical program.json/GeneratedProgram.lean/program.md/DecoderGlobals.lean" \
      > "$out/determinism.txt"
  '';

  # Deterministic DWARF -> Lean extractor for the `decodeOptionalBlobSchedule` vertical slice
  # (milestone 3). Reads the validated decoder DWARF sidecar with the pinned LLVM 21.1.8
  # `llvm-dwarfdump`, finds the single inline instance, its inline call stack and nested `readU64`
  # field reads, maps object-relative DWARF ranges to canonical-ELF PCs, and emits the committed
  # `BlobScheduleInstance.lean` verbatim.
  #
  # Filtered inputs: only the extractor script (via builtins.path, not the whole repo) and the
  # validated sidecar — so editing handwritten proofs never rebuilds it. Determinism is an
  # acceptance criterion: it runs twice and FAILS unless byte-identical, then a drift guard FAILS
  # unless the regenerated file equals the committed `BlobScheduleInstance.lean` (the analog of how
  # the decoder `.text` sha256 is reproduced AND enforced).
  blobScheduleExtractorScript = builtins.path {
    path = repo + "/tools/extract_blob_schedule_instance.py";
    name = "extract_blob_schedule_instance.py";
  };
  blobScheduleCommitted = builtins.path {
    path = repo + "/BinaryFv/SSZ/Zesu/Elfling/BlobScheduleInstance.lean";
    name = "BlobScheduleInstance.lean";
  };
  blobScheduleInstance = pkgs.runCommand "blob-schedule-instance" {
    nativeBuildInputs = [ pkgs.python3 pkgs.coreutils pkgs.diffutils ];
  } ''
    gen() {
      python3 ${blobScheduleExtractorScript} \
        ${zesuRawSidecar}/obj/zesu-raw-ssz-decoder.o \
        --dwarfdump ${pkgs.llvm}/bin/llvm-dwarfdump \
        --lean --out-lean "$1/BlobScheduleInstance.lean"
    }
    mkdir -p run1 run2 "$out"
    gen run1
    gen run2
    cmp -s run1/BlobScheduleInstance.lean run2/BlobScheduleInstance.lean \
      || { echo "BLOB-SCHEDULE EXTRACTOR NON-DETERMINISTIC: BlobScheduleInstance.lean differs between two runs" >&2; exit 1; }
    cmp -s run1/BlobScheduleInstance.lean ${blobScheduleCommitted} \
      || { echo "BLOB-SCHEDULE DRIFT: regenerated BlobScheduleInstance.lean differs from committed BinaryFv/SSZ/Zesu/Elfling/BlobScheduleInstance.lean" >&2; exit 1; }
    cp run1/BlobScheduleInstance.lean "$out/"
    printf '%s\n' "two independent runs produced byte-identical BlobScheduleInstance.lean; regenerated == committed" \
      > "$out/determinism.txt"
  '';

  # Audit-only optimized LLVM IR for the decoder (plan: "optimized LLVM IR for inspection only, never
  # as proof input"). Emitted through the pinned build.zig module graph (so imports resolve) by adding
  # `getEmittedLlvmIr()` to the raw-ssz-object step, at the SAME target/optimize as the canonical
  # object. Built twice and required byte-identical. It is never consumed by any Lean module.
  elflingDecoderLlvmIr = pkgs.stdenvNoCC.mkDerivation {
    pname = "elfling-decoder-llvm-ir";
    version = "96f1621";
    src = zesuRepaired;
    nativeBuildInputs = [ pkgs.zig pkgs.coreutils pkgs.diffutils ];
    dontConfigure = true;
    dontFixup = true;
    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      substituteInPlace build.zig \
        --replace-fail 'raw_objects_step.dependOn(&install_decoder.step);' \
          'raw_objects_step.dependOn(&install_decoder.step); raw_objects_step.dependOn(&b.addInstallFile(raw_decoder_object.getEmittedLlvmIr(), "lib/zesu_raw_ssz.ll").step);'
      zig build rv64im-raw-ssz-object -Doptimize=ReleaseSmall
      cp zig-out/lib/zesu_raw_ssz.ll run1.ll
      rm -rf zig-out "$ZIG_LOCAL_CACHE_DIR"
      zig build rv64im-raw-ssz-object -Doptimize=ReleaseSmall
      cp zig-out/lib/zesu_raw_ssz.ll run2.ll
      cmp -s run1.ll run2.ll \
        || { echo "DECODER LLVM IR NON-DETERMINISTIC between two builds" >&2; exit 1; }
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p "$out"
      cp run1.ll "$out/decoder.ll"
      printf '%s\n' "audit-only optimized LLVM IR for src/zkvm/raw_decoder_root.zig (rv64im_zicclsm, ReleaseSmall); never a proof input; two builds byte-identical" > "$out/README.txt"
      runHook postInstall
    '';
  };

  # Relocation acceptance test (plan "Verification and Acceptance"): relink the SAME pinned objects at
  # a DIFFERENT text base, regenerate the Elfling program from the SAME sidecars/source but the new
  # linker map, and require that every address-free identity (FunctionId, inline stack, nesting,
  # validated source hash, DWARF entry offset, catalog/excluded class) is byte-stable while every
  # generated address shifts by one constant nonzero delta. This is what proves the extractor holds no
  # hardcoded linked address and folds none into an identity — the handwritten contracts, keyed by
  # `FunctionId`, need no edit when the binary is relinked.
  elflingRelocationCheck = pkgs.runCommand "elfling-relocation-check" {
    nativeBuildInputs = [ pkgs.python3 riscvBinutils riscvPkgs.stdenv.cc pkgs.coreutils ];
  } ''
    mkdir -p reloc "$out"
    # Relink at text-segment base 0x400000 (canonical is 0x10000); the whole text segment shifts.
    ${riscvCc} ${cflags} -nostdlib -static -no-pie \
      ${zesuSsz}/obj/riscv64_start.o \
      ${zesuSsz}/obj/zesu-ssz-main.o \
      ${zesuSsz}/obj/zesu-raw-ssz-allocator.o \
      ${zesuSsz}/obj/zesu-raw-ssz-decoder.o \
      ${zesuSsz}/obj/zesu-raw-ssz-sink.o \
      ${zesuSsz}/obj/riscv64_runtime.o \
      -lgcc -Wl,--gc-sections -Wl,-e,_start \
      -Wl,-Ttext-segment=0x400000 \
      -Wl,-Map,reloc/zesu-ssz.map \
      -o reloc/zesu-ssz.elf

    python3 ${elflingGeneratorScript} \
      --readelf ${riscvReadelf} \
      --decoder ${zesuRawSidecar}/obj/zesu-raw-ssz-decoder.o \
      --allocator ${zesuRawSidecar}/obj/zesu-raw-ssz-allocator.o \
      --sink ${zesuRawSidecar}/obj/zesu-raw-ssz-sink.o \
      --runtime ${zesuRuntimeSidecar}/obj/riscv64_runtime.o \
      --source ${zesuRepaired} \
      --runtime-c ${builtins.path { path = repo + "/targets/common/riscv64_runtime.c"; name = "riscv64_runtime.c"; }} \
      --map reloc/zesu-ssz.map \
      --elf reloc/zesu-ssz.elf \
      --objdump ${riscvObjdump} \
      --out-json reloc/program.json

    python3 ${builtins.path { path = repo + "/targets/ssz/zesu/tests/relocation_stability.py"; name = "relocation_stability.py"; }} \
      --canonical ${elflingProgram}/program.json \
      --relocated reloc/program.json | tee "$out/relocation.txt"
  '';

  # Negative tests for the generator's defect surfacing (review blocker #1): each shows a defect is
  # surfaced and FAILS generation, never silently dropped (unmapped region, ambiguous readArray width,
  # sibling PC overlap), and that the real program is defect-free. Runs against the real sidecars.
  elflingGeneratorDefectsCheck = pkgs.runCommand "elfling-generator-defects-check" {
    nativeBuildInputs = [ pkgs.python3 pkgs.coreutils ];
  } ''
    mkdir -p "$out"
    python3 ${builtins.path { path = repo + "/targets/ssz/zesu/tests/generator_defects_test.py"; name = "generator_defects_test.py"; }} \
      --generator ${elflingGeneratorScript} \
      --readelf ${riscvReadelf} \
      --decoder ${zesuRawSidecar}/obj/zesu-raw-ssz-decoder.o \
      --allocator ${zesuRawSidecar}/obj/zesu-raw-ssz-allocator.o \
      --sink ${zesuRawSidecar}/obj/zesu-raw-ssz-sink.o \
      --runtime ${zesuRuntimeSidecar}/obj/riscv64_runtime.o \
      --source ${zesuRepaired} \
      --runtime-c ${builtins.path { path = repo + "/targets/common/riscv64_runtime.c"; name = "riscv64_runtime.c"; }} \
      --map ${zesuSsz}/meta/zesu-ssz.map \
      --elf ${zesuSsz}/bin/zesu-ssz \
      --objdump ${riscvObjdump} | tee "$out/defects.txt"
  '';

  # Row B: the `ssz-contract-corpus-v1` contract-validation corpus is deterministic. Two independent
  # generator runs over the pinned strict-V4 fixtures must be byte-identical. This is
  # falsification/regression evidence, never a proof input.
  sszContractCorpus = pkgs.runCommand "ssz-contract-corpus" {
    nativeBuildInputs = [ pkgs.python3 pkgs.coreutils pkgs.diffutils ];
  } ''
    mkdir -p "$out"
    gen() {
      python3 ${builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_contract_corpus.py"; name = "ssz_contract_corpus.py"; }} \
        --fixtures ${builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_differential_audit.py"; name = "ssz_differential_audit.py"; }} \
        --out "$1"
    }
    gen run1.jsonl
    gen run2.jsonl
    cmp -s run1.jsonl run2.jsonl \
      || { echo "CORPUS NON-DETERMINISTIC: contract corpus differs between two runs" >&2; exit 1; }
    cp run1.jsonl "$out/corpus.jsonl"
    printf 'cases=%s (byte-identical across two runs)\n' "$(wc -l < run1.jsonl)" | tee "$out/summary.txt"
  '';

  # Evaluate the exact pinned Zig compiler's RV64 layout query. `@compileLog` deliberately fails
  # compilation after reporting the values, so this derivation turns that compiler output into the
  # Lean data module consumed by the proof while preserving the raw compiler transcript as evidence.
  zesuAbiManifest = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-raw-ssz-rv64-abi-manifest";
    version = "96f1621";
    src = zesuRepaired;
    nativeBuildInputs = [ pkgs.gawk pkgs.zig ];
    dontConfigure = true;
    dontFixup = true;

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
      set +e
      zig build-obj -target riscv64-linux-musl --dep ssz_raw \
        -Mroot=${repo}/targets/ssz/zesu/abi_manifest.zig \
        -Mssz_raw=$PWD/src/stateless/stateless/ssz_raw.zig > abi.log 2>&1
      status=$?
      set -e
      test "$status" != 0
      grep -F 'Compile Log Output:' abi.log
      grep -F '@as(*const' abi.log
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p "$out"
      cp abi.log "$out/abi-manifest.log"
      {
        printf '%s\n' 'namespace ZesuSszAbi'
        printf '%s\n' '/-- Generated from the pinned Zig compiler targeting riscv64-linux-musl. -/'
        printf '%s\n' 'def manifest : Array (String × Nat) := #['
        ${pkgs.gawk}/bin/awk '
          /@as\(\*const/ {
            if (match($0, /"[^"]+"/)) {
              key = substr($0, RSTART + 1, RLENGTH - 2)
              if (match($0, /comptime_int, [0-9]+/)) {
                value = substr($0, RSTART + 14, RLENGTH - 14)
                printf "  (\"%s\", %s),\n", key, value
              }
            }
          }
        ' abi.log
        printf '%s\n' ']'
        printf '%s\n' 'end ZesuSszAbi'
      } > "$out/ZesuSszAbi.lean"
      runHook postInstall
    '';
  };

  # Host-only full-value formatter used by the strict three-way SSZ gate.
  # It imports only the lossless raw decoder and is never linked into the
  # RV64 parser/sink measurement composition.
  zesuValue = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-value";
    version = "96f1621";
    src = zesuRepaired;
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
      printf '%s\n' "zesu=codygunton/zesu@${zesuRepairedRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  # Row B host contract probe: a ReleaseSafe host executable that imports the pinned `ssz_raw` module
  # and tests the decoder over the shared contract corpus. Item 1: it reaches the *file-private*
  # catalog routines through a VALIDATION-ONLY OVERLAY — `overlay_exports.zig` is appended to a
  # sha256-verified copy of the pinned `ssz_raw.zig` (verified BEFORE the append; the copy lives only
  # inside this derivation's build tree, so no production object derivation is affected). It emits the
  # canonical decision plus an allocation ledger and validates out-of-memory safety. Host-only; never
  # linked into the RV64 graph.
  zesuContractProbe = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-contract-probe";
    version = "96f1621";
    src = zesuRepaired;
    nativeBuildInputs = [ pkgs.zig ];
    dontConfigure = true;
    dontFixup = true;

    # The exact pinned sha256 of each overlaid source file (the source manifest entries). Each overlay
    # is applied only after its hash matches, so a drifted source fails the build rather than silently
    # exposing a different routine set. raw_allocator/raw_decoder_root are Zesu sources; riscv64_runtime
    # is the repo's freestanding RV64 C runtime (memcpy/memmove).
    ssz_raw_sha256 = "ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131";
    raw_allocator_sha256 = "c9e9457e45a3827729adb1921e07ba31997a536dc8f719e04d2d0d6f4c742591";
    raw_decoder_root_sha256 = "53afe7a5c7c70122a3e2a9f9673a3415a50579a2ed11a21d9dd1c839e0c18a5e";
    riscv64_runtime_sha256 = "5f80e272e96ccb30ca109bb77c9a78c9769bfd6b54ac2d7f712d3c2deb9b8235";

    buildPhase = ''
      runHook preBuild
      export HOME="$TMPDIR"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
      export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"

      # --- validation-only overlays: verify each pinned source, then append private-routine re-exports.
      overlay=src/stateless/stateless/ssz_raw.zig
      echo "$ssz_raw_sha256  $overlay" | sha256sum -c - \
        || { echo "OVERLAY: pinned ssz_raw.zig sha256 mismatch (source drifted)" >&2; exit 1; }
      for fn in decodeNewPayloadRequest decodeExecutionPayload decodeExecutionRequests \
                decodeExecutionWitness decodeChainConfig decodeForkConfig decodeForkActivation \
                decodeOptionalU64 decodeOptionalBlobSchedule decodeVersionedHashes decodeWithdrawals \
                decodeDepositRequests decodeWithdrawalRequests decodeConsolidationRequests \
                decodePublicKeys decodeByteListList requireCanonicalOffsets requireU32Length \
                readOffset readU32 readU64 readU256 readArray bytesAt hasExactErePrefix; do
        grep -qE "^fn $fn\b" "$overlay" \
          || { echo "OVERLAY: private catalog routine 'fn $fn' not found in pinned source" >&2; exit 1; }
      done
      cat ${builtins.path { path = repo + "/targets/ssz/zesu/probe/overlay_exports.zig"; name = "overlay_exports.zig"; }} >> "$overlay"

      alloc_overlay=src/zkvm/raw_allocator.zig
      echo "$raw_allocator_sha256  $alloc_overlay" | sha256sum -c - \
        || { echo "OVERLAY: pinned raw_allocator.zig sha256 mismatch (source drifted)" >&2; exit 1; }
      grep -qE "^pub export fn zesu_raw_alloc\b" "$alloc_overlay" \
        || { echo "OVERLAY: zesu_raw_alloc not found in pinned raw_allocator.zig" >&2; exit 1; }
      cat ${builtins.path { path = repo + "/targets/ssz/zesu/probe/overlay_exports_allocator.zig"; name = "overlay_exports_allocator.zig"; }} >> "$alloc_overlay"

      root_overlay=src/zkvm/raw_decoder_root.zig
      echo "$raw_decoder_root_sha256  $root_overlay" | sha256sum -c - \
        || { echo "OVERLAY: pinned raw_decoder_root.zig sha256 mismatch (source drifted)" >&2; exit 1; }
      for fn in allocatorAlloc allocatorResize allocatorRemap allocatorFree allocator; do
        grep -qE "^fn $fn\b|^fn $fn\(" "$root_overlay" \
          || { echo "OVERLAY: private routine 'fn $fn' not found in pinned raw_decoder_root.zig" >&2; exit 1; }
      done
      cat ${builtins.path { path = repo + "/targets/ssz/zesu/probe/overlay_exports_root.zig"; name = "overlay_exports_root.zig"; }} >> "$root_overlay"

      # The freestanding RV64 C runtime (memcpy/memmove) is verified, then compiled to a linked object.
      runtime_c=${builtins.path { path = repo + "/targets/common/riscv64_runtime.c"; name = "riscv64_runtime.c"; }}
      echo "$riscv64_runtime_sha256  $runtime_c" | sha256sum -c - \
        || { echo "OVERLAY: pinned riscv64_runtime.c sha256 mismatch (source drifted)" >&2; exit 1; }
      zig cc -c "$runtime_c" -o runtime.o -O2

      zig build-exe -O ReleaseSafe \
        --dep ssz_raw --dep raw_allocator --dep raw_decoder_root \
        -Mroot=${builtins.path { path = repo + "/targets/ssz/zesu/probe/ssz_contract_probe.zig"; name = "ssz_contract_probe.zig"; }} \
        -Mssz_raw=$PWD/$overlay \
        -Mraw_allocator=$PWD/$alloc_overlay \
        --dep ssz_raw -Mraw_decoder_root=$PWD/$root_overlay \
        runtime.o \
        -femit-bin=ssz-contract-probe
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p "$out/bin" "$out/meta"
      cp ssz-contract-probe "$out/bin/ssz-contract-probe"
      printf '%s\n' "zesu=codygunton/zesu@${zesuRepairedRevision}" > "$out/meta/provenance.txt"
      printf '%s\n' "zig=$(zig version)" >> "$out/meta/provenance.txt"
      runHook postInstall
    '';
  };

  # Row B source-vs-expectation gate (no Lean toolchain): the real private decoder source must (a)
  # decide accept/reject exactly as the corpus expects on every case, (b) never leak on any path, and
  # (c) survive the single-point out-of-memory sweep. Agreement is transitive, so this alone is a
  # complete source-vs-expectation check; the Lean-runner agreement lane cross-validates the oracle.
  sszContractProbeCheck =
    let
      probe = "${zesuContractProbe}/bin/ssz-contract-probe";
      agreement = builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_contract_agreement.py"; name = "ssz_contract_agreement.py"; };
      routineVectors = builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_routine_vectors.py"; name = "ssz_routine_vectors.py"; };
      generatedRoutineVectorsLean = builtins.path { path = repo + "/BinaryFv/SSZ/Zesu/Validation/GeneratedRoutineVectors.lean"; name = "GeneratedRoutineVectors.lean"; };
      mutation = builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_contract_mutation.py"; name = "ssz_contract_mutation.py"; };
      report = builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_contract_report.py"; name = "ssz_contract_report.py"; };
      corpusGen = builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_contract_corpus.py"; name = "ssz_contract_corpus.py"; };
      fixtures = builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_differential_audit.py"; name = "ssz_differential_audit.py"; };
    in
    pkgs.runCommand "ssz-contract-probe-check" {
      nativeBuildInputs = [ pkgs.python3 pkgs.coreutils ];
    } ''
      set -euo pipefail
      mkdir -p "$out"

      # (a) the real source's decision agrees with the corpus expectation on every case
      python3 ${agreement} --corpus-generator ${corpusGen} --fixtures ${fixtures} \
        --zesu-probe ${probe} --corpus-out "$out/corpus.jsonl" > "$out/agreement.txt" \
        || { echo "PROBE AGREEMENT FAILED" >&2; cat "$out/agreement.txt" >&2; exit 1; }

      # (b) no leaks and (c) out-of-memory safety: the probe exits nonzero on any defect
      ${probe} "$out/corpus.jsonl" --ledger "$out/ledger.jsonl" > "$out/outcomes.jsonl" \
        || { echo "PROBE LEAK/OOM DEFECT (see ledger)" >&2; cat "$out/ledger.jsonl" >&2; exit 1; }

      # (d) per-routine typed vectors: the real private routines match the exact expected value/error
      # AND — for the allocating routines — the observed per-event allocation ledger matches the
      # independent expected ledger the generator computes from the host ABI (`--dump-abi`) and each
      # routine's allocation structure. The probe exits nonzero on any value or ledger mismatch.
      ${probe} --dump-abi > "$out/abi.json"
      python3 ${routineVectors} --abi "$out/abi.json" --out "$out/routine-vectors.jsonl"
      ${probe} --routine-vectors "$out/routine-vectors.jsonl" > "$out/routine-outcomes.jsonl" \
        || { echo "ROUTINE VECTOR MISMATCH (see routine-outcomes.jsonl)" >&2; \
             grep -E '"match":false|"ledger_match":false' "$out/routine-outcomes.jsonl" >&2 || true; exit 1; }

      # Drift guard: the committed GeneratedRoutineVectors.lean (native_decide-checked by the proof.nix
      # meaning lane) must equal what the generator emits now, so the Zig-vector lane and the Lean lane
      # can never silently check different vectors.
      python3 ${routineVectors} --out-lean "$out/GeneratedRoutineVectors.lean"
      cmp -s "$out/GeneratedRoutineVectors.lean" ${generatedRoutineVectorsLean} \
        || { echo "DRIFT: committed GeneratedRoutineVectors.lean differs from --out-lean; regenerate it" >&2; \
             diff "$out/GeneratedRoutineVectors.lean" ${generatedRoutineVectorsLean} | head -40 >&2; exit 1; }

      # the real source rejects every targeted mutation class, and the per-routine value/error,
      # allocation-ledger, and removed-routine-case checks are all discriminating.
      python3 ${mutation} --fixtures ${fixtures} --lean-runner ${probe} \
        --probe ${probe} --routine-vectors-gen ${routineVectors} --report ${report} \
        --program-json ${elflingProgram}/program.json --abi "$out/abi.json" \
        --corpus "$out/corpus.jsonl" --outcomes "$out/outcomes.jsonl" --ledger "$out/ledger.jsonl" \
        > "$out/mutation.txt" \
        || { echo "MUTATION SMOKE FAILED" >&2; cat "$out/mutation.txt" >&2; exit 1; }

      # (e) coverage keyed by all 43 routines + 141 occurrences: every generated occurrence's routine
      # is exercised by a matching typed vector. The report asserts no routine/occurrence is an
      # uncovered gap; a regression that dropped a routine's vectors would surface here.
      python3 ${report} --corpus "$out/corpus.jsonl" --outcomes "$out/outcomes.jsonl" \
        --ledger "$out/ledger.jsonl" --out-json "$out/report.json" --out-md "$out/report.md" \
        --program-json ${elflingProgram}/program.json \
        --routine-vectors "$out/routine-vectors.jsonl" --routine-outcomes "$out/routine-outcomes.jsonl" \
        > "$out/report.txt"
      python3 -c 'import json,sys; rc=json.load(open("'"$out"'/report.json"))["routine_coverage"]; \
        sys.exit(0 if (rc["routines"]==43 and rc["occurrences"]==141 and rc["all_routines_covered"] \
        and rc["all_occurrences_covered"]) else 1)' \
        || { echo "COVERAGE GAP: not all 43 routines / 141 occurrences covered" >&2; \
             cat "$out/report.txt" >&2; exit 1; }

      {
        cat "$out/agreement.txt"
        cat "$out/mutation.txt"
        cat "$out/report.txt"
        printf 'cases=%s leaked=%s oom_unsafe=%s\n' \
          "$(wc -l < "$out/outcomes.jsonl")" \
          "$(grep -c '"leaked":true' "$out/ledger.jsonl" || true)" \
          "$(grep -c '"oom_safe":false' "$out/ledger.jsonl" || true)"
      } | tee "$out/summary.txt"
    '';

  # Production-object-unchanged guard (Row B). The shipped RV64 raw-SSZ objects are built by
  # `zesuRawObject` from the sha256-pinned Zesu source with NO validation overlay — the overlays are
  # appended only inside the host-only `zesuContractProbe`. Pinning the exact byte content of every
  # shipped object proves the Row B validation work cannot have changed production: an accidental
  # overlay leak, or any other drift, flips one of these hashes and fails the gate. (Rebuilds are
  # byte-deterministic: pinned source + pinned zig + ReleaseSmall.)
  sszProductionUnchanged = pkgs.runCommand "ssz-production-object-unchanged" {
    nativeBuildInputs = [ pkgs.coreutils ];
    decoderSha = "0acc871ac1ed37a70469d4240c4e3fba981d860b5102631da2044d74d5627817";
    allocatorSha = "d5c72b7ef88a470076f26286d5e39e030bc7f02991ef0bbad077007e28a4d152";
    sinkSha = "06225483b6dfc955a0a2141168cdbcf281a202bb1d2b0b5fdac8eb8df740b7fe";
  } ''
    set -euo pipefail
    obj=${zesuRawObject}/obj
    check() {
      got=$(sha256sum "$obj/$1" | cut -d' ' -f1)
      if [ "$got" != "$2" ]; then
        echo "PRODUCTION OBJECT CHANGED: $1 is $got, pinned $2. Row B validation is host-only and" \
             "must not affect production." >&2
        exit 1
      fi
      printf '%s  %s\n' "$got" "$1"
    }
    mkdir -p "$out"
    {
      check zesu-raw-ssz-decoder.o "$decoderSha"
      check zesu-raw-ssz-allocator.o "$allocatorSha"
      check zesu-raw-ssz-sink.o "$sinkSha"
    } > "$out/pinned-object-hashes.txt"
    printf 'all 3 shipped raw-SSZ objects byte-identical to their pinned hashes\n' | tee "$out/summary.txt"
  '';

  # Row C: deterministically capture the decodeOptionalBlobSchedule occurrence evidence from the
  # UNCHANGED production ELF (pinned qemu-riscv64 plugin trace + batch GDB), reduce it to the compact
  # form, and regenerate the Lean evidence module. The ELF is never rebuilt/patched. `setarch -R` +
  # the fixed nix-sandbox process image make every recorded address deterministic, so the emitted
  # module is reproducible; `sszBinaryEvidenceCheck` compares it to the committed one for drift.
  sszBinaryEvidence =
    let
      trace = builtins.path { path = repo + "/targets/ssz/zesu/trace"; name = "ssz-trace-tools"; };
      fixtures = builtins.path { path = repo + "/targets/ssz/zesu/tests/ssz_differential_audit.py"; name = "ssz_differential_audit.py"; };
      committedEvidence = builtins.path { path = repo + "/BinaryFv/SSZ/Zesu/Validation/GeneratedBinaryEvidence.lean"; name = "GeneratedBinaryEvidence.lean"; };
    in
    pkgs.runCommand "ssz-binary-occurrence-evidence" {
      nativeBuildInputs = [
        pkgs.python3 pkgs.gcc pkgs.gdb pkgs.util-linux pkgs.qemu-user pkgs.glib pkgs.pkg-config
        pkgs.coreutils
      ];
    } ''
      set -euo pipefail
      export HOME="$TMPDIR"
      cp -R ${trace} trace && chmod -R u+w trace
      cp ${fixtures} ssz_differential_audit.py

      # Build the observe-only plugin against the pinned qemu headers + glib.
      gcc -shared -fPIC -O2 -o trace/qemu_trace_plugin.so trace/qemu_trace_plugin.c \
        -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0)

      # Deterministic present / absent / malformed blob-schedule inputs.
      python3 - <<'PY'
      import importlib.util, sys
      spec = importlib.util.spec_from_file_location('fx', 'ssz_differential_audit.py')
      fx = importlib.util.module_from_spec(spec); sys.modules['fx'] = fx; spec.loader.exec_module(fx)
      open('present.bin', 'wb').write(fx.make_rich_v4())
      open('absent.bin', 'wb').write(fx.make_v4(chain_bytes=fx.chain_config(blob_schedule=None)))
      u64, u32, fa = fx.u64, fx.u32, fx.fork_activation
      act = fa(None, 0); blob = u64(22) + u64(23)                 # 16-byte (invalid) blob region
      fc = u64(20) + u32(16) + u32(16 + len(act)) + act + blob
      open('malformed.bin', 'wb').write(fx.make_v4(chain_bytes=u64(1) + u32(12) + fc))
      PY

      mkdir -p "$out"
      python3 trace/generate_evidence.py \
        --qemu ${qemuRiscv64} --gdb ${pkgs.gdb}/bin/gdb --plugin trace/qemu_trace_plugin.so \
        --elf ${zesuSsz}/bin/zesu-ssz --program-json ${elflingProgram}/program.json \
        --present present.bin --absent absent.bin --malformed malformed.bin --scratch scratch \
        --out-json "$out/evidence.json" --out-lean "$out/GeneratedBinaryEvidence.lean"

      # Drift: the committed generated evidence module (native_decide-checked by the proof.nix Row C
      # lane) must byte-equal what a fresh capture of the unchanged ELF produces, so the Lean checker
      # can never certify stale or hand-edited evidence.
      cmp -s "$out/GeneratedBinaryEvidence.lean" ${committedEvidence} \
        || { echo "DRIFT: committed GeneratedBinaryEvidence.lean differs from a fresh production capture" >&2; \
             diff "$out/GeneratedBinaryEvidence.lean" ${committedEvidence} | head -40 >&2; exit 1; }
      printf 'captured decodeOptionalBlobSchedule evidence for 3 arms; matches committed module\n' \
        | tee "$out/summary.txt"
    '';

  zesuSsz = pkgs.stdenvNoCC.mkDerivation {
    pname = "zesu-ssz-rv64im-zicclsm";
    version = "96f1621";
    src = source;
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
      ${riscvCc} ${cflags} -c ${repo}/targets/ssz/zesu/adapter/main.c \
        -o "$out/obj/zesu-ssz-main.o"
      ${riscvCc} ${cflags} -c ${repo}/targets/common/riscv64_runtime.c \
        -o "$out/obj/riscv64_runtime.o"
      ${riscvCc} ${cflags} -c ${repo}/targets/common/riscv64_start.S \
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
        ${repo}/targets/ssz/zesu/tests/ssz_sink_observability.py \
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
    version = "aa6c943-96f1621";
    src = zesu;
    nativeBuildInputs = [
      pkgs.gnumake
      pkgs.gnutar
      pkgs.gzip
      pkgs.gmp
      pkgs.pkg-config
      pkgs.secp256k1
      pkgs.openssl
      pkgs.stdenv.cc
      pkgs.zig
    ];
    buildPhase = ":";
    doCheck = true;
    checkPhase = ''
      export LD_LIBRARY_PATH="${zesuNativeCrypto}/lib"
      export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global"

      prepare_suite_source() {
        substituteInPlace build.zig \
          --replace-fail 'step.root_module.addLibraryPath(.{ .cwd_relative = "/usr/local/lib" });' \
          'step.root_module.addLibraryPath(.{ .cwd_relative = std.fs.path.dirname(mcl).? });'
        # The pinned zkeVM release contains a 264.3 MiB JSON fixture. This changes only the
        # test runner's input limit, not production decoder behavior.
        substituteInPlace tools/zkevm_test/main.zig \
          --replace-fail '.limited(256 * 1024 * 1024)' \
          '.limited(512 * 1024 * 1024)'
      }

      install_fixtures() {
        mkdir -p spec-tests/fixtures/zkevm
        tar xzf ${zesuFixtures} --strip-components=1 -C spec-tests/fixtures/zkevm
      }

      run_suite() {
        label="$1"
        export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-$label"
        zig build test -Dcrypto-prefix="${zesuNativeCrypto}"
        zig build zkevm-tests -Dcrypto-prefix="${zesuNativeCrypto}"
      }

      prepare_suite_source
      install_fixtures
      run_suite production

      repaired_source="$TMPDIR/repaired-source"
      cp -a ${zesuRepaired} "$repaired_source"
      chmod -R u+w "$repaired_source"
      cd "$repaired_source"
      prepare_suite_source
      install_fixtures
      run_suite repaired
    '';
    installPhase = ''
      mkdir -p "$out"
      printf '%s\n' production repaired > "$out/passed"
      printf '%s\n' "production=Consensys/zesu@${zesuProductionRevision}" > "$out/provenance.txt"
      printf '%s\n' "repaired=codygunton/zesu@${zesuRepairedRevision}" >> "$out/provenance.txt"
    '';
  };

  zesuSszRun = pkgs.writeShellApplication {
    name = "zesu-ssz";
    runtimeInputs = [ pkgs.qemu-user ];
    text = ''
      exec qemu-riscv64 ${zesuSsz}/bin/zesu-ssz "$@"
    '';
  };
in
{
  public = {
    inherit
      zesuNativeSuite
      zesuProductionObject
      zesuRawObject
      zesuRawSidecar
      zesuRuntimeSidecar
      elflingProgram
      blobScheduleInstance
      elflingDecoderLlvmIr
      elflingRelocationCheck
      elflingGeneratorDefectsCheck
      sszContractCorpus
      zesuContractProbe
      sszContractProbeCheck
      sszProductionUnchanged
      sszBinaryEvidence
      zesuAbiManifest
      zesuSinkObservability
      zesuSsz
      zesuSszRun
      zesuValue;

    zesu-value = zesuValue;
    zesu-ssz = zesuSsz;
    zesu-raw-ssz-sidecar = zesuRawSidecar;
    zesu-ssz-runtime-sidecar = zesuRuntimeSidecar;
    elfling-program = elflingProgram;
    blob-schedule-instance = blobScheduleInstance;
    elfling-decoder-llvm-ir = elflingDecoderLlvmIr;
    elfling-relocation-check = elflingRelocationCheck;
    elfling-generator-defects-check = elflingGeneratorDefectsCheck;
    ssz-contract-corpus = sszContractCorpus;
    zesu-contract-probe = zesuContractProbe;
    ssz-contract-probe-check = sszContractProbeCheck;
    ssz-production-object-unchanged = sszProductionUnchanged;
    ssz-binary-evidence = sszBinaryEvidence;
    zesu-abi-manifest = zesuAbiManifest;
    zesu-sink-observability = zesuSinkObservability;
    zesu-native-suite = zesuNativeSuite;
  };
}
