{ pkgs, rv64, targets }:
let
  inherit (rv64) riscvNm riscvObjdump riscvSize;
  zesuRv64Object = targets.public.zesuRv64Object;
  zesuSszDecodeRv64Elf = targets.public.zesuSszDecodeRv64Elf;
  zesuSszDecodeLinuxRv64Elf = targets.public.zesuSszDecodeLinuxRv64Elf;

  stats = pkgs.runCommand "zesu-rv64-object-stats" { } ''
    mkdir -p "$out/bin" "$out/meta"
    ${riscvSize} ${zesuRv64Object}/obj/zesu.o > "$out/meta/size.txt"
    ${riscvNm} -u ${zesuRv64Object}/obj/zesu.o > "$out/meta/undefined-symbols.txt"
    cat > "$out/bin/show-stats" <<EOF
    #!${pkgs.runtimeShell}
    cat ${zesuRv64Object}/meta/provenance.txt
    cat "$out/meta/size.txt"
    EOF
    chmod +x "$out/bin/show-stats"
  '';

  dump = pkgs.writeShellApplication {
    name = "dump-zesu-rv64-object";
    text = ''exec ${riscvObjdump} -dr ${zesuRv64Object}/obj/zesu.o "$@"'';
  };

  python = pkgs.python3.withPackages (ps: [ ps.pyelftools ps.capstone ps.numpy ]);
  makeCfg = name: artifact: filename: pkgs.runCommand name { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      PYTHONPATH=${../tools} python ${../tools/generate_zesu_cfg.py} \
        --object ${artifact}/${filename} --output "$out/zesu-cfg.json" \
        --flame "$out/flame.json" --proof-map "$out/proof-map.json"
      python ${../tools/test_zesu_cfg.py} "$out/zesu-cfg.json"
      PYTHONPATH=${../tools} python ${../tools/test_source_path_normalization.py}
      mkdir "$TMPDIR/repeated"
      PYTHONPATH=${../tools} python ${../tools/generate_zesu_cfg.py} \
        --object ${artifact}/${filename} --output "$TMPDIR/repeated/zesu-cfg.json" \
        --flame "$TMPDIR/repeated/flame.json" --proof-map "$TMPDIR/repeated/proof-map.json"
      cmp "$out/zesu-cfg.json" "$TMPDIR/repeated/zesu-cfg.json"
      cmp "$out/flame.json" "$TMPDIR/repeated/flame.json"
      cmp "$out/proof-map.json" "$TMPDIR/repeated/proof-map.json"
    '';
  zesuCfg = makeCfg "zesu-rv64-cfg-d67f28c" zesuRv64Object "obj/zesu.o";
  zesuSszDecodeCfg = makeCfg "zesu-ssz-decode-rv64-cfg-d67f28c" zesuSszDecodeRv64Elf "bin/zesu-ssz-decode";
  zesuSszDecodeLinuxCfg = makeCfg "zesu-ssz-decode-linux-rv64-cfg-d67f28c"
    zesuSszDecodeLinuxRv64Elf "bin/zesu-ssz-decode";
  zesuSszDecodeBareMetalRetargetCheck = pkgs.runCommand
    "zesu-ssz-decode-bare-metal-retarget-check-d67f28c" { nativeBuildInputs = [ python ]; } ''
      PYTHONPATH=${../tools} python ${../tools/test_elf_identity.py}
      PYTHONPATH=${../tools} python ${../tools/test_validate_baremetal_retarget.py}
      python ${../tools/validate_baremetal_retarget.py} \
        --old-elf ${zesuSszDecodeLinuxRv64Elf}/bin/zesu-ssz-decode \
        --new-elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
        --old-cfg ${zesuSszDecodeLinuxCfg}/zesu-cfg.json \
        --new-cfg ${zesuSszDecodeCfg}/zesu-cfg.json
      touch "$out"
    '';

  zesuSszDecodeLevel1Manifest = pkgs.runCommand "zesu-ssz-decode-level1-manifest-d67f28c"
    { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_manifest.py} \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --flame ${zesuSszDecodeCfg}/flame.json \
        --level 1 --output "$out/level1-manifest.json"
      python ${../tools/test_level_manifest.py} "$out/level1-manifest.json"
    '';

  zesuSszDecodeLevel2Manifest = pkgs.runCommand "zesu-ssz-decode-level2-manifest-d67f28c"
    { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_manifest.py} \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --flame ${zesuSszDecodeCfg}/flame.json \
        --level 2 --output "$out/level2-manifest.json"
      PYTHONPATH=${../tools} python ${../tools/test_level2_manifest.py} "$out/level2-manifest.json"
    '';

  zesuSszDecodeLevel3Manifest = pkgs.runCommand "zesu-ssz-decode-level3-manifest-d67f28c"
    { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_manifest.py} \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --flame ${zesuSszDecodeCfg}/flame.json \
        --level 3 --output "$out/level3-manifest.json"
      PYTHONPATH=${../tools} python ${../tools/test_level3_manifest.py} \
        "$out/level3-manifest.json" ${../tools/hlevel3_targets.json}
    '';

  zesuSszDecodeLevel1BoundaryBindings = pkgs.runCommand
    "zesu-ssz-decode-level1-boundary-bindings-d67f28c" { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_boundary_bindings.py} \
        --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json \
        --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
        --output "$out/level1-boundary-bindings.json"
      python ${../tools/test_level_boundary_bindings.py} "$out/level1-boundary-bindings.json"
    '';

  zesuSszDecodeLevel2BoundaryBindings = pkgs.runCommand
    "zesu-ssz-decode-level2-boundary-bindings-d67f28c" { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_boundary_bindings.py} \
        --manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
        --output "$out/level2-boundary-bindings.json"
      python ${../tools/test_level2_boundary_bindings.py} "$out/level2-boundary-bindings.json"
    '';

  zesuSszDecodeLevel3BoundaryBindings = pkgs.runCommand
    "zesu-ssz-decode-level3-boundary-bindings-d67f28c" { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_boundary_bindings.py} \
        --manifest ${zesuSszDecodeLevel3Manifest}/level3-manifest.json \
        --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
        --output "$out/level3-boundary-bindings.json"
      python ${../tools/test_level3_boundary_bindings.py} "$out/level3-boundary-bindings.json"
    '';

  zesuSszDecodeLevel1Lean = pkgs.runCommand "zesu-ssz-decode-level1-lean-d67f28c"
    { nativeBuildInputs = [ pkgs.python3 ]; } ''
      mkdir -p "$out/BinaryFv/Zesu/Elflings"
      PYTHONPATH=${../tools} python ${../tools/test_generate_level1_lean.py}
      python ${../tools/generate_level1_lean.py} \
        --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --output "$out/BinaryFv/Zesu/Elflings/GeneratedLevel1.lean"
      cmp "$out/BinaryFv/Zesu/Elflings/GeneratedLevel1.lean" \
        ${../BinaryFv/Zesu/Elflings/GeneratedLevel1.lean}
    '';

  zesuSszDecodeLevel2Lean = pkgs.runCommand "zesu-ssz-decode-level2-lean-d67f28c"
    { nativeBuildInputs = [ pkgs.python3 ]; } ''
      mkdir -p "$out/BinaryFv/Zesu/Elflings"
      PYTHONPATH=${../tools} python ${../tools/test_generate_level2_lean.py} \
        ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        ${zesuSszDecodeCfg}/zesu-cfg.json \
        ${../tools/level2_contract_evidence_profiles.json}
      PYTHONPATH=${../tools} python ${../tools/generate_level2_lean.py} \
        --manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --profiles ${../tools/level2_contract_evidence_profiles.json} \
        --output "$out/BinaryFv/Zesu/Elflings/GeneratedLevel2.lean"
      cmp "$out/BinaryFv/Zesu/Elflings/GeneratedLevel2.lean" \
        ${../BinaryFv/Zesu/Elflings/GeneratedLevel2.lean}
    '';

  zesuSszDecodeStatelessInputLayout = pkgs.runCommand
    "zesu-ssz-decode-stateless-input-layout-d67f28c" { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      PYTHONPATH=${../tools} python ${../tools/generate_zig_type_layout.py} \
        --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
        --type input.StatelessInput --output "$out/stateless-input-layout.json"
      python ${../tools/test_zig_type_layout.py} "$out/stateless-input-layout.json"
    '';

  level1EvidenceTools = builtins.path {
    path = ../tools/level1_evidence;
    name = "zesu-level1-evidence-tools";
  };
  zesuSszDecodeLevel1Evidence = pkgs.runCommand "zesu-ssz-decode-level1-evidence-d67f28c" {
    nativeBuildInputs = [ pkgs.gcc pkgs.glib pkgs.pkg-config python pkgs.qemu-user ];
  } ''
    set -euo pipefail
    cp -R ${level1EvidenceTools} tools
    chmod -R u+w tools
    cp ${../tools/elf_identity.py} tools/elf_identity.py
    python -m unittest discover -s tools -p 'test_*.py'
    gcc -shared -fPIC -O2 -Wall -Wextra -Werror -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0) tools/qemu_trace_plugin.c -o trace.so
    snapshots=$(python -c 'import json; rows=json.load(open("${zesuSszDecodeLevel1Manifest}/level1-manifest.json"))["instances"]; cfg=json.load(open("${zesuSszDecodeCfg}/zesu-cfg.json")); main=next(row for row in cfg["functionInstances"] if row["kind"] == "concrete" and row["name"] == "ssz_decode_root.main"); pcs=sorted({pc for row in rows for pc in row["executionPcs"]} | {row["entryPc"] for row in rows} | set(main["pcs"])); print(",".join("snapshot="+str(pc) for pc in pcs))')
    ${rv64.qemuRiscv64} -plugin ./trace.so,out=minimal.trace,input=${targets.public.zesuSszDecodeSmoke}/minimal.ssz,input_address=0x2001a000,context_address=0x2401a0b8,terminal=0x101d0,capture_write=0x10190,capture_window=0x14d30,capture_window_width=848,"$snapshots" ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode
    ${rv64.qemuRiscv64} -plugin ./trace.so,out=invalid.trace,input=${targets.public.zesuSszDecodeSmoke}/invalid.ssz,input_address=0x2001a000,context_address=0x2401a0b8,terminal=0x101d0,capture_write=0x10190,capture_window=0x14d30,capture_window_width=848,"$snapshots" ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode
    mkdir -p "$out"
    python tools/analyze.py --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json \
      --bindings ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json \
      --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      --trace minimal=minimal.trace --trace invalid=invalid.trace \
      --input minimal=${targets.public.zesuSszDecodeSmoke}/minimal.ssz \
      --input invalid=${targets.public.zesuSszDecodeSmoke}/invalid.ssz \
      --output "$out/level1-evidence.json"
  '';

  zesuSszDecodeLevel2Evidence = pkgs.runCommand "zesu-ssz-decode-level2-evidence-d67f28c" {
    nativeBuildInputs = [ pkgs.gcc pkgs.glib pkgs.pkg-config python pkgs.qemu-user ];
  } ''
    set -euo pipefail
    cp -R ${level1EvidenceTools} tools
    chmod -R u+w tools
    cp ${../tools/elf_identity.py} tools/elf_identity.py
    python -m unittest discover -s tools -p 'test_*.py'
    gcc -shared -fPIC -O2 -Wall -Wextra -Werror -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0) tools/qemu_trace_plugin.c -o trace.so
    snapshots=$(python -c 'import json; rows=json.load(open("${zesuSszDecodeLevel2Manifest}/level2-manifest.json"))["instances"]; pcs=sorted({pc for row in rows for pc in row["executionPcs"]} | {row["entryPc"] for row in rows} | {pc for row in rows for pc in row["exitPcs"]}); print(",".join("snapshot="+str(pc) for pc in pcs))')
    for vector in minimal block-number chain-id-zero legacy-requests legacy-payload \
        future-activation extra-data-33 public-key-overflow versioned-hash-overflow \
        one-transaction one-withdrawal invalid; do
      ${rv64.qemuRiscv64} -plugin ./trace.so,out="$vector.trace",input=${targets.public.zesuSszDecodeSmoke}/"$vector.ssz",input_address=0x2001a000,context_address=0x2401a0b8,terminal=0x101d0,capture_write=0x10190,capture_window=0x14d30,capture_window_width=848,"$snapshots" \
        ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode
    done
    mkdir -p "$out"
    python tools/analyze.py --structural-only \
      --manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
      --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      --trace minimal=minimal.trace --trace block-number=block-number.trace \
      --trace chain-id-zero=chain-id-zero.trace --trace legacy-requests=legacy-requests.trace \
      --trace legacy-payload=legacy-payload.trace \
      --trace future-activation=future-activation.trace \
      --trace extra-data-33=extra-data-33.trace \
      --trace public-key-overflow=public-key-overflow.trace \
      --trace versioned-hash-overflow=versioned-hash-overflow.trace \
      --trace one-transaction=one-transaction.trace \
      --trace one-withdrawal=one-withdrawal.trace \
      --trace invalid=invalid.trace \
      --output "$out/level2-evidence.json"
  '';

  zesuSszDecodeLevel2Admission = pkgs.runCommand
    "zesu-ssz-decode-level2-admission-d67f28c" { nativeBuildInputs = [ pkgs.python3 ]; } ''
      mkdir -p "$out"
      PYTHONPATH=${../tools} python ${../tools/test_generate_level2_admission.py} \
        ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        ${zesuSszDecodeLevel2Evidence}/level2-evidence.json \
        ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json \
        ${zesuSszDecodeCfg}/zesu-cfg.json \
        ${../tools/level2_contract_clauses.json} \
        ${../tools/level2_contract_evidence_profiles.json} \
        ${../tools/level2_contract_defect_audits.json}
      PYTHONPATH=${../tools} python ${../tools/generate_level2_admission.py} \
        --manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        --evidence ${zesuSszDecodeLevel2Evidence}/level2-evidence.json \
        --bindings ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --registry ${../tools/level2_contract_clauses.json} \
        --profiles ${../tools/level2_contract_evidence_profiles.json} \
        --defect-audits ${../tools/level2_contract_defect_audits.json} \
        --output "$out/level2-admission.json"
    '';

  zesuSszDecodeLevel3Evidence = pkgs.runCommand "zesu-ssz-decode-level3-evidence-d67f28c" {
    nativeBuildInputs = [ pkgs.gcc pkgs.glib pkgs.pkg-config python pkgs.qemu-user ];
  } ''
    set -euo pipefail
    cp -R ${level1EvidenceTools} tools
    chmod -R u+w tools
    cp ${../tools/elf_identity.py} tools/elf_identity.py
    python -m unittest discover -s tools -p 'test_*.py'
    gcc -shared -fPIC -O2 -Wall -Wextra -Werror -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0) tools/qemu_trace_plugin.c -o trace.so
    snapshots=$(python -c 'import json; rows=json.load(open("${zesuSszDecodeLevel3Manifest}/level3-manifest.json"))["instances"]; pcs=sorted({pc for row in rows for pc in row["executionPcs"]} | {row["entryPc"] for row in rows} | {pc for row in rows for pc in row["exitPcs"]}); print(",".join("snapshot="+str(pc) for pc in pcs))')
    for schema in $(seq 0 22); do
      cp ${targets.public.zesuSszDecodeSmoke}/minimal.ssz "fork-schema-$schema.ssz"
      chmod u+w "fork-schema-$schema.ssz"
      python -c 'from pathlib import Path; import sys; p=Path(sys.argv[1]); b=bytearray(p.read_bytes()); b[0]=int(sys.argv[2]); p.write_bytes(b)' \
        "fork-schema-$schema.ssz" "$schema"
    done
    for vector in minimal block-number chain-id-zero legacy-requests legacy-payload \
        future-activation extra-data-33 public-key-overflow versioned-hash-overflow \
        one-transaction one-withdrawal activation-timestamp blob-transaction invalid; do
      ${rv64.qemuRiscv64} -plugin ./trace.so,out="$vector.trace",input=${targets.public.zesuSszDecodeSmoke}/"$vector.ssz",input_address=0x2001a000,context_address=0x2401a0b8,terminal=0x101d0,capture_write=0x10190,capture_window=0x14d30,capture_window_width=848,"$snapshots" \
        ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode
    done
    fork_traces=()
    for schema in $(seq 0 22); do
      label=$(printf 'fork-schema-%02x' "$schema")
      ${rv64.qemuRiscv64} -plugin ./trace.so,out="$label.trace",input="fork-schema-$schema.ssz",input_address=0x2001a000,context_address=0x2401a0b8,terminal=0x101d0,capture_write=0x10190,capture_window=0x14d30,capture_window_width=848,"$snapshots" \
        ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode
      fork_traces+=(--trace "$label=$label.trace")
    done
    mkdir -p "$out"
    # This pre-work records unobserved proposed contracts. It does not admit them.
    python tools/analyze.py --structural-only --allow-incomplete-entry-coverage \
      --manifest ${zesuSszDecodeLevel3Manifest}/level3-manifest.json \
      --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      --trace minimal=minimal.trace --trace block-number=block-number.trace \
      --trace chain-id-zero=chain-id-zero.trace --trace legacy-requests=legacy-requests.trace \
      --trace legacy-payload=legacy-payload.trace \
      --trace future-activation=future-activation.trace \
      --trace extra-data-33=extra-data-33.trace \
      --trace public-key-overflow=public-key-overflow.trace \
      --trace versioned-hash-overflow=versioned-hash-overflow.trace \
      --trace one-transaction=one-transaction.trace \
      --trace one-withdrawal=one-withdrawal.trace \
      --trace activation-timestamp=activation-timestamp.trace \
      --trace blob-transaction=blob-transaction.trace \
      --trace invalid=invalid.trace \
      "''${fork_traces[@]}" \
      --output "$out/level3-evidence.json"
  '';

  zesuSszDecodeHLevel3Prework = pkgs.runCommand
    "zesu-ssz-decode-hlevel3-prework-d67f28c" { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      PYTHONPATH=${../tools} python ${../tools/generate_hlevel3_prework.py} \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --flame ${zesuSszDecodeCfg}/flame.json \
        --manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        --level3-manifest ${zesuSszDecodeLevel3Manifest}/level3-manifest.json \
        --evidence ${zesuSszDecodeLevel2Evidence}/level2-evidence.json \
        --level3-evidence ${zesuSszDecodeLevel3Evidence}/level3-evidence.json \
        --clauses ${../tools/level2_contract_clauses.json} \
        --targets ${../tools/hlevel3_targets.json} \
        --output "$out/hlevel3-prework.json"
      PYTHONPATH=${../tools} python ${../tools/generate_hlevel3_guidance.py} \
        --inventory "$out/hlevel3-prework.json" \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --catalogue ${../tools/hlevel3_proof_idioms.json} \
        --lean-root ${../BinaryFv/Zesu/MachineExecution} \
        --output "$out/hlevel3-guidance.json"
      PYTHONPATH=${../tools} python ${../tools/generate_hlevel3_admission.py} \
        --inventory "$out/hlevel3-prework.json" \
        --evidence ${zesuSszDecodeLevel3Evidence}/level3-evidence.json \
        --bindings ${zesuSszDecodeLevel3BoundaryBindings}/level3-boundary-bindings.json \
        --registry ${../tools/hlevel3_contract_schemas.json} \
        --output "$out/hlevel3-admission.json"
      HLEVEL3_DIRECT_PROOFS=${../tools/hlevel3_direct_proofs.json} \
        PYTHONPATH=${../tools} python ${../tools/generate_hlevel3_lean_staging.py} \
        --inventory "$out/hlevel3-prework.json" \
        --guidance "$out/hlevel3-guidance.json" \
        --admission "$out/hlevel3-admission.json" \
        --catalogue ${../tools/hlevel3_proof_idioms.json} \
        --output "$out/HLevel3.lean" \
        --idiom-output "$out/HLevel3IdiomChecks.lean"
      cmp "$out/HLevel3.lean" ${../BinaryFv/Zesu/Staging/HLevel3.lean}
      cmp "$out/HLevel3IdiomChecks.lean" ${../BinaryFv/Zesu/Staging/HLevel3IdiomChecks.lean}
      PYTHONPATH=${../tools} python ${../tools/validate_hlevel3_guidance_retrospective.py} \
        --manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        --source ${../BinaryFv/Zesu/MachineExecution/Level1WriteSuccessSteps.lean} \
        --output "$out/hlevel3-retrospective.json"
      mkdir live-artifacts
      cp ${zesuSszDecodeLevel2Manifest}/level2-manifest.json live-artifacts/
      cp ${zesuSszDecodeLevel2Evidence}/level2-evidence.json live-artifacts/
      HLEVEL3_ARTIFACT_DIR=$PWD/live-artifacts \
      HLEVEL3_CFG_DIR=${zesuSszDecodeCfg} \
      HLEVEL3_MANIFEST=${zesuSszDecodeLevel3Manifest}/level3-manifest.json \
      HLEVEL3_EVIDENCE=${zesuSszDecodeLevel3Evidence}/level3-evidence.json \
      HLEVEL3_CLAUSES=${../tools/level2_contract_clauses.json} \
      HLEVEL3_TARGETS=${../tools/hlevel3_targets.json} \
        PYTHONPATH=${../tools} python ${../tools/test_generate_hlevel3_prework.py}
      HLEVEL3_PREWORK_DIR=$out \
      HLEVEL3_EVIDENCE=${zesuSszDecodeLevel3Evidence}/level3-evidence.json \
      HLEVEL3_BINDINGS=${zesuSszDecodeLevel3BoundaryBindings}/level3-boundary-bindings.json \
      HLEVEL3_REGISTRY=${../tools/hlevel3_contract_schemas.json} \
        PYTHONPATH=${../tools} python ${../tools/test_generate_hlevel3_admission.py}
      HLEVEL3_GUIDANCE=$out/hlevel3-guidance.json \
        PYTHONPATH=${../tools} python ${../tools/test_generate_hlevel3_guidance.py}
      HLEVEL3_PREWORK_DIR=$out \
      HLEVEL3_CATALOGUE=${../tools/hlevel3_proof_idioms.json} \
      HLEVEL3_DIRECT_PROOFS=${../tools/hlevel3_direct_proofs.json} \
      HLEVEL3_READ_U32_SOURCE=${../BinaryFv/Zesu/Staging/ReadU32.lean} \
        PYTHONPATH=${../tools} python ${../tools/test_generate_hlevel3_lean_staging.py}
      HLEVEL3_LEVEL2_MANIFEST=${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
      HLEVEL3_RETROSPECTIVE_SOURCE=${../BinaryFv/Zesu/MachineExecution/Level1WriteSuccessSteps.lean} \
        PYTHONPATH=${../tools} python ${../tools/test_validate_hlevel3_guidance_retrospective.py}
      mkdir repeated
      PYTHONPATH=${../tools} python ${../tools/generate_hlevel3_prework.py} \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --flame ${zesuSszDecodeCfg}/flame.json \
        --manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json \
        --level3-manifest ${zesuSszDecodeLevel3Manifest}/level3-manifest.json \
        --evidence ${zesuSszDecodeLevel2Evidence}/level2-evidence.json \
        --level3-evidence ${zesuSszDecodeLevel3Evidence}/level3-evidence.json \
        --clauses ${../tools/level2_contract_clauses.json} \
        --targets ${../tools/hlevel3_targets.json} \
        --output repeated/hlevel3-prework.json
      cmp "$out/hlevel3-prework.json" repeated/hlevel3-prework.json
      PYTHONPATH=${../tools} python ${../tools/generate_hlevel3_guidance.py} \
        --inventory repeated/hlevel3-prework.json \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --catalogue ${../tools/hlevel3_proof_idioms.json} \
        --lean-root ${../BinaryFv/Zesu/MachineExecution} \
        --output repeated/hlevel3-guidance.json
      cmp "$out/hlevel3-guidance.json" repeated/hlevel3-guidance.json
    '';

  zesuCfgUi = pkgs.runCommand "zesu-rv64-cfg-ui-d67f28c"
    { nativeBuildInputs = [ pkgs.python3 ]; } ''
    cp -R ${../tools/binary-regions-ui} "$out"
    chmod -R u+w "$out"
    cp ${zesuSszDecodeCfg}/zesu-cfg.json "$out/zesu-cfg.json"
    cp ${zesuSszDecodeCfg}/flame.json "$out/"
    python ${../tools/build_flame_ui_data.py} --input ${zesuSszDecodeCfg}/flame.json \
      --core "$out/flame-core.json" --details "$out/flame-details.json"
    cp ${zesuSszDecodeLevel1Manifest}/level1-manifest.json "$out/"
    cp ${zesuSszDecodeLevel2Manifest}/level2-manifest.json "$out/"
    cp ${zesuSszDecodeLevel1Evidence}/level1-evidence.json "$out/"
    cp ${zesuSszDecodeLevel2Evidence}/level2-evidence.json "$out/"
    cp ${zesuSszDecodeLevel2Admission}/level2-admission.json "$out/"
    cp ${zesuSszDecodeLevel3Manifest}/level3-manifest.json "$out/"
    cp ${zesuSszDecodeLevel3Evidence}/level3-evidence.json "$out/"
    cp ${zesuSszDecodeLevel3BoundaryBindings}/level3-boundary-bindings.json "$out/"
    cp ${zesuSszDecodeHLevel3Prework}/hlevel3-prework.json "$out/"
    cp ${zesuSszDecodeHLevel3Prework}/hlevel3-guidance.json "$out/"
    cp ${zesuSszDecodeHLevel3Prework}/hlevel3-admission.json "$out/"
    cp ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json "$out/"
    cp ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json "$out/"
    cp ${zesuSszDecodeStatelessInputLayout}/stateless-input-layout.json "$out/"
    cp ${../tools/build_ssz_proof_map.py} build_ssz_proof_map.py
    cp ${../tools/test_ssz_proof_map.py} test_ssz_proof_map.py
    cp ${../tools/hlevel3_direct_proofs.json} "$out/hlevel3_direct_proofs.json"
    python build_ssz_proof_map.py --cfg ${zesuSszDecodeCfg}/zesu-cfg.json --flame ${zesuSszDecodeCfg}/flame.json --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json --evidence ${zesuSszDecodeLevel1Evidence}/level1-evidence.json --bindings ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json --level2-manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json --level2-evidence ${zesuSszDecodeLevel2Evidence}/level2-evidence.json --level2-bindings ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json --hlevel3-inventory ${zesuSszDecodeHLevel3Prework}/hlevel3-prework.json --hlevel3-guidance ${zesuSszDecodeHLevel3Prework}/hlevel3-guidance.json --hlevel3-admission ${zesuSszDecodeHLevel3Prework}/hlevel3-admission.json --hlevel3-direct-proofs "$out/hlevel3_direct_proofs.json" --output "$out/proof-map.json" --flame-progress-output "$out/flame-progress.json"
    HLEVEL3_DIRECT_PROOFS="$out/hlevel3_direct_proofs.json" \
      python test_ssz_proof_map.py ${zesuSszDecodeCfg}/zesu-cfg.json ${zesuSszDecodeCfg}/flame.json ${zesuSszDecodeLevel1Manifest}/level1-manifest.json ${zesuSszDecodeLevel1Evidence}/level1-evidence.json ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json ${zesuSszDecodeLevel2Manifest}/level2-manifest.json ${zesuSszDecodeLevel2Evidence}/level2-evidence.json ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json ${zesuSszDecodeHLevel3Prework}/hlevel3-prework.json ${zesuSszDecodeHLevel3Prework}/hlevel3-guidance.json ${zesuSszDecodeHLevel3Prework}/hlevel3-admission.json
    grep -Fq "fetch('proof-map.json')" "$out/index.html"
    grep -Fq "flame-core-full.json" "$out/index.html"
    grep -Fq '.minFrameSize(1)' "$out/index.html"
    grep -Fq 'PROGRESS.get(meta.owner)' "$out/index.html"
    grep -Fq 'contract_consumed:' "$out/index.html"
    grep -Fq 'proof_in_progress:' "$out/index.html"
    grep -Fq 'covered_by_proved_parent' "$out/index.html"
    cp ${zesuCfg}/flame.json "$out/flame-full.json"
    python ${../tools/build_flame_ui_data.py} --input ${zesuCfg}/flame.json \
      --core "$out/flame-core-full.json" --details "$out/flame-details-full.json"
    PYTHONPATH=${../tools} python ${../tools/test_flame_ui_data.py}
  '';
in
{
  public = {
    inherit dump stats zesuCfg zesuSszDecodeCfg zesuSszDecodeLinuxCfg
      zesuSszDecodeBareMetalRetargetCheck zesuSszDecodeLevel1Manifest
      zesuSszDecodeLevel2Manifest zesuSszDecodeLevel3Manifest
      zesuSszDecodeLevel1BoundaryBindings zesuSszDecodeLevel2BoundaryBindings
      zesuSszDecodeLevel3BoundaryBindings
      zesuSszDecodeLevel1Lean
      zesuSszDecodeLevel2Lean
      zesuSszDecodeStatelessInputLayout
      zesuSszDecodeLevel1Evidence zesuSszDecodeLevel2Evidence zesuSszDecodeLevel3Evidence
      zesuSszDecodeLevel2Admission zesuSszDecodeHLevel3Prework zesuCfgUi;
    machine-regions-ui = zesuCfgUi;
  };
}
