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

  python = pkgs.python3.withPackages (ps: [ ps.pyelftools ps.capstone ]);
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
    cp ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json "$out/"
    cp ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json "$out/"
    cp ${zesuSszDecodeStatelessInputLayout}/stateless-input-layout.json "$out/"
    cp ${../tools/build_ssz_proof_map.py} build_ssz_proof_map.py
    cp ${../tools/test_ssz_proof_map.py} test_ssz_proof_map.py
    python build_ssz_proof_map.py --cfg ${zesuSszDecodeCfg}/zesu-cfg.json --flame ${zesuSszDecodeCfg}/flame.json --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json --evidence ${zesuSszDecodeLevel1Evidence}/level1-evidence.json --bindings ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json --level2-manifest ${zesuSszDecodeLevel2Manifest}/level2-manifest.json --level2-evidence ${zesuSszDecodeLevel2Evidence}/level2-evidence.json --level2-bindings ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json --output "$out/proof-map.json" --flame-progress-output "$out/flame-progress.json"
    python test_ssz_proof_map.py ${zesuSszDecodeCfg}/zesu-cfg.json ${zesuSszDecodeCfg}/flame.json ${zesuSszDecodeLevel1Manifest}/level1-manifest.json ${zesuSszDecodeLevel1Evidence}/level1-evidence.json ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json ${zesuSszDecodeLevel2Manifest}/level2-manifest.json ${zesuSszDecodeLevel2Evidence}/level2-evidence.json ${zesuSszDecodeLevel2BoundaryBindings}/level2-boundary-bindings.json
    grep -Fq "fetch('proof-map.json')" "$out/index.html"
    grep -Fq "flame-core-full.json" "$out/index.html"
    grep -Fq '.minFrameSize(1)' "$out/index.html"
    grep -Fq 'PROGRESS.get(meta.owner)' "$out/index.html"
    grep -Fq 'contract_consumed:' "$out/index.html"
    grep -Fq 'proof_in_progress:' "$out/index.html"
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
      zesuSszDecodeLevel2Manifest
      zesuSszDecodeLevel1BoundaryBindings zesuSszDecodeLevel2BoundaryBindings
      zesuSszDecodeLevel1Lean
      zesuSszDecodeLevel2Lean
      zesuSszDecodeStatelessInputLayout
      zesuSszDecodeLevel1Evidence zesuSszDecodeLevel2Evidence
      zesuSszDecodeLevel2Admission zesuCfgUi;
    machine-regions-ui = zesuCfgUi;
  };
}
