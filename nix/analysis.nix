{ pkgs, rv64, targets }:
let
  inherit (rv64) riscvNm riscvObjdump riscvSize;
  zesuRv64Object = targets.public.zesuRv64Object;
  zesuSszDecodeRv64Elf = targets.public.zesuSszDecodeRv64Elf;

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
      python ${../tools/generate_zesu_cfg.py} \
        --object ${artifact}/${filename} --output "$out/zesu-cfg.json" \
        --flame "$out/flame.json" --proof-map "$out/proof-map.json"
      python ${../tools/test_zesu_cfg.py} "$out/zesu-cfg.json"
      mkdir "$TMPDIR/repeated"
      python ${../tools/generate_zesu_cfg.py} \
        --object ${artifact}/${filename} --output "$TMPDIR/repeated/zesu-cfg.json" \
        --flame "$TMPDIR/repeated/flame.json" --proof-map "$TMPDIR/repeated/proof-map.json"
      cmp "$out/zesu-cfg.json" "$TMPDIR/repeated/zesu-cfg.json"
      cmp "$out/flame.json" "$TMPDIR/repeated/flame.json"
      cmp "$out/proof-map.json" "$TMPDIR/repeated/proof-map.json"
    '';
  zesuCfg = makeCfg "zesu-rv64-cfg-e5f8c13" zesuRv64Object "obj/zesu.o";
  zesuSszDecodeCfg = makeCfg "zesu-ssz-decode-rv64-cfg-e5f8c13" zesuSszDecodeRv64Elf "bin/zesu-ssz-decode";

  zesuSszDecodeLevel1Manifest = pkgs.runCommand "zesu-ssz-decode-level1-manifest-e5f8c13"
    { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_manifest.py} \
        --cfg ${zesuSszDecodeCfg}/zesu-cfg.json \
        --flame ${zesuSszDecodeCfg}/flame.json \
        --level 1 --output "$out/level1-manifest.json"
      python ${../tools/test_level_manifest.py} "$out/level1-manifest.json"
    '';

  zesuSszDecodeLevel1BoundaryBindings = pkgs.runCommand
    "zesu-ssz-decode-level1-boundary-bindings-e5f8c13" { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_level_boundary_bindings.py} \
        --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json \
        --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
        --output "$out/level1-boundary-bindings.json"
      python ${../tools/test_level_boundary_bindings.py} "$out/level1-boundary-bindings.json"
    '';

  zesuSszDecodeStatelessInputLayout = pkgs.runCommand
    "zesu-ssz-decode-stateless-input-layout-e5f8c13" { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_zig_type_layout.py} \
        --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
        --type input.StatelessInput --output "$out/stateless-input-layout.json"
      python ${../tools/test_zig_type_layout.py} "$out/stateless-input-layout.json"
    '';

  level1EvidenceTools = builtins.path {
    path = ../tools/level1_evidence;
    name = "zesu-level1-evidence-tools";
  };
  zesuSszDecodeLevel1Evidence = pkgs.runCommand "zesu-ssz-decode-level1-evidence-e5f8c13" {
    nativeBuildInputs = [ pkgs.gcc pkgs.glib pkgs.pkg-config pkgs.python3 pkgs.qemu-user ];
  } ''
    set -euo pipefail
    cp -R ${level1EvidenceTools} tools
    chmod -R u+w tools
    python -m unittest discover -s tools -p 'test_*.py'
    gcc -shared -fPIC -O2 -Wall -Wextra -Werror -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0) tools/qemu_trace_plugin.c -o trace.so
    snapshots=$(python -c 'import json; rows=json.load(open("${zesuSszDecodeLevel1Manifest}/level1-manifest.json"))["instances"]; print(",".join("snapshot="+str(row["entryPc"]) for row in rows))')
    ${rv64.qemuRiscv64} -plugin ./trace.so,out=minimal.trace,"$snapshots" ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode < ${targets.public.zesuSszDecodeSmoke}/minimal.ssz > /dev/null
    ${rv64.qemuRiscv64} -plugin ./trace.so,out=invalid.trace,"$snapshots" ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode < ${targets.public.zesuSszDecodeSmoke}/invalid.ssz > /dev/null
    mkdir -p "$out"
    python tools/analyze.py --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json \
      --bindings ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json \
      --elf ${zesuSszDecodeRv64Elf}/bin/zesu-ssz-decode \
      --trace minimal=minimal.trace --trace invalid=invalid.trace \
      --input minimal=${targets.public.zesuSszDecodeSmoke}/minimal.ssz \
      --input invalid=${targets.public.zesuSszDecodeSmoke}/invalid.ssz \
      --output "$out/level1-evidence.json"
  '';

  zesuCfgUi = pkgs.runCommand "zesu-rv64-cfg-ui-e5f8c13"
    { nativeBuildInputs = [ pkgs.python3 ]; } ''
    cp -R ${../tools/binary-regions-ui} "$out"
    chmod -R u+w "$out"
    cp ${zesuSszDecodeCfg}/zesu-cfg.json "$out/zesu-cfg.json"
    cp ${zesuSszDecodeCfg}/flame.json "$out/"
    cp ${zesuSszDecodeLevel1Manifest}/level1-manifest.json "$out/"
    cp ${zesuSszDecodeLevel1Evidence}/level1-evidence.json "$out/"
    cp ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json "$out/"
    cp ${zesuSszDecodeStatelessInputLayout}/stateless-input-layout.json "$out/"
    cp ${../tools/build_ssz_proof_map.py} build_ssz_proof_map.py
    cp ${../tools/test_ssz_proof_map.py} test_ssz_proof_map.py
    python build_ssz_proof_map.py --cfg ${zesuSszDecodeCfg}/zesu-cfg.json --flame ${zesuSszDecodeCfg}/flame.json --manifest ${zesuSszDecodeLevel1Manifest}/level1-manifest.json --evidence ${zesuSszDecodeLevel1Evidence}/level1-evidence.json --bindings ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json --output "$out/proof-map.json"
    python test_ssz_proof_map.py ${zesuSszDecodeCfg}/zesu-cfg.json ${zesuSszDecodeCfg}/flame.json ${zesuSszDecodeLevel1Manifest}/level1-manifest.json ${zesuSszDecodeLevel1Evidence}/level1-evidence.json ${zesuSszDecodeLevel1BoundaryBindings}/level1-boundary-bindings.json
    cp ${zesuCfg}/flame.json "$out/flame-full.json"
  '';
in
{
  public = {
    inherit dump stats zesuCfg zesuSszDecodeCfg zesuSszDecodeLevel1Manifest
      zesuSszDecodeLevel1BoundaryBindings
      zesuSszDecodeStatelessInputLayout
      zesuSszDecodeLevel1Evidence zesuCfgUi;
    machine-regions-ui = zesuCfgUi;
  };
}
