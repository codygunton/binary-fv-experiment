{ pkgs, rv64, targets }:
let
  inherit (rv64) riscvNm riscvObjdump riscvSize;
  zesuRv64Object = targets.public.zesuRv64Object;
  zesuSszDecodeRv64Object = targets.public.zesuSszDecodeRv64Object;

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
  makeCfg = name: object: filename: pkgs.runCommand name { nativeBuildInputs = [ python ]; } ''
      mkdir -p "$out"
      python ${../tools/generate_zesu_cfg.py} \
        --object ${object}/obj/${filename} --output "$out/zesu-cfg.json" \
        --flame "$out/flame.json" --proof-map "$out/proof-map.json"
      python ${../tools/test_zesu_cfg.py} "$out/zesu-cfg.json"
      mkdir "$TMPDIR/repeated"
      python ${../tools/generate_zesu_cfg.py} \
        --object ${object}/obj/${filename} --output "$TMPDIR/repeated/zesu-cfg.json" \
        --flame "$TMPDIR/repeated/flame.json" --proof-map "$TMPDIR/repeated/proof-map.json"
      cmp "$out/zesu-cfg.json" "$TMPDIR/repeated/zesu-cfg.json"
      cmp "$out/flame.json" "$TMPDIR/repeated/flame.json"
      cmp "$out/proof-map.json" "$TMPDIR/repeated/proof-map.json"
    '';
  zesuCfg = makeCfg "zesu-rv64-cfg-6acdbd9" zesuRv64Object "zesu.o";
  zesuSszDecodeCfg = makeCfg "zesu-ssz-decode-rv64-cfg-6acdbd9" zesuSszDecodeRv64Object "zesu-ssz-decode.o";

  zesuCfgUi = pkgs.runCommand "zesu-rv64-cfg-ui-6acdbd9" { } ''
    cp -R ${../tools/binary-regions-ui} "$out"
    chmod -R u+w "$out"
    cp ${zesuSszDecodeCfg}/zesu-cfg.json "$out/zesu-cfg.json"
    cp ${zesuSszDecodeCfg}/flame.json ${zesuSszDecodeCfg}/proof-map.json "$out/"
    cp ${zesuCfg}/flame.json "$out/flame-full.json"
  '';
in
{
  public = {
    inherit dump stats zesuCfg zesuSszDecodeCfg zesuCfgUi;
    machine-regions-ui = zesuCfgUi;
  };
}
