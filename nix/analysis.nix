{ pkgs, rv64, targets }:
let
  inherit (rv64) riscvNm riscvObjdump riscvSize;
  zesuRv64Object = targets.public.zesuRv64Object;

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
  zesuCfg = pkgs.runCommand "zesu-rv64-cfg-d8071c4" {
    nativeBuildInputs = [ python ];
  } ''
    mkdir -p "$out"
    python ${../tools/generate_zesu_cfg.py} \
      --object ${zesuRv64Object}/obj/zesu.o --output "$out/zesu-cfg.json" \
      --flame "$out/flame.json" --proof-map "$out/proof-map.json"
    python ${../tools/test_zesu_cfg.py} "$out/zesu-cfg.json"
  '';

  zesuCfgUi = pkgs.runCommand "zesu-rv64-cfg-ui-d8071c4" { } ''
    cp -R ${../tools/binary-regions-ui} "$out"
    chmod -R u+w "$out"
    cp ${zesuCfg}/zesu-cfg.json "$out/zesu-cfg.json"
    cp ${zesuCfg}/flame.json ${zesuCfg}/proof-map.json "$out/"
  '';
in
{
  public = {
    inherit dump stats zesuCfg zesuCfgUi;
    machine-regions-ui = zesuCfgUi;
  };
}
