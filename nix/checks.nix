{ packages }:
let
  checks = {
    inherit (packages) binaryFvLean evmSailLeanExtraction zesuRv64Object zesuCfgUi;
    default = packages.binaryFvLean;
  };

  apps = rec {
    stats = {
      type = "app";
      program = "${packages.stats}/bin/show-stats";
      meta.description = "Print the pinned authentic Zesu RV64 object statistics";
    };
    dump = {
      type = "app";
      program = "${packages.dump}/bin/dump-zesu-rv64-object";
      meta.description = "Disassemble the pinned authentic Zesu RV64 object";
    };
    default = stats;
  };
in
{
  inherit apps checks;
}
