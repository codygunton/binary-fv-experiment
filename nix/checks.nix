{ packages }:
let
  checks = {
    inherit (packages)
      binaryFvLean
      dump
      stats
      zesuProductionObject
      zesuRawObject
      zesuRawSidecar
      zesuRuntimeSidecar
      elflingProgram
      elflingDecoderLlvmIr
      elflingRelocationCheck
      elflingGeneratorDefectsCheck
      zesuSinkObservability
      zesuSsz
      zesuValue;
    default = packages.stats;
  };

  apps = rec {
    zesu-ssz = {
      type = "app";
      program = "${packages.zesuSszRun}/bin/zesu-ssz";
      meta.description = "Run the RV64IM_Zicclsm Zesu raw SSZ decoder candidate";
    };
    stats = {
      type = "app";
      program = "${packages.stats}/bin/show-stats";
      meta.description = "Print reproducible RV64IM_Zicclsm stats for the SSZ target";
    };
    dump = {
      type = "app";
      program = "${packages.dump}/bin/dump";
      meta.description = "Print RISC-V objdump -d for zesu-ssz";
    };
    default = stats;
  };
in
{
  inherit apps checks;
}
