{ packages }:
let
  checks = {
    inherit (packages)
      binaryFvLean
      dump
      rethKeccak
      stats
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
      sszContractProbeCheck
      zesuSinkObservability
      zesuSsz
      zesuValue;
    default = packages.stats;
  };

  apps = rec {
    reth-keccak = {
      type = "app";
      program = "${packages.rethKeccakRun}/bin/reth-keccak";
      meta.description = "Run the RV64IM_Zicclsm Reth RustCrypto Keccak-256 candidate";
    };
    zesu-ssz = {
      type = "app";
      program = "${packages.zesuSszRun}/bin/zesu-ssz";
      meta.description = "Run the RV64IM_Zicclsm Zesu raw SSZ decoder candidate";
    };
    stats = {
      type = "app";
      program = "${packages.stats}/bin/show-stats";
      meta.description = "Print reproducible RV64IM_Zicclsm stats for Keccak and SSZ";
    };
    dump = {
      type = "app";
      program = "${packages.dump}/bin/dump";
      meta.description = "Print RISC-V objdump -d for reth-keccak or zesu-ssz";
    };
    default = stats;
  };
in
{
  inherit apps checks;
}
