{ packages }:
let
  checks = {
    inherit (packages)
      binaryFvLean
      dump
      rethKeccak
      sha3
      stats
      tinfl
      zesuProductionObject
      zesuRawObject
      zesuSinkObservability
      zesuSsz
      zesuValue;
    default = packages.stats;
  };

  apps = rec {
    sha3 = {
      type = "app";
      program = "${packages.sha3Run}/bin/sha3";
      meta.description = "Run the RV64IM_Zicclsm SHA-3 binary under qemu-riscv64";
    };
    tinfl = {
      type = "app";
      program = "${packages.tinflRun}/bin/tinfl";
      meta.description = "Run the RV64IM_Zicclsm miniz tinfl binary under qemu-riscv64";
    };
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
      meta.description = "Print reproducible RV64IM_Zicclsm stats for all four evaluation targets";
    };
    dump = {
      type = "app";
      program = "${packages.dump}/bin/dump";
      meta.description = "Print RISC-V objdump -d for sha3, tinfl, reth-keccak, or zesu-ssz";
    };
    default = stats;
  };
in
{
  inherit apps checks;
}
