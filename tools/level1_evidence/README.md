# Level 1 boundary evidence

The QEMU trace plugin observes the unchanged production RV64 ELF. The Nix target
zesuSszDecodeLevel1Evidence obtains snapshot PCs exclusively from the generated Level 1 manifest,
runs one successful and one rejected SSZ input, and records:

- all integer registers whenever an exercised Level 1 entry is reached;
- declared register-binding checkpoints inside an instance. The current checkpoint proves that
  `ssz.decode` has `x8 = entry x10` after its prologue at `0x121ac`;
- the first result store at `0x1230c`, including its eight-byte width and exact `entry x10` address;
- executed PCs and concrete load/store address, width, and value records;
- observed transitions leaving each generated Level 1 execution extent;
- the exact observed dynamic interval from `ssz.decode` entry to `writeSuccess` or `writeFailure`,
  including its step count, changed integer registers, and success result address;
- the exact production ELF SHA-256 digest.

The analyzer requires the union of vectors to reach every selected Level 1 entry. Its tests reject a
different ELF, a deleted entry snapshot, a missing binding checkpoint, a forged binding, a deleted
result store, and malformed records. The report is admission evidence, not a theorem premise. It
leaves universal path coverage, step bounds, complete register and memory frames, and the semantic
result relation unmeasured. Contract-specific checkers must add source-probe expectations before
those clauses can appear in `Level1ContractAssumptions`.
