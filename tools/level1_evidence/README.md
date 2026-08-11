# Level 1 boundary evidence

The QEMU trace plugin observes the unchanged production RV64 ELF. The Nix target
zesuSszDecodeLevel1Evidence obtains snapshot PCs exclusively from the generated Level 1 manifest,
runs one successful and one rejected SSZ input, and records:

- all integer registers whenever an exercised Level 1 entry is reached;
- executed PCs and concrete load/store address, width, and value records;
- observed transitions leaving each generated Level 1 execution extent;
- the exact production ELF SHA-256 digest.

The analyzer requires the union of vectors to reach every selected Level 1 entry. Its tests reject a
different ELF, a deleted entry snapshot, and malformed records. The report is admission evidence,
not a theorem premise: it explicitly leaves universal path coverage, step bounds, complete register
and memory frames, and the semantic result relation unmeasured. Contract-specific checkers must add
source-probe expectations before any of those clauses can appear in Level1ContractAssumptions.
