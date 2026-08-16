# Level 2 contract repair proposal

PR #96 correctly selects 19 Level 2 function instances, but four shared contract schemas do not yet
describe executable entry states. The repair changes the entry predicates and their caller
construction. It does not add fields to `Level2ContractAssumptions`.

1. Add `frameSize ≤ callerStack` to `EncoderCallEntry`. Remove it as an unsupported exit-only
   requirement. Each concrete writer call proves it from its current stack pointer and literal child
   frame size.
2. Add caller-derived execution-access structures to `ConstantEncoderEntry`, `RawEncoderEntry`,
   `EncoderCallEntry`, and `InlineEncoderEntry`. Each structure must contain the configured-machine,
   retirement, PMA, MMIO, code-separation, read-access, and write-access facts used by that schema's
   first instruction and memory operations. Follow `MemcpyMachineAccess`. Do not add these facts as
   separate Level 2 assumptions.
3. Change the upper input arm of `DecodeBoundaryEntry` from
   `stackPointer ≤ inputAddress` to `stackPointer + 0x380 ≤ inputAddress`. Retain the lower disjoint
   arm. Prove both arms from the concrete Level 1 caller layout.
4. Prove one complete constant, raw, called, and inline encoder contract before accepting the other
   instances that share its schema. The representative proof must execute from the strengthened
   entry and establish the declared exit, bound, and frames.
5. Keep the 19 selected contracts in `Level2ContractAssumptions`. The theorem
   `level1Contracts_of_level2` must construct the strengthened entries at each concrete call site.
   `root_compliance` remains conditional on `hLevel2` until those 19 contracts are discharged.

The generated clause matrix is the admission gate. A schema remains `not-admitted` when it has a
contradiction, a missing execution fact, an incomplete empirical clause, or no representative proof.
Inline collection address bindings remain missing until a production trace or a proved caller fact
binds the live register or stack word to the represented collection.
