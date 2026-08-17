# Machine execution

`Level0MainSteps.lean` proves the concrete Sail instruction steps owned directly by Level 0. Multi-step
composition uses the repository's confined-trace/segment interfaces instead of transparent chains of
successor states.

`Level2RuntimeLeaves.lean` proves the closed bare-metal read, allocator, `memcpy`, write-output, and
exit regions used while converting `Level2ContractAssumptions` into the six Level 1 contracts.
`Level1WriteSuccessSteps.lean` uses `Seg` for parent-owned instruction sequences and consumes the
selected Level 2 encoder contracts without exposing transparent successor-state chains.
