# Machine execution

`Level0MainSteps.lean` proves the concrete Sail instruction steps owned directly by Level 0. Multi-step
composition uses the repository's confined-trace/segment interfaces instead of transparent chains of
successor states.

`Level2RuntimeLeaves.lean` proves the selected closed Linux-runtime leaves used while converting
`Level2ContractAssumptions` into the six Level 1 contracts. Its `zkvm_exit` proof combines exact Sail
instructions with the endpoint model's explicit host `exit` transition; this mixed `EndpointState`
trace cannot use the Sail-only `Seg` interface.
