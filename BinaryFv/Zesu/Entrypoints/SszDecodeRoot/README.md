# `ssz_decode_root.main`

`Level1Boundary.lean` states exact call boundaries, `Level1Contracts.lean` bundles the six immediate
immediate contracts, and `Level0Contract.lean` composes those opaque calls with all 24 parent-owned
instructions. `Level2Contracts.lean` states the reviewed fixed-raw encoder contracts and the five
genuine encoder-call contracts for booleans, optional u64 values, byte-list arrays, byte slices, and
u64 values. The genuine-call contracts bind semantic values to entry registers and memory, and frame
their exact temporary stack windows; the larger inlined encoder regions require separate live-state
contracts. The same file states the shared emitted `memcpy` contract, including nonoverlapping source
and destination windows, byte-copy semantics, and its exact generated return set. `HostExecution.lean`
models the three distinguished bare-metal read, write, and exit instructions on top of their real
Sail machine steps. The three optimized transaction, withdrawal, and hash-array
regions use separate inline contracts: their live count registers and decoded array representations
are explicit, their writes are confined to the existing 2,000-byte `writeSuccess` frame, and no
source-function ABI is assumed.

`Level2ContractAssumptions` is the current proof-progress gauge: it contains exactly the 19
unresolved generated instances above. `Level2Refinement.lean` proves
`level1Contracts_of_level2`, filling the bare-metal read and exit leaves, allocator leaf, and
`memcpy` unconditionally before deriving all six Level 1 contracts. `Root.lean` calls that edge
explicitly from its sole `hLevel2` premise.
