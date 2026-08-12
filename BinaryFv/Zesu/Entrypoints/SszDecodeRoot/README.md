# `ssz_decode_root.main`

`Level1Boundary.lean` states exact call boundaries, `Level1Contracts.lean` bundles the six unresolved
immediate contracts, and `Level0Contract.lean` composes those opaque calls with all 24 parent-owned
instructions. `Level2Contracts.lean` states the reviewed fixed-raw encoder contracts and the five
genuine encoder-call contracts for booleans, optional u64 values, byte-list arrays, byte slices, and
u64 values. The genuine-call contracts bind semantic values to entry registers and memory, and frame
their exact temporary stack windows; the larger inlined encoder regions require separate live-state
contracts. `HostExecution.lean` models the linked read/write/exit ecalls.
