# `ssz_decode_root.main`

`Level1Boundary.lean` states exact call boundaries, `Level1Contracts.lean` bundles the six unresolved
immediate contracts, and `Level0Contract.lean` composes those opaque calls with all 24 parent-owned
instructions. `Level2Contracts.lean` states the reviewed fixed-raw encoder contract shape and its ten
exact generated callsites. `HostExecution.lean` models the linked read/write/exit ecalls.
