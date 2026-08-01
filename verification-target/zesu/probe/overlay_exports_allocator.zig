// ============================================================================================
// VALIDATION-ONLY OVERLAY (Row B, PR #45) for `src/zkvm/raw_allocator.zig` — appended by the
// `zesuContractProbe` nix derivation to a byte-identical, sha256-verified copy of the pinned source.
//
// It re-exports the bump allocator `zesu_raw_alloc` under a `probe_*` name so the host contract probe
// can test it DIRECTLY. `zesu_raw_alloc` is already `pub export`, so this alias only pins the identity
// for the probe's `comptime` existence proof; every line of the pinned source above this marker is
// unchanged. The host defines the `extern var ZKVM_HEAP_POS`/`ZKVM_HEAP_TOP` cursor/limit the
// allocator reads — the probe drives a *virtual* heap (arbitrary numeric addresses), because
// `zesu_raw_alloc` only does checked pointer arithmetic and never dereferences the heap.
//
// Compiled ONLY into the host-only `ssz-contract-probe`; never part of any production RV64 object.
// ============================================================================================

pub const probe_zesu_raw_alloc = zesu_raw_alloc;
