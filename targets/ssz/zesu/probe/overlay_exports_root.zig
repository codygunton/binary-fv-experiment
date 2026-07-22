// ============================================================================================
// VALIDATION-ONLY OVERLAY (Row B, PR #45) for `src/zkvm/raw_decoder_root.zig` — appended by the
// `zesuContractProbe` nix derivation to a byte-identical, sha256-verified copy of the pinned source.
//
// It re-exports the file-private allocator vtable thunks and the allocator constructor under `probe_*`
// names so the host contract probe can test each DIRECTLY, and adds `probe_reset` so each vector runs
// against fresh decoder state — the module's `attempted`/`stored_result`/`last_status` globals persist
// across calls (the source deliberately allows one decode per heap reset). The exported
// `zesu_decode_raw`/`zesu_raw_result`/`zesu_raw_error` are already public and are called by name.
//
// Every line of the pinned source above this marker is unchanged. Compiled ONLY into the host-only
// `ssz-contract-probe`; never part of any production RV64 object derivation.
// ============================================================================================

pub const probe_allocatorAlloc = allocatorAlloc;
pub const probe_allocatorResize = allocatorResize;
pub const probe_allocatorRemap = allocatorRemap;
pub const probe_allocatorFree = allocatorFree;
pub const probe_allocator = allocator;

/// Reset the one-shot decode state so each per-routine vector runs fresh.
pub fn probe_reset() void {
    attempted = false;
    stored_result = null;
    last_status = .not_run;
}
