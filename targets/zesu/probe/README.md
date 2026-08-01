# Host contract probe

The host probe calls routines from the pinned Zig decoder directly. Its job is to test the
handwritten contract meanings before those meanings are used in machine-code proofs.

Most decoder routines are private to their Zig source files. The validation-only
[decoder](overlay_exports.zig), [allocator](overlay_exports_allocator.zig), and
[root-wrapper](overlay_exports_root.zig) overlays expose them inside the host probe build. Nix first
checks each pinned source hash, copies the source, and appends the corresponding overlay. Production
RV64 objects are built separately from untouched source, and the `sszProductionUnchanged` check pins
the hashes of all three shipped objects.

[ssz_contract_probe.zig](ssz_contract_probe.zig) supports whole-decoder corpus checks and typed
per-source function vectors. For allocating routines it records every allocation's order, size, alignment,
stable block identity, aliasing, and cleanup. Its out-of-memory sweep injects failure at every
recorded allocation when there are at most 256; larger ledgers use a fixed-stride sample and set
`oom_sampled` in the output. Host pointers are never written to evidence files, so results remain
deterministic across machines.
