# Host contract probe

The host probe calls routines from the pinned Zig decoder directly. Its job is to test the
handwritten contract meanings before those meanings are used in machine-code proofs.

Most decoder routines are private to their Zig source files. The `overlay_exports*.zig` files expose
them only inside the host probe build. Nix first verifies each pinned source hash, copies the file,
and appends the overlay. Production RV64 objects are built separately from untouched source, and a
byte-hash guard verifies that the validation overlay did not leak into them.

`ssz_contract_probe.zig` supports whole-decoder corpus checks and typed per-routine vectors. For
allocating routines it records every allocation's order, size, alignment, stable block identity,
aliasing, and cleanup, then tests failure at each relevant allocation point. Host pointers are never
written to evidence files, so results remain deterministic across machines.
