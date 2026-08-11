# Static classification of the uncovered occurrences (GENERATED)

Mechanically derived from the UNCHANGED production `zesu-ssz` disassembly (objdump); not from
test-run coverage. Diagnostic-only; never imported by the proof.

std.mem.Allocator VTable at `0x13f70`: alloc=`0x13768`, resize=`0x13760`, remap=`0x13030`, free=`0x10440`.
Indirect (jalr) calls index the vtable at offsets: `[0, 24]` (0=alloc, 8=resize, 16=remap, 24=free).

- **occ 135 `allocatorResize`** (entry 79712): statically unreachable — std.mem.Allocator resize slot (vtable+8); the vtable is indexed only at offsets [0, 24] by any indirect call and no direct jal targets it, so the decoder never calls allocator.resize (exact-size bump allocations never grow).
- **occ 123 `allocatorRemap`** (entry 77872): statically unreachable — std.mem.Allocator remap slot (vtable+16); the vtable is indexed only at offsets [0, 24] by any indirect call and no direct jal targets it, so the decoder never calls allocator.remap.
- **occ 137 `zesu_raw_error`** (entry 79744): statically unreachable — exported raw-ABI error getter; no jal/jalr/data pointer in the binary references its entry, so the sealed _start harness never calls it (it discriminates success/failure via zesu_raw_result's null return). No ABI surface to invoke it without relinking (forbidden).

All three statically unreachable: **True**. The production-evidence coverage claims exclude them.
