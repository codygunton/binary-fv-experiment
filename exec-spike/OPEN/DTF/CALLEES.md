# DTF `rlp_decode.decodeTxFields`: callees (S7 step 3)

From `zmap show f_8000050c` (static map; states from `map/map.json` at `501f89f0`) and
`OPEN/DTF/BLOCKERS.md` (the 11 indirect calls resolve to allocator vtable slots once `Pre` fixes
the vtable; the map's other table-heuristic candidates are excluded).

| callee | id | calls | state | note |
|---|---|---|---|---|
| `rlp.decodeItem` | F2 `f_800d6960` | 63 direct | closed+compliance | |
| `memcpy` | `f_800e06c0` | 7 direct | assumed (service) | `ziskMemcpy` |
| `rlp_decode.txAccessList` | TX `f_80000000` | 4 direct (`0x80001a6c`, `0x80001c94`, `0x80001d50`, `0x80001ec0`: one per typed arm) | **not closed** (waiting) | see below |
| `array_list.Aligned([32]u8,null).ensureTotalCapacity` | F1 `f_800cb40c` | 1 direct | closed+sail | `txHashList` growth |
| `array_list.Aligned([32]u8,null).toOwnedSlice` | F4 `f_800d677c` | 1 direct | closed+sail | `txHashList` result |
| `alt_fl_alloc.alloc` | `f_80042494` | 7 indirect (slot 0) | assumed | `AllocAssumptions` |
| `alt_fl_alloc.remap` | F0 `f_8004218c` | 2 indirect (slot 2) | closed+sail | |
| `alt_fl_alloc.free` | `f_80041f38` | 2 indirect (slot 3) | assumed | `AllocAssumptions` |

## Not closed, bottom-up

1. **TX `rlp_decode.txAccessList`** (`f_80000000`): 323 instructions, 2 loops (heads
   `0x800000c4`, `0x8000018c`), 15 cut points, 11 joins, `leaves_estimate` 53, no static blocker
   (its misaligned input loads and keys-buffer stores are supported since S5 probe 3). Its own
   callees are all closed or assumed (F2, F1, F4, F5, F0, alloc, free, memcpy). zesislar contract:
   yes, `ZesuSsz/Contracts/TxAccessListContract.v`, transcribed as `ZesuExec/Fn/TX/Spec.lean`
   (transcribed/unreviewed). Cut design: `OPEN/TX/CUTS.md`. It is S6's function, so DTF waits
   on S6 and no other callee.

No other callee of DTF is open.
