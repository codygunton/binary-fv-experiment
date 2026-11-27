# DTF `rlp_decode.decodeTxFields`: blocker evidence (S7 step 1)

Function `f_8000050c`, 2,825 instructions, entry `0x8000050c`. The map lists no static blocker
(only supported forms, no unresolved indirect transfer); the three items below are what the
heuristics resolved, with the evidence from the disassembly
(`llvm-objdump -d -M no-aliases`). Offsets are absolute addresses.

Calling convention (from the two callers, `0x8003d2b4` and `0x8003d414`): `a0` = result
(`anyerror!input.Transaction`, 0x128 bytes: the Transaction at `+0`, the u16 error code at
`+0x120`), `a1` = allocator object `{ctx, vtable}`, `a2` = `tx_type`, `a3`/`a4` = payload slice
`{ptr, len}`. Frame 0x370 bytes.

## Jump table at `0x80000584`

```
80000560  andi  a0, a2, 0xff          ; index = tx_type (u8)
80000564  auipc a1, 0x110
80000568  slli  a0, a0, 0x3
8000056c  addi  a1, a1, -0x514        ; base = 0x80110050 (.rodata)
80000570  add   a0, a1, a0
80000574  ld    a0, 0x0(a0)
80000584  jalr  zero, 0x0(a0)
```

| tx_type | table word (`0x80110050 + 8 i`) | target | source arm (`rlp_decode.zig`) |
|---|---|---|---|
| 0 | `0x80110050` | `0x80000588` | legacy |
| 1 | `0x80110058` | `0x8000081c` | EIP-2930 |
| 2 | `0x80110060` | `0x8000069c` | EIP-1559 |
| 3 | `0x80110068` | `0x8000075c` | EIP-4844 |
| 4 | `0x80110070` | `0x800005dc` | EIP-7702 |
| 5 | `0x80110078` | `0x80014504` | outside the function |

Index bound: there is **no** range check before the `jalr`; the source's `else => return
error.InvalidBlock` arm was removed by the compiler. Both callers guarantee `tx_type ≤ 4`:
`decodeSingleTx` (`rlp_decode.zig:276`: `if (tx_type == 0 or tx_type > 4) return
error.InvalidBlock`) and `decodeTxItem` (`:296`, same test; the list case passes `0`). So the
contract's `Pre` requires `tx_type ≤ 4`, and the `.jumpInd` leaf goal is closed by that fact
and `RodataLoaded` of the 40 table bytes. The five target addresses equal zesislar's
`PROVENANCE.md` count (five). The rodata `0x80110050:40` must be in the image.

## Indirect calls (11): all allocator vtable slots

Each target is loaded from the allocator vtable: the vtable pointer is the second word of the
allocator object (`ld s9, 0x8(s3)` at `0x8000188c`, `s3` = `a1` at entry; the other sites reload
it into `s2`/`s6` or from the spill slot `S-0x350`, `S` = entry `sp`). With `Pre` fixing that
word to `alt_fl_alloc.vtable` (`0x801136d8`, rodata, already in the image), every site has one
target:

| site | slot (`ld t, k(vtable)`) | callee |
|---|---|---|
| `0x80001704` | 0 (`k = 0`) | `alt_fl_alloc.alloc` |
| `0x8000179c` | 0 | `alt_fl_alloc.alloc` |
| `0x800018f8` | 0 | `alt_fl_alloc.alloc` |
| `0x80001994` | 0 | `alt_fl_alloc.alloc` |
| `0x80001a30` | 0 | `alt_fl_alloc.alloc` |
| `0x800029a4` | 2 (`k = 16`) | `alt_fl_alloc.remap` (F0) |
| `0x80002a04` | 0 | `alt_fl_alloc.alloc` |
| `0x80002a68` | 3 (`k = 24`) | `alt_fl_alloc.free` |
| `0x80002c64` | 0 | `alt_fl_alloc.alloc` |
| `0x80002f10` | 3 | `alt_fl_alloc.free` |
| `0x80002f50` | 2 | `alt_fl_alloc.remap` (F0) |

(Slots from the map's block-local evaluation; the table-heuristic candidate lists also contain
`Io.Writer`, `scratch_arena` and `host.JournalVTable` entries at the same slot, which `Pre`
excludes.) Source: `alloc.dupe` (`txBytesCopy`), the `ArrayListUnmanaged.append` growth and
`toOwnedSlice` of `txHashList`/`txAuthList`.

## Misaligned accesses (supported since S5 probe 3)

Loads from an RLP payload pointer (any byte offset of the input) and stores at odd offsets of
the result struct:

| sites | access | why misaligned |
|---|---|---|
| `0x80001164`..`0x8000116c`, `0x8000129c`..`0x800012a4`, `0x80001410`..`0x80001418`, `0x80001504`..`0x8000150c`, `0x800015f8`..`0x80001600` | `ld`, `ld`, `lw` | 20-byte `to` address copied from its payload (`txAddr`, one copy per tx type); PLATFORM.md's `ld a2,0(a1)` at `0x80001164` |
| `0x800020e8`..`0x800020f4` | four `ld` | 32-byte hash copied from its payload (`txHashList`) |
| `0x80002e00` | `sd zero, 0x21(a6)` | result: padding after `gas_priority_fee`'s tag |
| `0x80002e40` | `sw zero, 0xa9(a6)` | result: padding after `chain_id`'s tag byte (`+0xa8`) |
| `0x80002ea8`, `0x80002eac`, `0x80002eb0` | `sd`, `sd`, `sw` at `0x109`, `0x111`, `0x119` | result: the `?Address` `to` at `+0x109` |

`a6` is the result pointer. Aligned by construction (not counted): `0x800029b0` and
`0x80002f60` load the word at `0x8010fe00` (rodata `0x8e38e38e38e38e39`, the multiplier of a
division by 9 after `>> 4`, i.e. by 144 = the `AuthorizationTuple` size); `0x8010fe00:8` must be
in the image.
