# Level 3 direct-discharge review

This report classifies every proposed Level 3 instance. `direct-now` instances have no
unresolved child proof. `direct-after-dependencies` instances become direct proofs after
the named shared leaf or wrapper proof exists. `retain-contract` instances keep a Level 3
assumption because they contain a runtime loop, a large parser, or an unresolved allocator.
The validator also accepts a shared concrete body when the core flame metadata records its
machine owner at expanded call sites. The current tree uses this form for `fi:1:43a9`.

Counts: 8 direct now; 25 direct after shared dependencies; 15 parent-composed inline instances; 9 retained contracts.

| Instance | Source operation | Entry | Execution | Owned | Observed | Decision | Reason |
|---|---|---:|---:|---:|---:|---|---|
| `fi:1:2ff8` | `ssz.readU32` | `0x12734` | 11 | 0 | 34 | direct-after-dependencies | wrapper around the shared mem.readInt leaf |
| `fi:1:3064` | `ssz.readU32` | `0x128cc` | 10 | 0 | 34 | direct-after-dependencies | wrapper around the shared mem.readInt leaf |
| `fi:1:30e2` | `ssz.readU32` | `0x12944` | 10 | 0 | 34 | direct-after-dependencies | wrapper around the shared mem.readInt leaf |
| `fi:1:3335` | `ssz.readU32` | `0x12c18` | 4 | 0 | 34 | direct-after-dependencies | wrapper around the shared mem.readInt leaf |
| `fi:1:3457` | `ssz.readU32` | `0x12ff0` | 10 | 0 | 34 | direct-after-dependencies | wrapper around the shared mem.readInt leaf |
| `fi:1:3a74` | `ssz.decodeWithdrawal` | `0x145d0` | 129 | 63 | 1 | direct-after-dependencies | fixed-record decoder with three shared mem.readInt children |
| `fi:1:3b27` | `ssz.readU32` | `0x1484c` | 11 | 0 | 34 | direct-after-dependencies | wrapper around the shared mem.readInt leaf |
| `fi:1:3d8b` | `extern_io.write_output` | `0x14e2c` | 16 | 3 | 34 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:3db4` | `extern_io.write_output` | `0x14e3c` | 16 | 3 | 34 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:3ddd` | `extern_io.write_output` | `0x14e4c` | 16 | 3 | 34 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:3e06` | `extern_io.write_output` | `0x14e5c` | 16 | 3 | 34 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:3e2f` | `extern_io.write_output` | `0x14e6c` | 16 | 3 | 34 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:3e81` | `extern_io.write_output` | `0x14ed8` | 16 | 3 | 34 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:3ec4` | `ssz_decode_observation.Encoder.int` | `0x150dc` | 18 | 0 | 2 | direct-after-dependencies | wrapper around mem.writeInt and Encoder.raw |
| `fi:1:3f5b` | `ssz_decode_observation.Encoder.optionalU128` | `0x15118` | 47 | 12 | 2 | direct-after-dependencies | 12 owned instructions around reviewed Boolean and integer encoders |
| `fi:1:3f94` | `ssz_decode_observation.Encoder.optionalAddress` | `0x15158` | 41 | 13 | 2 | direct-after-dependencies | 13 owned instructions around reviewed Boolean and raw encoders |
| `fi:1:4045` | `ssz_decode_observation.Encoder.raw` | `0x15548` | 17 | 0 | 1 | direct-after-dependencies | wrapper around extern_io.write_output |
| `fi:1:40c3` | `ssz_decode_observation.Encoder.raw` | `0x156c0` | 17 | 0 | 1 | direct-after-dependencies | wrapper around extern_io.write_output |
| `fi:1:4101` | `extern_io.write_output` | `0x15730` | 16 | 3 | 34 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:412a` | `ssz_decode_observation.Encoder.raw` | `0x158c4` | 17 | 0 | 1 | direct-after-dependencies | wrapper around extern_io.write_output |
| `fi:1:42a2` | `ssz_decode_observation.Encoder.raw` | `0x15bac` | 17 | 0 | 34 | direct-after-dependencies | wrapper around extern_io.write_output |
| `fi:1:43a9` | `ssz_decode_observation.Encoder.int` | `0x15cb0` | 26 | 5 | 2 | direct-after-dependencies | wrapper around mem.writeInt and Encoder.raw |
| `fi:1:4494` | `ssz_decode_observation.Encoder.int` | `0x15ce4` | 24 | 5 | 2 | direct-after-dependencies | wrapper around mem.writeInt and Encoder.raw |
| `fi:1:45f6` | `ssz_decode_observation.Encoder.raw` | `0x15d1c` | 17 | 0 | 34 | direct-after-dependencies | wrapper around extern_io.write_output |
| `fi:1:49b1` | `extern_io.write_output` | `0x161c0` | 18 | 5 | 3 | direct-after-dependencies | 3-5 owned instructions around the proved write_output leaf |
| `fi:1:2fa7` | `mem.readInt` | `0x121c4` | 10 | 10 | 37 | direct-now | ten-instruction leaf; prove one shared fixed-width read theorem |
| `fi:1:2fe4` | `ssz.forkNameFromSchemaByte` | `0x1221c` | 12 | 12 | 36 | direct-now | twelve-instruction leaf with finite result branches |
| `fi:1:34fd` | `ssz.decode__struct_1051.f` | `0x13098` | 7 | 7 | 34 | direct-now | leaf wrapper with 6-17 instructions |
| `fi:1:351c` | `ssz.decode__struct_1051.f` | `0x130b0` | 6 | 6 | 34 | direct-now | leaf wrapper with 6-17 instructions |
| `fi:1:3541` | `ssz.decode__struct_1051.f` | `0x130c8` | 13 | 13 | 34 | direct-now | leaf wrapper with 6-17 instructions |
| `fi:1:3566` | `ssz.decode__struct_1051.f` | `0x13100` | 17 | 17 | 34 | direct-now | leaf wrapper with 6-17 instructions |
| `fi:1:358b` | `ssz.decode__struct_1051.f` | `0x13144` | 16 | 16 | 33 | direct-now | leaf wrapper with 6-17 instructions |
| `fi:1:45b2` | `mem.writeInt` | `0x15d18` | 1 | 1 | 34 | direct-now | one-instruction leaf; reuse the staged store contract |
| `fi:1:1999` | `ssz.decodeByteListList` | `0x10214` | 298 | 81 | 34 | retain-contract | runtime-sized offset loop and allocator descendants |
| `fi:1:340d` | `mem.Allocator.alloc__anon_1045` | `0x12e90` | 205 | 0 | 34 | retain-contract | allocator subtree delegates to allocAdvancedWithRetAddr |
| `fi:1:386d` | `mem.Allocator.alloc__anon_1173` | `0x13ef4` | 344 | 0 | 34 | retain-contract | allocator subtree delegates to allocAdvancedWithRetAddr |
| `fi:1:3940` | `rlp_decode.decodeSingleTx` | `0x14258` | 3146 | 63 | 2 | retain-contract | large RLP subtree with several parser children |
| `fi:1:39b7` | `mem.Allocator.alloc__anon_1432` | `0x14560` | 173 | 0 | 34 | retain-contract | allocator subtree delegates to allocAdvancedWithRetAddr |
| `fi:1:3fdd` | `ssz_decode_observation.Encoder.accessList` | `0x151c8` | 158 | 118 | 2 | retain-contract | runtime-sized collection encoder |
| `fi:1:406f` | `ssz_decode_observation.Encoder.authorizations` | `0x15578` | 87 | 38 | 2 | retain-contract | runtime-sized collection encoder |
| `fi:1:5a81` | `mem.Allocator.alloc__anon_1151` | `0x170b4` | 197 | 16 | 34 | retain-contract | allocator subtree delegates to allocAdvancedWithRetAddr |
| `fi:1:5b8d` | `mem.Allocator.dupe__anon_1128` | `0x17154` | 206 | 25 | 34 | retain-contract | allocator copy has allocation and memcpy descendants |

## Parent-composed inline instances

These source instances must compose with their Level 2 parent state. The integer-reader
instructions interleave with `sszDecode`. The raw-encoder tail consumes the `Encoder.bytes`
caller frame while it restores registers and the stack pointer.

| Instance | Source operation | Entry | Scheduled instructions |
|---|---|---:|---:|
| `fi:1:4350` | `ssz_decode_observation.Encoder.raw` | `0x15c90` | 21 |
| `fi:1:3167` | `ssz.readU32` | `0x129cc` | 10 |
| `fi:1:31b1` | `ssz.readU32` | `0x129f0` | 11 |
| `fi:1:3203` | `ssz.readU64` | `0x12a4c` | 24 |
| `fi:1:32f5` | `ssz.readU32` | `0x12ae8` | 11 |
| `fi:1:327b` | `ssz.readU64` | `0x12df4` | 24 |
| `fi:1:34c1` | `ssz.readU32` | `0x1305c` | 10 |
| `fi:1:35ab` | `ssz.readU64` | `0x138b8` | 15 |
| `fi:1:361f` | `ssz.readU64` | `0x138f4` | 16 |
| `fi:1:3693` | `ssz.readU32` | `0x13934` | 14 |
| `fi:1:36dd` | `ssz.readU64` | `0x1398c` | 16 |
| `fi:1:3731` | `ssz.readU64` | `0x139f4` | 12 |
| `fi:1:37a5` | `ssz.readU64` | `0x13a24` | 12 |
| `fi:1:37cf` | `ssz.readU32` | `0x13ce0` | 11 |
| `fi:1:3823` | `ssz.readU64` | `0x13cf0` | 23 |

## Recommended proof order

1. Prove generic `mem.readInt`, the staged `mem.writeInt`, and the five struct-field leaves.
2. Discharge the standalone `ssz.readU32` and `extern_io.write_output` wrappers.
3. Compose the scheduled `ssz.readU32` and `ssz.readU64` fragments inside `sszDecode`.
4. Discharge `Encoder.raw`, then `Encoder.int`, then the two optional encoders.
5. Discharge `ssz.decodeWithdrawal` with the shared integer-read theorem.
6. Design assumptions only for the nine retained instances.

A direct proof still needs a local semantic theorem statement. It avoids exposing that
statement as an `hLevel3` premise and avoids a second refinement level for the wrapper.
