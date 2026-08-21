import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyProof
import BinaryFv.Zesu.MachineExecution.Level0MainSteps
import BinaryFv.RiscV.Elfling.Seg
import BinaryFv.Zesu.Staging.MemWriteInt
import BinaryFv.Zesu.Staging.MemReadInt
import BinaryFv.Zesu.Staging.ReadU32
import BinaryFv.Zesu.Staging.ForkName
import BinaryFv.Zesu.Staging.CheckedSlice
import BinaryFv.Zesu.Staging.WriteOutput
import BinaryFv.Zesu.Staging.RawEncoder
import BinaryFv.Zesu.Staging.IntegerEncoder
import BinaryFv.Zesu.Staging.BooleanEncoder
import BinaryFv.Zesu.Staging.OptionalEncoder

/-!
# Generated hLevel3 staging

This file is not in the production import tree. Each contract definition is a reviewed
design hole. Each refinement theorem is a machine-proof hole with generated guidance.
-/

namespace BinaryFv.Zesu.Staging.HLevel3

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

/--
Contract design hole for `fi:1:1999` at `0x10214`.
Source operation: Decode one SSZ variable-list offset table into represented byte slices.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and the pinned EVM-Sail SSZ
decoder`.
Family: `byte-list-list-decode`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decodeByteListList_fi_1_1999_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:2fa7` at `0x121c4`.
Source operation: Read a fixed-width little-endian integer from the represented source window.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and zig/std/mem.zig`.
Family: `read-integer`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_mem_readInt_fi_1_2fa7_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_mem_readInt_fi_1_2fa7_Contract

/--
Contract design hole for `fi:1:2fe4` at `0x1221c`.
Source operation: Map the schema byte to the reviewed fork-name result or rejection.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig`.
Family: `fork-name`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_forkNameFromSchemaByte_fi_1_2fe4_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_forkNameFromSchemaByte_fi_1_2fe4_Contract

/--
Contract design hole for `fi:1:2ff8` at `0x12734`.
Source operation: Read a fixed-width little-endian integer from the represented source window.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and zig/std/mem.zig`.
Family: `read-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_readU32_fi_1_3064`, `ssz_readU32_fi_1_30e2`,
`ssz_readU32_fi_1_3335`, `ssz_readU32_fi_1_3457`, `ssz_readU32_fi_1_3b27`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_readU32_fi_1_2ff8_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_readU32_fi_1_2ff8_Contract

/--
Contract design hole for `fi:1:3064` at `0x128cc`.
Source operation: Read a fixed-width little-endian integer from the represented source window.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and zig/std/mem.zig`.
Family: `read-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_readU32_fi_1_2ff8`, `ssz_readU32_fi_1_30e2`,
`ssz_readU32_fi_1_3335`, `ssz_readU32_fi_1_3457`, `ssz_readU32_fi_1_3b27`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_readU32_fi_1_3064_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_readU32_fi_1_3064_Contract

/--
Contract design hole for `fi:1:30e2` at `0x12944`.
Source operation: Read a fixed-width little-endian integer from the represented source window.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and zig/std/mem.zig`.
Family: `read-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_readU32_fi_1_2ff8`, `ssz_readU32_fi_1_3064`,
`ssz_readU32_fi_1_3335`, `ssz_readU32_fi_1_3457`, `ssz_readU32_fi_1_3b27`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_readU32_fi_1_30e2_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_readU32_fi_1_30e2_Contract

/--
Contract design hole for `fi:1:3335` at `0x12c18`.
Source operation: Read a fixed-width little-endian integer from the represented source window.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and zig/std/mem.zig`.
Family: `read-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_readU32_fi_1_2ff8`, `ssz_readU32_fi_1_3064`,
`ssz_readU32_fi_1_30e2`, `ssz_readU32_fi_1_3457`, `ssz_readU32_fi_1_3b27`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_readU32_fi_1_3335_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_readU32_fi_1_3335_Contract

/--
Contract design hole for `fi:1:340d` at `0x12e90`.
Source operation: Allocate an aligned byte window with the requested size.
Source reference: `zig/std/mem/Allocator.zig`.
Family: `allocator-alloc`.
Boundary bindings: `n=x22`.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_mem_Allocator_alloc__anon_1045_fi_1_340d_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:3457` at `0x12ff0`.
Source operation: Read a fixed-width little-endian integer from the represented source window.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and zig/std/mem.zig`.
Family: `read-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_readU32_fi_1_2ff8`, `ssz_readU32_fi_1_3064`,
`ssz_readU32_fi_1_30e2`, `ssz_readU32_fi_1_3335`, `ssz_readU32_fi_1_3b27`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_readU32_fi_1_3457_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_readU32_fi_1_3457_Contract

/--
Contract design hole for `fi:1:34fd` at `0x13098`.
Source operation: Select one execution-request byte slice from the checked offset table.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig`.
Family: `checked-slice-selection`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode__struct_1051_f_fi_1_351c`,
`ssz_decode__struct_1051_f_fi_1_3541`, `ssz_decode__struct_1051_f_fi_1_3566`,
`ssz_decode__struct_1051_f_fi_1_358b`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode__struct_1051_f_fi_1_34fd_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode__struct_1051_f_fi_1_34fd_Contract

/--
Contract design hole for `fi:1:351c` at `0x130b0`.
Source operation: Select one execution-request byte slice from the checked offset table.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig`.
Family: `checked-slice-selection`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode__struct_1051_f_fi_1_34fd`,
`ssz_decode__struct_1051_f_fi_1_3541`, `ssz_decode__struct_1051_f_fi_1_3566`,
`ssz_decode__struct_1051_f_fi_1_358b`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode__struct_1051_f_fi_1_351c_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode__struct_1051_f_fi_1_351c_Contract

/--
Contract design hole for `fi:1:3541` at `0x130c8`.
Source operation: Select one execution-request byte slice from the checked offset table.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig`.
Family: `checked-slice-selection`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode__struct_1051_f_fi_1_34fd`,
`ssz_decode__struct_1051_f_fi_1_351c`, `ssz_decode__struct_1051_f_fi_1_3566`,
`ssz_decode__struct_1051_f_fi_1_358b`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode__struct_1051_f_fi_1_3541_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode__struct_1051_f_fi_1_3541_Contract

/--
Contract design hole for `fi:1:3566` at `0x13100`.
Source operation: Select one execution-request byte slice from the checked offset table.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig`.
Family: `checked-slice-selection`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode__struct_1051_f_fi_1_34fd`,
`ssz_decode__struct_1051_f_fi_1_351c`, `ssz_decode__struct_1051_f_fi_1_3541`,
`ssz_decode__struct_1051_f_fi_1_358b`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode__struct_1051_f_fi_1_3566_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode__struct_1051_f_fi_1_3566_Contract

/--
Contract design hole for `fi:1:358b` at `0x13144`.
Source operation: Select one execution-request byte slice from the checked offset table.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig`.
Family: `checked-slice-selection`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode__struct_1051_f_fi_1_34fd`,
`ssz_decode__struct_1051_f_fi_1_351c`, `ssz_decode__struct_1051_f_fi_1_3541`,
`ssz_decode__struct_1051_f_fi_1_3566`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode__struct_1051_f_fi_1_358b_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode__struct_1051_f_fi_1_358b_Contract

/--
Contract design hole for `fi:1:386d` at `0x13ef4`.
Source operation: Allocate an aligned byte window with the requested size.
Source reference: `zig/std/mem/Allocator.zig`.
Family: `allocator-alloc`.
Boundary bindings: `n=x23`.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_mem_Allocator_alloc__anon_1173_fi_1_386d_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:3940` at `0x14258`.
Source operation: Decode one transaction RLP item into the Zesu transaction representation.
Source reference: `deps/zesu/src/stateless/rlp_decode.zig and the pinned EVM-Sail transaction
decoder`.
Family: `transaction-decode`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_rlp_decode_decodeSingleTx_fi_1_3940_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:39b7` at `0x14560`.
Source operation: Allocate an aligned byte window with the requested size.
Source reference: `zig/std/mem/Allocator.zig`.
Family: `allocator-alloc`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_mem_Allocator_alloc__anon_1432_fi_1_39b7_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:3a74` at `0x145d0`.
Source operation: Decode one fixed-size SSZ withdrawal record.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and the pinned EVM-Sail SSZ
decoder`.
Family: `withdrawal-decode`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decodeWithdrawal_fi_1_3a74_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:3b27` at `0x1484c`.
Source operation: Read a fixed-width little-endian integer from the represented source window.
Source reference: `deps/zesu/src/stateless/stateless/ssz.zig and zig/std/mem.zig`.
Family: `read-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_readU32_fi_1_2ff8`, `ssz_readU32_fi_1_3064`,
`ssz_readU32_fi_1_30e2`, `ssz_readU32_fi_1_3335`, `ssz_readU32_fi_1_3457`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_readU32_fi_1_3b27_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_readU32_fi_1_3b27_Contract

/--
Contract design hole for `fi:1:3d8b` at `0x14e2c`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3db4`,
`extern_io_write_output_fi_1_3ddd`, `extern_io_write_output_fi_1_3e06`,
`extern_io_write_output_fi_1_3e2f`, `extern_io_write_output_fi_1_3e81`,
`extern_io_write_output_fi_1_4101`, `extern_io_write_output_fi_1_49b1`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_3d8b_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_3d8b_Contract

/--
Contract design hole for `fi:1:3db4` at `0x14e3c`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3d8b`,
`extern_io_write_output_fi_1_3ddd`, `extern_io_write_output_fi_1_3e06`,
`extern_io_write_output_fi_1_3e2f`, `extern_io_write_output_fi_1_3e81`,
`extern_io_write_output_fi_1_4101`, `extern_io_write_output_fi_1_49b1`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_3db4_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_3db4_Contract

/--
Contract design hole for `fi:1:3ddd` at `0x14e4c`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3d8b`,
`extern_io_write_output_fi_1_3db4`, `extern_io_write_output_fi_1_3e06`,
`extern_io_write_output_fi_1_3e2f`, `extern_io_write_output_fi_1_3e81`,
`extern_io_write_output_fi_1_4101`, `extern_io_write_output_fi_1_49b1`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_3ddd_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_3ddd_Contract

/--
Contract design hole for `fi:1:3e06` at `0x14e5c`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3d8b`,
`extern_io_write_output_fi_1_3db4`, `extern_io_write_output_fi_1_3ddd`,
`extern_io_write_output_fi_1_3e2f`, `extern_io_write_output_fi_1_3e81`,
`extern_io_write_output_fi_1_4101`, `extern_io_write_output_fi_1_49b1`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_3e06_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_3e06_Contract

/--
Contract design hole for `fi:1:3e2f` at `0x14e6c`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3d8b`,
`extern_io_write_output_fi_1_3db4`, `extern_io_write_output_fi_1_3ddd`,
`extern_io_write_output_fi_1_3e06`, `extern_io_write_output_fi_1_3e81`,
`extern_io_write_output_fi_1_4101`, `extern_io_write_output_fi_1_49b1`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_3e2f_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_3e2f_Contract

/--
Contract design hole for `fi:1:3e81` at `0x14ed8`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3d8b`,
`extern_io_write_output_fi_1_3db4`, `extern_io_write_output_fi_1_3ddd`,
`extern_io_write_output_fi_1_3e06`, `extern_io_write_output_fi_1_3e2f`,
`extern_io_write_output_fi_1_4101`, `extern_io_write_output_fi_1_49b1`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_3e81_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_3e81_Contract

/--
Contract design hole for `fi:1:3f5b` at `0x15118`.
Source operation: Append the canonical tagged encoding of one optional value.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-optional`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract

/--
Contract design hole for `fi:1:3f94` at `0x15158`.
Source operation: Append the canonical tagged encoding of one optional value.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-optional`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract

/--
Contract design hole for `fi:1:3fdd` at `0x151c8`.
Source operation: Append the canonical observation encoding of one structured collection.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-collection`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_accessList_fi_1_3fdd_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:4045` at `0x15548`.
Source operation: Append one represented byte window to the observation output.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-raw`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode_observation_Encoder_raw_fi_1_40c3`,
`ssz_decode_observation_Encoder_raw_fi_1_412a`, `ssz_decode_observation_Encoder_raw_fi_1_42a2`,
`ssz_decode_observation_Encoder_raw_fi_1_45f6`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_raw_fi_1_4045_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_raw_fi_1_4045_Contract

/--
Contract design hole for `fi:1:406f` at `0x15578`.
Source operation: Append the canonical observation encoding of one structured collection.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-collection`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_authorizations_fi_1_406f_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:40c3` at `0x156c0`.
Source operation: Append one represented byte window to the observation output.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-raw`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode_observation_Encoder_raw_fi_1_4045`,
`ssz_decode_observation_Encoder_raw_fi_1_412a`, `ssz_decode_observation_Encoder_raw_fi_1_42a2`,
`ssz_decode_observation_Encoder_raw_fi_1_45f6`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_raw_fi_1_40c3_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_raw_fi_1_40c3_Contract

/--
Contract design hole for `fi:1:4101` at `0x15730`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3d8b`,
`extern_io_write_output_fi_1_3db4`, `extern_io_write_output_fi_1_3ddd`,
`extern_io_write_output_fi_1_3e06`, `extern_io_write_output_fi_1_3e2f`,
`extern_io_write_output_fi_1_3e81`, `extern_io_write_output_fi_1_49b1`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_4101_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_4101_Contract

/--
Contract design hole for `fi:1:412a` at `0x158c4`.
Source operation: Append one represented byte window to the observation output.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-raw`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode_observation_Encoder_raw_fi_1_4045`,
`ssz_decode_observation_Encoder_raw_fi_1_40c3`, `ssz_decode_observation_Encoder_raw_fi_1_42a2`,
`ssz_decode_observation_Encoder_raw_fi_1_45f6`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_raw_fi_1_412a_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_raw_fi_1_412a_Contract

/--
Contract design hole for `fi:1:42a2` at `0x15bac`.
Source operation: Append one represented byte window to the observation output.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-raw`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode_observation_Encoder_raw_fi_1_4045`,
`ssz_decode_observation_Encoder_raw_fi_1_40c3`, `ssz_decode_observation_Encoder_raw_fi_1_412a`,
`ssz_decode_observation_Encoder_raw_fi_1_45f6`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_raw_fi_1_42a2_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_raw_fi_1_42a2_Contract

/--
Contract design hole for `fi:1:43a9` at `0x15cb0`.
Source operation: Append one fixed-width integer to the observation output.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode_observation_Encoder_int_fi_1_4494`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_int_fi_1_43a9_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_int_fi_1_43a9_Contract

/--
Contract design hole for `fi:1:4494` at `0x15ce4`.
Source operation: Append one fixed-width integer to the observation output.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-integer`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode_observation_Encoder_int_fi_1_43a9`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_int_fi_1_4494_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_int_fi_1_4494_Contract

/--
Contract design hole for `fi:1:45b2` at `0x15d18`.
Source operation: Write one fixed-width little-endian integer into the represented destination
window.
Source reference: `zig/std/mem.zig`.
Family: `write-integer`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_mem_writeInt_fi_1_45b2_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_mem_writeInt_fi_1_45b2_Contract

/--
Contract design hole for `fi:1:45f6` at `0x15d1c`.
Source operation: Append one represented byte window to the observation output.
Source reference: `deps/zesu/src/zkvm/ssz_decode_observation.zig`.
Family: `encoder-raw`.
Boundary bindings: none.
Same-source contract candidates: `ssz_decode_observation_Encoder_raw_fi_1_4045`,
`ssz_decode_observation_Encoder_raw_fi_1_40c3`, `ssz_decode_observation_Encoder_raw_fi_1_412a`,
`ssz_decode_observation_Encoder_raw_fi_1_42a2`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_ssz_decode_observation_Encoder_raw_fi_1_45f6_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_ssz_decode_observation_Encoder_raw_fi_1_45f6_Contract

/--
Contract design hole for `fi:1:49b1` at `0x161c0`.
Source operation: Append the represented source bytes to the bare-metal output context.
Source reference: `deps/zesu/src/zkvm/extern_io.zig`.
Family: `host-write`.
Boundary bindings: none.
Same-source contract candidates: `extern_io_write_output_fi_1_3d8b`,
`extern_io_write_output_fi_1_3db4`, `extern_io_write_output_fi_1_3ddd`,
`extern_io_write_output_fi_1_3e06`, `extern_io_write_output_fi_1_3e2f`,
`extern_io_write_output_fi_1_3e81`, `extern_io_write_output_fi_1_4101`.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_extern_io_write_output_fi_1_49b1_Contract : Prop := by
  exact BinaryFv.Zesu.Staging.Proposed_extern_io_write_output_fi_1_49b1_Contract

/--
Contract design hole for `fi:1:5a81` at `0x170b4`.
Source operation: Allocate an aligned byte window with the requested size.
Source reference: `zig/std/mem/Allocator.zig`.
Family: `allocator-alloc`.
Boundary bindings: `n=x12`.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_mem_Allocator_alloc__anon_1151_fi_1_5a81_Contract : Prop := by
  sorry

/--
Contract design hole for `fi:1:5b8d` at `0x17154`.
Source operation: Allocate a destination window and copy the represented source bytes into it.
Source reference: `zig/std/mem/Allocator.zig`.
Family: `allocator-dupe`.
Boundary bindings: none.
Same-source contract candidates: none.
Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.
Required design: bind semantic values to the recorded DWARF registers or memory.
Required design: state configured-machine, access, termination, and exact frame facts.
Do not replace this hole with a PC-only or unbound semantic contract.
-/
def Proposed_mem_Allocator_dupe__anon_1128_fi_1_5b8d_Contract : Prop := by
  sorry

/-- The 41 proposed Level 3 contracts selected below the 17 unresolved Level 2 fields. -/
structure Level3ContractAssumptions : Prop where
  ssz_decodeByteListList_fi_1_1999 :
    Proposed_ssz_decodeByteListList_fi_1_1999_Contract
  mem_Allocator_alloc__anon_1045_fi_1_340d :
    Proposed_mem_Allocator_alloc__anon_1045_fi_1_340d_Contract
  mem_Allocator_alloc__anon_1173_fi_1_386d :
    Proposed_mem_Allocator_alloc__anon_1173_fi_1_386d_Contract
  rlp_decode_decodeSingleTx_fi_1_3940 :
    Proposed_rlp_decode_decodeSingleTx_fi_1_3940_Contract
  mem_Allocator_alloc__anon_1432_fi_1_39b7 :
    Proposed_mem_Allocator_alloc__anon_1432_fi_1_39b7_Contract
  ssz_decodeWithdrawal_fi_1_3a74 :
    Proposed_ssz_decodeWithdrawal_fi_1_3a74_Contract
  ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b :
    Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract
  ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94 :
    Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract
  ssz_decode_observation_Encoder_accessList_fi_1_3fdd :
    Proposed_ssz_decode_observation_Encoder_accessList_fi_1_3fdd_Contract
  ssz_decode_observation_Encoder_authorizations_fi_1_406f :
    Proposed_ssz_decode_observation_Encoder_authorizations_fi_1_406f_Contract
  mem_Allocator_alloc__anon_1151_fi_1_5a81 :
    Proposed_mem_Allocator_alloc__anon_1151_fi_1_5a81_Contract
  mem_Allocator_dupe__anon_1128_fi_1_5b8d :
    Proposed_mem_Allocator_dupe__anon_1128_fi_1_5b8d_Contract

/--
Resolve Level 2 field `sszDecode` for `fi:1:2e0f`.
Level 3 contracts: `mem_Allocator_dupe__anon_1128_fi_1_5b8d`,
`ssz_decodeByteListList_fi_1_1999`, `mem_Allocator_alloc__anon_1151_fi_1_5a81`,
`mem_Allocator_alloc__anon_1045_fi_1_340d`, `mem_Allocator_alloc__anon_1173_fi_1_386d`,
`rlp_decode_decodeSingleTx_fi_1_3940`, `mem_Allocator_alloc__anon_1432_fi_1_39b7`,
`ssz_decodeWithdrawal_fi_1_3a74`.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.MachineExecution.memcpyInstanceContract`,
`BinaryFv.Zesu.Staging.proposed_memReadInt_proved`,
`BinaryFv.Zesu.Staging.proposed_forkNameFromSchemaByte_proved`,
`BinaryFv.Zesu.Staging.proposed_readU32_2ff8_proved`,
`BinaryFv.Zesu.Staging.proposed_readU32_3064_proved`,
`BinaryFv.Zesu.Staging.proposed_readU32_30e2_proved`,
`BinaryFv.Zesu.Staging.proposed_readU32_3335_proved`,
`BinaryFv.Zesu.Staging.proposed_readU32_3457_proved`,
`BinaryFv.Zesu.Staging.proposed_checkedSlice_34fd_proved`,
`BinaryFv.Zesu.Staging.proposed_checkedSlice_351c_proved`,
`BinaryFv.Zesu.Staging.proposed_checkedSlice_3541_proved`,
`BinaryFv.Zesu.Staging.proposed_checkedSlice_3566_proved`,
`BinaryFv.Zesu.Staging.proposed_checkedSlice_358b_proved`,
`BinaryFv.Zesu.Staging.proposed_readU32_3b27_proved`.
Parent-composed inline instances: `fi:1:3167`, `fi:1:31b1`, `fi:1:3203`, `fi:1:327b`,
`fi:1:32f5`, `fi:1:34c1`, `fi:1:35ab`, `fi:1:361f`, `fi:1:3693`, `fi:1:36dd`, `fi:1:3731`,
`fi:1:37a5`, `fi:1:37cf`, `fi:1:3823`.
Parent glue: 2144 instructions in 168 block fragments.
Inline `fi:1:3167` (`ssz.readU32`) contributes 10 scheduled instructions from 0x129cc. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:31b1` (`ssz.readU32`) contributes 11 scheduled instructions from 0x129f0. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:3203` (`ssz.readU64`) contributes 24 scheduled instructions from 0x12a4c. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:327b` (`ssz.readU64`) contributes 24 scheduled instructions from 0x12df4. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:32f5` (`ssz.readU32`) contributes 11 scheduled instructions from 0x12ae8. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:34c1` (`ssz.readU32`) contributes 10 scheduled instructions from 0x1305c. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:35ab` (`ssz.readU64`) contributes 15 scheduled instructions from 0x138b8. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:361f` (`ssz.readU64`) contributes 16 scheduled instructions from 0x138f4. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:3693` (`ssz.readU32`) contributes 14 scheduled instructions from 0x13934. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:36dd` (`ssz.readU64`) contributes 16 scheduled instructions from 0x1398c. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:3731` (`ssz.readU64`) contributes 12 scheduled instructions from 0x139f4. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:37a5` (`ssz.readU64`) contributes 12 scheduled instructions from 0x13a24. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:37cf` (`ssz.readU32`) contributes 11 scheduled instructions from 0x13ce0. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Inline `fi:1:3823` (`ssz.readU64`) contributes 23 scheduled instructions from 0x13cf0. It is not
a standalone machine region. Compose these instructions with the parent and reuse the shared
integer-reader load, shift, OR, and `Seg` fragments.
Fragment `0x121ac` (6 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:10adc5365e4a6c68`, `motif:cd26604b518d4d93`. Closest proofs: none.
Fragment `0x121ec` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x121f4` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:ed2fe286c82d2061`. Closest proofs: none.
Fragment `0x12200` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12204` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:6d657803278499fb`. Closest proofs: none.
Fragment `0x1220c` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:c93c034715b527d3`. Closest proofs: none.
Fragment `0x12218` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x1224c` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x1225c` (15 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:802297fc6fb86a27`, `motif:c9fb64f3a61c6eea`, `motif:effe2dbd30d8bf0d`. Closest
proofs: none.
Fragment `0x12298` (8 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:2229c4040d831b3f`, `motif:effe2dbd30d8bf0d`. Closest proofs: none.
Fragment `0x122b8` (21 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:055702010fa3b0ac`, `motif:eb3e47401d63410e`. Closest proofs: none.
Fragment `0x1230c` (40 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:0f88227d3478acd9`, `motif:a9979d2624b9bea2`, `motif:cf70036185249508`,
`motif:db232d031c0e562b`. Closest proofs: none.
Fragment `0x123ac` (5 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:058bbcaa69d86958`. Closest proofs: none.
Fragment `0x123c0` (5 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:058bbcaa69d86958`. Closest proofs: none.
Fragment `0x123d4` (5 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:058bbcaa69d86958`. Closest proofs: none.
Fragment `0x123e8` (5 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:058bbcaa69d86958`. Closest proofs: none.
Fragment `0x123fc` (57 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:3d9733a0b5d31f7a`, `motif:42651b9ebc3342e0`, `motif:586bf6c8a0cbce8a`,
`motif:cf70036185249508`, `motif:db232d031c0e562b`, `motif:e98ffb8adc5ab0dd`. Closest proofs:
none.
Fragment `0x124e0` (9 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:058bbcaa69d86958`, `motif:259fcad78dee0ed9`. Closest proofs: none.
Fragment `0x12504` (27 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`,
`BinaryFv.Zesu.MachineExecution.configuredRetStep`.
Motifs: `motif:02aeaf41d6bf2a5e`, `motif:259fcad78dee0ed9`, `motif:99e8108cc11a826e`,
`motif:a0846bb208aef4ea`, `motif:e7e5ee3a3c35481d`. Closest proofs: none.
Fragment `0x12570` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12580` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:19610085fdff4a3c`. Closest proofs: none.
Fragment `0x1258c` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x1259c` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x125ac` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x125bc` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x125cc` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x125dc` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x125ec` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x125fc` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:19610085fdff4a3c`. Closest proofs: none.
Fragment `0x12608` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12618` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12628` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12638` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:19610085fdff4a3c`. Closest proofs: none.
Fragment `0x12648` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12658` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12668` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12678` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12688` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:431f7ccb31d63bd9`. Closest proofs: none.
Fragment `0x12698` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x126a4` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x126a8` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:7a6bb6154e2752c6`. Closest proofs: none.
Fragment `0x126b4` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x126f4` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x12760` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x12764` (11 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:322eb0f23c96d6fc`. Closest proofs: none.
Fragment `0x12790` (11 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:322eb0f23c96d6fc`. Closest proofs: none.
Fragment `0x127bc` (11 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:322eb0f23c96d6fc`. Closest proofs: none.
Fragment `0x127e8` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:6d657803278499fb`. Closest proofs: none.
Fragment `0x127f0` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x127f4` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x127f8` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:7a6bb6154e2752c6`. Closest proofs: none.
Fragment `0x12804` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x12844` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x12884` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x128c4` (2 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x128f4` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:cc7beb3a65c61de4`. Closest proofs: none.
Fragment `0x128fc` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x1293c` (2 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x1296c` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:cc7beb3a65c61de4`. Closest proofs: none.
Fragment `0x12974` (2 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x1297c` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12988` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x129c8` (23 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:337496e7f6de3267`, `motif:60d15ab6f5ef18c4`, `motif:f19355251af7da08`. Closest
proofs: none.
Fragment `0x12a24` (5 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12a38` (5 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12a4c` (25 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:3882953a056cbe60`, `motif:cdc1d3e4dfd36488`. Closest proofs: none.
Fragment `0x12ab0` (90 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:1160559b028ce6ae`, `motif:133bc6a434340379`, `motif:1bb1e82ae16efeea`,
`motif:2445e5fe869210a3`, `motif:29ab321384cd0fad`, `motif:2b95cfcaa493e814`,
`motif:318fac39b92b394a`, `motif:3d26a98ddc105c45`, `motif:3efce179b73cdd11`,
`motif:6d3aff39b4773579`, `motif:92bdeb182860442c`, `motif:c126229ace809980`,
`motif:e9f1a3d42ceac142`, `motif:f19355251af7da08`, `motif:f20f95a066f073d1`. Closest proofs:
none.
Fragment `0x12c28` (42 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:133bc6a434340379`, `motif:4d64a51abd709211`, `motif:6d657803278499fb`,
`motif:6e3e7744e33e3798`, `motif:97e9ce5e3e69c357`, `motif:c6b7b6aae967b037`,
`motif:ceb0d9a024d3001e`, `motif:dae19658980a6164`, `motif:e3bb7b6debe9a53d`,
`motif:f20f95a066f073d1`. Closest proofs: none.
Fragment `0x12cd0` (7 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:69d77e1eae574472`. Closest proofs: none.
Fragment `0x12cec` (7 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8c306e9e5ff720ae`. Closest proofs: none.
Fragment `0x12d08` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x12d0c` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x12d10` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12d1c` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x12d5c` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x12d9c` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x12ddc` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:ed2fe286c82d2061`. Closest proofs: none.
Fragment `0x12de4` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12de8` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12df4` (25 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:3882953a056cbe60`, `motif:cdc1d3e4dfd36488`. Closest proofs: none.
Fragment `0x12e58` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x12e60` (12 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:45dfced50d998bd8`, `motif:cd26604b518d4d93`. Closest proofs: none.
Fragment `0x12ec8` (26 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:157339b06d3300f9`, `motif:27cfea70774ffaed`, `motif:2da0a3df85264c22`,
`motif:34e5446b50addf60`. Closest proofs: none.
Fragment `0x12f48` (10 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:34e5446b50addf60`, `motif:9a144369cee8d6f6`, `motif:aeac4b90c1b52699`,
`motif:f2e82442e78c469c`. Closest proofs: none.
Fragment `0x12f70` (6 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d70cdfdc160ce88e`. Closest proofs: none.
Fragment `0x12f88` (5 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8174d3a4e1c952d8`. Closest proofs: none.
Fragment `0x12f9c` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:7a6bb6154e2752c6`. Closest proofs: none.
Fragment `0x12fac` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x12fec` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x13018` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x1301c` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:6d657803278499fb`. Closest proofs: none.
Fragment `0x13024` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x1302c` (7 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:6d657803278499fb`, `motif:d54b47c71ff49ada`. Closest proofs: none.
Fragment `0x13048` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x1304c` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x1305c` (15 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8174d3a4e1c952d8`, `motif:ceb0d9a024d3001e`, `motif:f20f95a066f073d1`. Closest
proofs: none.
Fragment `0x130fc` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x13150` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:ed2fe286c82d2061`. Closest proofs: none.
Fragment `0x13158` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x13198` (4 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:5016719021f71c2a`, `motif:802297fc6fb86a27`. Closest proofs: none.
Fragment `0x131a8` (2 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:5016719021f71c2a`. Closest proofs: none.
Fragment `0x131b0` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8c4654ed93b1e827`. Closest proofs: none.
Fragment `0x131bc` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x131fc` (339 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:058bbcaa69d86958`, `motif:1f9f26760d419a14`, `motif:3b5f0bf4e5fc9988`,
`motif:59612eba4122cda2`, `motif:60d15ab6f5ef18c4`. Closest proofs: none.
Fragment `0x13748` (270 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:166b3c2e18bf9ab0`, `motif:6b13913d8f1ff2a7`, `motif:6d3aff39b4773579`,
`motif:71e80ad26bc1de3d`, `motif:7897e3d7c72dd41b`, `motif:8c306e9e5ff720ae`,
`motif:a6dd8355475b90f4`, `motif:c10fd8dbf06652b0`, `motif:cd92d0f0234f96b2`,
`motif:f2e82442e78c469c`. Closest proofs: none.
Fragment `0x13b80` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x13bc0` (43 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:3d26a98ddc105c45`, `motif:7897e3d7c72dd41b`, `motif:c93c034715b527d3`,
`motif:d8a879d5dd4ddfb8`. Closest proofs: none.
Fragment `0x13c6c` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8c4654ed93b1e827`. Closest proofs: none.
Fragment `0x13c78` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x13cb8` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`.
Motifs: none. Closest proofs: none.
Fragment `0x13cc0` (7 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:69d77e1eae574472`. Closest proofs: none.
Fragment `0x13cdc` (40 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:133bc6a434340379`, `motif:2a320bafb4e66886`, `motif:337496e7f6de3267`,
`motif:6b13913d8f1ff2a7`, `motif:a6dd8355475b90f4`, `motif:ceb0d9a024d3001e`,
`motif:d8a879d5dd4ddfb8`. Closest proofs: none.
Fragment `0x13db0` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x13db8` (5 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:066543c2b45d5eff`, `motif:4e572021751d58b7`. Closest proofs: none.
Fragment `0x13dcc` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x13dd0` (8 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:c6b7b6aae967b037`. Closest proofs: none.
Fragment `0x13df0` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: `motif:f2fd49ee2d35a3a7`. Closest proofs: none.
Fragment `0x13dfc` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: `motif:f2fd49ee2d35a3a7`. Closest proofs: none.
Fragment `0x13e08` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x13e48` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x13e88` (7 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:4d2c947dcbab506b`, `motif:ca275be525f9253b`. Closest proofs: none.
Fragment `0x13ea4` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: none.
Motifs: `motif:58a32f87f528080c`. Closest proofs: none.
Fragment `0x13eac` (12 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:4e572021751d58b7`, `motif:a48e57a5c9e097c2`, `motif:c4ba05f6fd62e18a`. Closest
proofs: none.
Fragment `0x13edc` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: none.
Motifs: `motif:58a32f87f528080c`. Closest proofs: none.
Fragment `0x13ee4` (4 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:f2fd49ee2d35a3a7`. Closest proofs: none.
Fragment `0x141e0` (26 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:11b1497dba807c6c`, `motif:2a320bafb4e66886`, `motif:2da0a3df85264c22`,
`motif:97e9ce5e3e69c357`, `motif:9a144369cee8d6f6`, `motif:dae19658980a6164`,
`motif:e98ffb8adc5ab0dd`. Closest proofs: none.
Fragment `0x14248` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: `motif:b631af6e154c4ce1`. Closest proofs: none.
Fragment `0x14250` (2 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: `motif:348c1d38932e3afe`. Closest proofs: none.
Fragment `0x1425c` (2 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: `motif:348c1d38932e3afe`. Closest proofs: none.
Fragment `0x14438` (9 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: `motif:0f88227d3478acd9`. Closest proofs: none.
Fragment `0x1445c` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`.
Motifs: none. Closest proofs: none.
Fragment `0x14460` (6 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:1c8071aec1063b7c`, `motif:d26a15b90eb8a64b`. Closest proofs: none.
Fragment `0x14478` (9 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:11b1497dba807c6c`, `motif:8b35081da32a7c96`. Closest proofs: none.
Fragment `0x1449c` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:3882953a056cbe60`. Closest proofs: none.
Fragment `0x144a4` (10 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:4d2c947dcbab506b`, `motif:a48e57a5c9e097c2`, `motif:f2fd49ee2d35a3a7`. Closest
proofs: none.
Fragment `0x144cc` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:203d0ee2dd28617d`. Closest proofs: none.
Fragment `0x144dc` (9 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:f2fd49ee2d35a3a7`. Closest proofs: none.
Fragment `0x14500` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x14540` (8 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:975e86962ecb9d0f`. Closest proofs: none.
Fragment `0x145a0` (12 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:b631af6e154c4ce1`, `motif:d11eac2439ff8b16`, `motif:f2fd49ee2d35a3a7`. Closest
proofs: none.
Fragment `0x14790` (2 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`.
Motifs: none. Closest proofs: none.
Fragment `0x147ac` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x147e0` (7 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:3d9733a0b5d31f7a`, `motif:8174d3a4e1c952d8`. Closest proofs: none.
Fragment `0x147fc` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8c4654ed93b1e827`. Closest proofs: none.
Fragment `0x14808` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x14848` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: none. Closest proofs: none.
Fragment `0x14878` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x1487c` (13 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:de3d0500fedad614`. Closest proofs: none.
Fragment `0x148b0` (12 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:de3d0500fedad614`. Closest proofs: none.
Fragment `0x148e0` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x148e4` (8 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:18169ce62dc09b6d`, `motif:ca275be525f9253b`. Closest proofs: none.
Fragment `0x14904` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:203d0ee2dd28617d`. Closest proofs: none.
Fragment `0x14914` (16 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:18169ce62dc09b6d`, `motif:541b46dcdb00aba4`. Closest proofs: none.
Fragment `0x14954` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:203d0ee2dd28617d`. Closest proofs: none.
Fragment `0x14964` (17 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:18169ce62dc09b6d`, `motif:541b46dcdb00aba4`. Closest proofs: none.
Fragment `0x149a8` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:203d0ee2dd28617d`. Closest proofs: none.
Fragment `0x149b8` (7 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x149d4` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x14a14` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x14a54` (16 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d9edd42f15993ef9`. Closest proofs: none.
Fragment `0x14a94` (14 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8e16f6d53c1c68a0`, `motif:975e86962ecb9d0f`. Closest proofs: none.
Fragment `0x14acc` (4 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:203d0ee2dd28617d`. Closest proofs: none.
Fragment `0x14adc` (11 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:6c1029df5014c0f9`, `motif:d11eac2439ff8b16`. Closest proofs: none.
Fragment `0x14b08` (8 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:11b1497dba807c6c`, `motif:46abafc066ef7dce`, `motif:8174d3a4e1c952d8`. Closest
proofs: none.
Fragment `0x14b28` (46 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:1bb1e82ae16efeea`, `motif:2229c4040d831b3f`, `motif:348c1d38932e3afe`,
`motif:3efce179b73cdd11`, `motif:97e9ce5e3e69c357`, `motif:9f775ee85031f771`,
`motif:e98ffb8adc5ab0dd`, `motif:f2fd49ee2d35a3a7`. Closest proofs: none.
Fragment `0x14be0` (47 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.stepStore`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:9f775ee85031f771`, `motif:eb3e47401d63410e`, `motif:f670689d3b49bfa1`. Closest
proofs: none.
Fragment `0x14c9c` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x14ca0` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:ed2fe286c82d2061`. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_sszDecode
    (mem_Allocator_dupe__anon_1128_fi_1_5b8d : Proposed_mem_Allocator_dupe__anon_1128_fi_1_5b8d_Contract)
    (ssz_decodeByteListList_fi_1_1999 : Proposed_ssz_decodeByteListList_fi_1_1999_Contract)
    (mem_Allocator_alloc__anon_1151_fi_1_5a81 : Proposed_mem_Allocator_alloc__anon_1151_fi_1_5a81_Contract)
    (mem_Allocator_alloc__anon_1045_fi_1_340d : Proposed_mem_Allocator_alloc__anon_1045_fi_1_340d_Contract)
    (mem_Allocator_alloc__anon_1173_fi_1_386d : Proposed_mem_Allocator_alloc__anon_1173_fi_1_386d_Contract)
    (rlp_decode_decodeSingleTx_fi_1_3940 : Proposed_rlp_decode_decodeSingleTx_fi_1_3940_Contract)
    (mem_Allocator_alloc__anon_1432_fi_1_39b7 : Proposed_mem_Allocator_alloc__anon_1432_fi_1_39b7_Contract)
    (ssz_decodeWithdrawal_fi_1_3a74 : Proposed_ssz_decodeWithdrawal_fi_1_3a74_Contract)
    : SszDecodeLevel2InstanceContract := by
  sorry

/--
Resolve Level 2 field `writeFailureRecord` for `fi:1:499d`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_49b1_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeFailureRecord
    : WriteFailureRecordInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_49b1_proved

/--
Resolve Level 2 field `writeSuccessBlockHash` for `fi:1:3e6d`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_3e81_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessBlockHash
    : WriteSuccessBlockHashInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_3e81_proved

/--
Resolve Level 2 field `writeSuccessBoolean` for `fi:1:4276`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_rawEncoder_42a2_proved`.
Parent-composed inline instances: none.
Parent glue: 7 instructions in 2 block fragments.
Fragment `0x15b9c` (4 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:2eb88edeb11900e1`. Closest proofs: none.
Fragment `0x15bbc` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`,
`BinaryFv.Zesu.MachineExecution.configuredRetStep`.
Motifs: `motif:1891f020d6b485dc`. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessBoolean
    : WriteSuccessBooleanInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_booleanEncoder_4276_proved

/--
Resolve Level 2 field `writeSuccessFeeRecipient` for `fi:1:3da0`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_3db4_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessFeeRecipient
    : WriteSuccessFeeRecipientInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_3db4_proved

/--
Resolve Level 2 field `writeSuccessInt` for `fi:1:4578`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_memWriteInt_proved`,
`BinaryFv.Zesu.Staging.proposed_rawEncoder_45f6_proved`.
Parent-composed inline instances: none.
Parent glue: 5 instructions in 2 block fragments.
Fragment `0x15d10` (2 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:2eb88edeb11900e1`. Closest proofs: none.
Fragment `0x15d2c` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`,
`BinaryFv.Zesu.MachineExecution.configuredRetStep`.
Motifs: `motif:1891f020d6b485dc`. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessInt
    : WriteSuccessIntInstanceContract := by
  sorry

/--
Resolve Level 2 field `writeSuccessBytes` for `fi:1:4333`.
Level 3 contracts: none.
Earlier Level 2 results: `writeSuccessInt`.
Unconditional child proofs: none.
Parent-composed inline instances: `fi:1:4350`.
Parent glue: 30 instructions in 4 block fragments.
Inline `fi:1:4350` (`ssz_decode_observation.Encoder.raw`) contributes 21 scheduled instructions
from 0x10190. It is not a standalone machine region. Compose these instructions with the parent
and reuse the shared integer-reader load, shift, OR, and `Seg` fragments.
Fragment `0x10190` (5 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`,
`BinaryFv.Zesu.MachineExecution.configuredRetStep`.
Motifs: `motif:066543c2b45d5eff`, `motif:46abafc066ef7dce`. Closest proofs: none.
Fragment `0x101a4` (8 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:7cc72153757d2c36`. Closest proofs: none.
Fragment `0x15c6c` (9 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:f1750b1e29b40bc8`. Closest proofs: none.
Fragment `0x15c90` (8 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:2279394c061c63f8`, `motif:aeac4b90c1b52699`. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessBytes
    (writeSuccessInt : WriteSuccessIntInstanceContract)
    : WriteSuccessBytesInstanceContract := by
  sorry

/--
Resolve Level 2 field `writeSuccessByteLists` for `fi:1:4316`.
Level 3 contracts: none.
Earlier Level 2 results: `writeSuccessInt`, `writeSuccessBytes`.
Unconditional child proofs: none.
Parent-composed inline instances: none.
Parent glue: 23 instructions in 5 block fragments.
Fragment `0x15c10` (9 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:f1750b1e29b40bc8`. Closest proofs: none.
Fragment `0x15c34` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x15c3c` (4 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:10adc5365e4a6c68`, `motif:9fe69b320398dba8`. Closest proofs: none.
Fragment `0x15c4c` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x15c58` (5 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`,
`BinaryFv.Zesu.MachineExecution.configuredRetStep`.
Motifs: `motif:99e8108cc11a826e`, `motif:f2fd49ee2d35a3a7`. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessByteLists
    (writeSuccessInt : WriteSuccessIntInstanceContract)
    (writeSuccessBytes : WriteSuccessBytesInstanceContract)
    : WriteSuccessByteListsInstanceContract := by
  sorry

/--
Resolve Level 2 field `writeSuccessHashes` for `fi:1:4116`.
Level 3 contracts: none.
Earlier Level 2 results: `writeSuccessInt`.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_rawEncoder_412a_proved`.
Parent-composed inline instances: none.
Parent glue: 99 instructions in 4 block fragments.
Fragment `0x15744` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8e16f6d53c1c68a0`. Closest proofs: none.
Fragment `0x15750` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x15754` (92 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:1a72c511d58942ab`, `motif:3b5f0bf4e5fc9988`. Closest proofs: none.
Fragment `0x158d4` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8174d3a4e1c952d8`. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessHashes
    (writeSuccessInt : WriteSuccessIntInstanceContract)
    : WriteSuccessHashesInstanceContract := by
  sorry

/--
Resolve Level 2 field `writeSuccessLogsBloom` for `fi:1:3e1b`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_3e2f_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessLogsBloom
    : WriteSuccessLogsBloomInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_3e2f_proved

/--
Resolve Level 2 field `writeSuccessOptionalU64` for `fi:1:42cc`.
Level 3 contracts: none.
Earlier Level 2 results: `writeSuccessBoolean`, `writeSuccessInt`.
Unconditional child proofs: none.
Parent-composed inline instances: none.
Parent glue: 18 instructions in 4 block fragments.
Fragment `0x15bc8` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x15bd0` (7 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:2eb88edeb11900e1`, `motif:9fe69b320398dba8`. Closest proofs: none.
Fragment `0x15bec` (6 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:2279394c061c63f8`. Closest proofs: none.
Fragment `0x15c04` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessOptionalU64
    (writeSuccessBoolean : WriteSuccessBooleanInstanceContract)
    (writeSuccessInt : WriteSuccessIntInstanceContract)
    : WriteSuccessOptionalU64InstanceContract := by
  sorry

/--
Resolve Level 2 field `writeSuccessParentBeaconRoot` for `fi:1:40ed`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_4101_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessParentBeaconRoot
    : WriteSuccessParentBeaconRootInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_4101_proved

/--
Resolve Level 2 field `writeSuccessParentHash` for `fi:1:3d77`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_3d8b_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessParentHash
    : WriteSuccessParentHashInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_3d8b_proved

/--
Resolve Level 2 field `writeSuccessReceiptsRoot` for `fi:1:3df2`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_3e06_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessReceiptsRoot
    : WriteSuccessReceiptsRootInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_3e06_proved

/--
Resolve Level 2 field `writeSuccessStateRoot` for `fi:1:3dc9`.
Level 3 contracts: none.
Earlier Level 2 results: none.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_writeOutput_3ddd_proved`.
Parent-composed inline instances: none.
Parent glue: 0 instructions in 0 block fragments.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessStateRoot
    : WriteSuccessStateRootInstanceContract :=
  BinaryFv.Zesu.Staging.proposed_writeOutput_3ddd_proved

/--
Resolve Level 2 field `writeSuccessTransactions` for `fi:1:3e96`.
Level 3 contracts: `ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b`,
`ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94`,
`ssz_decode_observation_Encoder_accessList_fi_1_3fdd`,
`ssz_decode_observation_Encoder_authorizations_fi_1_406f`.
Earlier Level 2 results: `writeSuccessInt`, `writeSuccessOptionalU64`, `writeSuccessBytes`.
Unconditional child proofs: `BinaryFv.Zesu.Staging.proposed_integerEncoder_4494_proved`,
`BinaryFv.Zesu.Staging.proposed_integerEncoder_43a9_proved`,
`BinaryFv.Zesu.Staging.proposed_rawEncoder_4045_proved`.
Parent-composed inline instances: `fi:1:3ec4`.
Parent glue: 289 instructions in 24 block fragments.
Inline `fi:1:3ec4` (`ssz_decode_observation.Encoder.int__anon_1642`) contributes 18 scheduled
instructions from 0x10190. It is not a standalone machine region. Compose these instructions
with the parent and reuse the shared integer-reader load, shift, OR, and `Seg` fragments.
Fragment `0x10190` (5 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`,
`BinaryFv.Zesu.MachineExecution.configuredRetStep`.
Motifs: `motif:066543c2b45d5eff`, `motif:46abafc066ef7dce`. Closest proofs: none.
Fragment `0x101a4` (8 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:7cc72153757d2c36`. Closest proofs: none.
Fragment `0x14ef4` (2 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:9fe69b320398dba8`. Closest proofs: none.
Fragment `0x14efc` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x14f00` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: none. Closest proofs: none.
Fragment `0x14f08` (122 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:10adc5365e4a6c68`, `motif:1160559b028ce6ae`, `motif:133bc6a434340379`,
`motif:166b3c2e18bf9ab0`, `motif:1b04c3e112d1bc8c`, `motif:1bb1e82ae16efeea`,
`motif:2229c4040d831b3f`, `motif:2b95cfcaa493e814`, `motif:318fac39b92b394a`,
`motif:61b812638b9a08f2`, `motif:6c1029df5014c0f9`, `motif:6e3e7744e33e3798`,
`motif:92bdeb182860442c`, `motif:cd26604b518d4d93`, `motif:e45d82e5b545468b`,
`motif:e6e0b8fc7a348252`, `motif:f20f95a066f073d1`. Closest proofs: none.
Fragment `0x150f0` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:4d2c947dcbab506b`. Closest proofs: none.
Fragment `0x150fc` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:c4ba05f6fd62e18a`. Closest proofs: none.
Fragment `0x15108` (4 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d70cdfdc160ce88e`. Closest proofs: none.
Fragment `0x15148` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8e16f6d53c1c68a0`. Closest proofs: none.
Fragment `0x15154` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: none. Closest proofs: none.
Fragment `0x1519c` (6 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8e16f6d53c1c68a0`, `motif:aeac4b90c1b52699`. Closest proofs: none.
Fragment `0x151b4` (4 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:d70cdfdc160ce88e`. Closest proofs: none.
Fragment `0x151c4` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: none. Closest proofs: none.
Fragment `0x153c0` (4 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:1c8071aec1063b7c`. Closest proofs: none.
Fragment `0x153d0` (1 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: none.
Motifs: none. Closest proofs: none.
Fragment `0x153d4` (93 steps): compose with `BinaryFv.RiscV.Seg.stepStore`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:133bc6a434340379`, `motif:2445e5fe869210a3`, `motif:51cb9acae55b1e5d`,
`motif:6e135e5007094700`, `motif:92bdeb182860442c`, `motif:c126229ace809980`,
`motif:d4c91c4d5b91b676`, `motif:d54b47c71ff49ada`, `motif:e3bb7b6debe9a53d`,
`motif:e9f1a3d42ceac142`, `motif:f2e82442e78c469c`, `motif:f85767bb44dbabaa`. Closest proofs:
none.
Fragment `0x15558` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x15564` (4 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:c4ba05f6fd62e18a`. Closest proofs: none.
Fragment `0x15574` (1 steps): compose with `BinaryFv.RiscV.Seg.forget`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`.
Motifs: none. Closest proofs: none.
Fragment `0x15620` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:c4ba05f6fd62e18a`. Closest proofs: none.
Fragment `0x1562c` (6 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:bafe46f445f4bc2e`. Closest proofs: none.
Fragment `0x15644` (6 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:bafe46f445f4bc2e`. Closest proofs: none.
Fragment `0x1565c` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs: `BinaryFv.Zesu.MachineExecution.configuredJStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessTransactions
    (ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b : Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract)
    (ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94 : Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract)
    (ssz_decode_observation_Encoder_accessList_fi_1_3fdd : Proposed_ssz_decode_observation_Encoder_accessList_fi_1_3fdd_Contract)
    (ssz_decode_observation_Encoder_authorizations_fi_1_406f : Proposed_ssz_decode_observation_Encoder_authorizations_fi_1_406f_Contract)
    (writeSuccessInt : WriteSuccessIntInstanceContract)
    (writeSuccessOptionalU64 : WriteSuccessOptionalU64InstanceContract)
    (writeSuccessBytes : WriteSuccessBytesInstanceContract)
    : WriteSuccessTransactionsInstanceContract := by
  sorry

/--
Resolve Level 2 field `writeSuccessWithdrawals` for `fi:1:40af`.
Level 3 contracts: none.
Earlier Level 2 results: `writeSuccessInt`.
Unconditional child proofs: `BinaryFv.Zesu.MachineExecution.memcpyInstanceContract`,
`BinaryFv.Zesu.Staging.proposed_rawEncoder_40c3_proved`.
Parent-composed inline instances: none.
Parent glue: 22 instructions in 7 block fragments.
Fragment `0x15680` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8e16f6d53c1c68a0`. Closest proofs: none.
Fragment `0x1568c` (2 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: none. Closest proofs: none.
Fragment `0x15694` (5 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.configuredJalrCallStep`,
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8e16f6d53c1c68a0`, `motif:d26a15b90eb8a64b`. Closest proofs: none.
Fragment `0x156a8` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:c4ba05f6fd62e18a`. Closest proofs: none.
Fragment `0x156b4` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:c4ba05f6fd62e18a`. Closest proofs: none.
Fragment `0x156d0` (3 steps): compose with `BinaryFv.RiscV.Seg.step`,
`BinaryFv.RiscV.Seg.forget`. Step APIs: `BinaryFv.Zesu.configuredAuipcStep`,
`BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep`,
`BinaryFv.Zesu.configuredJalrCallStep`.
Motifs: `motif:c4ba05f6fd62e18a`. Closest proofs: none.
Fragment `0x156dc` (3 steps): compose with `BinaryFv.RiscV.Seg.stepJump`,
`BinaryFv.RiscV.Seg.step`. Step APIs:
`BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep`.
Motifs: `motif:8174d3a4e1c952d8`. Closest proofs: none.
Frame rule: choose the complete register and memory write regions before `Seg` starts.
Frame rule: use `Seg.forget` before a later write replaces a recorded register value.
-/
private theorem resolve_writeSuccessWithdrawals
    (writeSuccessInt : WriteSuccessIntInstanceContract)
    : WriteSuccessWithdrawalsInstanceContract := by
  sorry

/-- The staged Level 3 to Level 2 refinement edge. Production code does not import it. -/
theorem level2Contracts_of_level3_staged
    (hLevel3 : Level3ContractAssumptions) : Level2ContractAssumptions := by
  have resolved_sszDecode : SszDecodeLevel2InstanceContract :=
    resolve_sszDecode
      hLevel3.mem_Allocator_dupe__anon_1128_fi_1_5b8d
      hLevel3.ssz_decodeByteListList_fi_1_1999
      hLevel3.mem_Allocator_alloc__anon_1151_fi_1_5a81
      hLevel3.mem_Allocator_alloc__anon_1045_fi_1_340d
      hLevel3.mem_Allocator_alloc__anon_1173_fi_1_386d
      hLevel3.rlp_decode_decodeSingleTx_fi_1_3940
      hLevel3.mem_Allocator_alloc__anon_1432_fi_1_39b7
      hLevel3.ssz_decodeWithdrawal_fi_1_3a74
  have resolved_writeFailureRecord : WriteFailureRecordInstanceContract :=
    resolve_writeFailureRecord
  have resolved_writeSuccessBlockHash : WriteSuccessBlockHashInstanceContract :=
    resolve_writeSuccessBlockHash
  have resolved_writeSuccessBoolean : WriteSuccessBooleanInstanceContract :=
    resolve_writeSuccessBoolean
  have resolved_writeSuccessFeeRecipient : WriteSuccessFeeRecipientInstanceContract :=
    resolve_writeSuccessFeeRecipient
  have resolved_writeSuccessInt : WriteSuccessIntInstanceContract :=
    resolve_writeSuccessInt
  have resolved_writeSuccessBytes : WriteSuccessBytesInstanceContract :=
    resolve_writeSuccessBytes
      resolved_writeSuccessInt
  have resolved_writeSuccessByteLists : WriteSuccessByteListsInstanceContract :=
    resolve_writeSuccessByteLists
      resolved_writeSuccessInt
      resolved_writeSuccessBytes
  have resolved_writeSuccessHashes : WriteSuccessHashesInstanceContract :=
    resolve_writeSuccessHashes
      resolved_writeSuccessInt
  have resolved_writeSuccessLogsBloom : WriteSuccessLogsBloomInstanceContract :=
    resolve_writeSuccessLogsBloom
  have resolved_writeSuccessOptionalU64 : WriteSuccessOptionalU64InstanceContract :=
    resolve_writeSuccessOptionalU64
      resolved_writeSuccessBoolean
      resolved_writeSuccessInt
  have resolved_writeSuccessParentBeaconRoot : WriteSuccessParentBeaconRootInstanceContract :=
    resolve_writeSuccessParentBeaconRoot
  have resolved_writeSuccessParentHash : WriteSuccessParentHashInstanceContract :=
    resolve_writeSuccessParentHash
  have resolved_writeSuccessReceiptsRoot : WriteSuccessReceiptsRootInstanceContract :=
    resolve_writeSuccessReceiptsRoot
  have resolved_writeSuccessStateRoot : WriteSuccessStateRootInstanceContract :=
    resolve_writeSuccessStateRoot
  have resolved_writeSuccessTransactions : WriteSuccessTransactionsInstanceContract :=
    resolve_writeSuccessTransactions
      hLevel3.ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b
      hLevel3.ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94
      hLevel3.ssz_decode_observation_Encoder_accessList_fi_1_3fdd
      hLevel3.ssz_decode_observation_Encoder_authorizations_fi_1_406f
      resolved_writeSuccessInt
      resolved_writeSuccessOptionalU64
      resolved_writeSuccessBytes
  have resolved_writeSuccessWithdrawals : WriteSuccessWithdrawalsInstanceContract :=
    resolve_writeSuccessWithdrawals
      resolved_writeSuccessInt
  exact {
    sszDecode := resolved_sszDecode
    writeSuccessParentHash := resolved_writeSuccessParentHash
    writeSuccessFeeRecipient := resolved_writeSuccessFeeRecipient
    writeSuccessStateRoot := resolved_writeSuccessStateRoot
    writeSuccessReceiptsRoot := resolved_writeSuccessReceiptsRoot
    writeSuccessLogsBloom := resolved_writeSuccessLogsBloom
    writeSuccessBlockHash := resolved_writeSuccessBlockHash
    writeSuccessParentBeaconRoot := resolved_writeSuccessParentBeaconRoot
    writeSuccessTransactions := resolved_writeSuccessTransactions
    writeSuccessWithdrawals := resolved_writeSuccessWithdrawals
    writeSuccessHashes := resolved_writeSuccessHashes
    writeSuccessBoolean := resolved_writeSuccessBoolean
    writeSuccessOptionalU64 := resolved_writeSuccessOptionalU64
    writeSuccessByteLists := resolved_writeSuccessByteLists
    writeSuccessBytes := resolved_writeSuccessBytes
    writeSuccessInt := resolved_writeSuccessInt
    writeFailureRecord := resolved_writeFailureRecord
  }

end BinaryFv.Zesu.Staging.HLevel3
