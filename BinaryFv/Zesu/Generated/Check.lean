import Image
import Program
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-!
# Regression checks on the generated artifacts

`#guard`s, not `#eval`s: a converter that drifts from the object must break the build rather than
print a different number into a log nobody reads. Everything here is decided by the kernel on the
generated data, so none of it is a trusted claim about the object — it is a claim that the two
generated files agree with each other and with the sizes the extractor reported.

Comments here are `--`, not `/-- -/`: a doc comment must attach to a declaration, and `#guard` is a
command, so the doc-comment form does not parse.
-/

open BinaryFv.Zesu.Generated BinaryFv.Binary BinaryFv.Binary.Elfling

-- `.text` is exactly the corpus the n-gram study measured: 17740 bytes, 4435 instructions.
#guard textBytes.size = 17740
#guard textBytes.size / 4 = 4435
#guard textSegment.memorySize = textBytes.size

-- `0x70` is `lbu a0, 1(a2)`, encoded `03 45 16 00`. It is the first instruction of the
-- `mem.readInt` motif — Case A — so an image off by any offset fails here.
#guard programImage.readByte? 0x70 = some 0x03
#guard programImage.readByte? 0x71 = some 0x45
#guard programImage.readByte? 0x72 = some 0x16
#guard programImage.readByte? 0x73 = some 0x00

-- One instance per DWARF function instance. The extractor checks identity distinctness; this
-- checks the count survived conversion.
#guard generatedProgram.functionInstances.size = 159

-- The offsets a linker still has to patch. Case D loses 2 of its 23 sites to these.
#guard relocatedPcs.size = 73

-- Ownership is a stack, not a value: `0x70` is claimed by `mem.readInt`, the `ssz.readU32` that
-- inlines it, and the `ssz.decodeByteListList` above that. Three claimants is the expected
-- nesting; a change means the region conversion lost or gained a level.
#guard (generatedProgram.functionInstances.filter
    (fun fi => fi.regions.any (fun r => r.start ≤ 0x70 ∧ 0x70 < r.start + r.size))).size = 3

-- No instance may claim an address outside the image.
#guard generatedProgram.functionInstances.all
  (fun fi => fi.regions.all (fun r => r.start + r.size ≤ textBytes.size))
