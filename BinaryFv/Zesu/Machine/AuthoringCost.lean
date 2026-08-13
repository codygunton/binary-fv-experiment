import BinaryFv.Zesu.Machine.Target

/-!
# The measurement that matters: lines at a call site

The campaign exists to reduce **proof authoring cost**, which is lines written and time spent
writing them. An earlier module in this branch measured *elaboration* time instead. That is a real
operational cost, but it is not the bottleneck the campaign was created to attack, and it moves in
the opposite direction from authoring cost.

The two diverge because of `autoParam`. An obligation discharged by an `autoParam` still costs its
full elaboration at every site — the four `native_decide`s per instruction do not go away — but it
costs the *author* nothing, because nothing is written for it. So:

* elaboration time is **unshareable**: 4 `native_decide` per instruction, always;
* lines at a call site are **highly shareable**: an `autoParam` moves them into the lemma, once.

This module measures the second. `fetchAt` below is the same `fetchInstruction`, with the four byte
reads and the bound moved into `autoParam`s so a site supplies only an address.
-/

namespace BinaryFv.Zesu.Machine

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.Zesu.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- Fetch at `pc`, with the bytes as `autoParam`s. A call site writes the address and nothing else.

The bytes stay **explicit**. They cannot be implicit: `native_decide` needs a closed goal, and a
metavariable byte leaves it `Expected type must not contain metavariables`. That is why the pre-wipe
`fetchInstruction` took them explicitly too — the four *proofs* are what the `autoParam` removes,
not the four literals.

This is the `InstructionClassSteps` design, whose own note records the point exactly: *"one lemma
per class whose only real arguments are those literals … everything else is an `autoParam` … no
`fetchWord … = <literal>` rewrite is needed at a call site."* -/
theorem fetchAt (state : State) (pc : Nat) (byte0 byte1 byte2 byte3 : UInt8)
    (loaded : programImage.matchesMemory state.mem)
    (read0 : programImage.readByte? pc = some byte0 := by native_decide)
    (read1 : programImage.readByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : programImage.readByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : programImage.readByte? (pc + 3) = some byte3 := by native_decide)
    (fits : pc < 2 ^ 64 := by decide) :
    FetchBytesAt state (BitVec.ofNat 64 pc)
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) :=
  ProgramImage.fetchBytesAt_of_image_bytes programImage state pc fits loaded
    byte0 byte1 byte2 byte3 read0 read1 read2 read3

/-! ## The ten instructions of Case A's motif, one line each

Compare against `CaseAAllSites.lean`, where the same ten cost five lines apiece because every byte
is written out. The elaboration is identical — forty `native_decide`s either way. -/

example (s : State) (l : programImage.matchesMemory s.mem) : True := by
  have _f70 := fetchAt s 0x70 0x03 0x45 0x16 0x00 l
  have _f74 := fetchAt s 0x74 0x03 0x46 0x06 0x00 l
  have _f78 := fetchAt s 0x78 0x83 0x46 0x29 0x00 l
  have _f7c := fetchAt s 0x7c 0x03 0x47 0x39 0x00 l
  have _f80 := fetchAt s 0x80 0x13 0x15 0x85 0x00 l
  have _f84 := fetchAt s 0x84 0x33 0x65 0xc5 0x00 l
  have _f88 := fetchAt s 0x88 0x93 0x96 0x06 0x01 l
  have _f8c := fetchAt s 0x8c 0x13 0x17 0x87 0x01 l
  have _f90 := fetchAt s 0x90 0xb3 0x66 0xd7 0x00 l
  have _f94 := fetchAt s 0x94 0x33 0xe5 0xa6 0x00 l
  trivial

end BinaryFv.Zesu.Machine
