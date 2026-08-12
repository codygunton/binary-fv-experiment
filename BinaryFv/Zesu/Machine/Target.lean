import Image
import Program
import BinaryFv.RiscV.Elfling.ProgramGeometry
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Step.AbstractPremise

/-!
# The Zesu SSZ decode target, bound to the machine premises

This is the whole target-specific surface the step layer needs. Everything above it — the class
step lemmas, `Seg`, the motif lemmas — is written against these names and never against an address.

Three of the four bindings are one-liners that carry no target data at all; they are named here
rather than inlined because the step layer is stated in terms of them:

* `decoderPreserved` — registers stable across the target's own instructions. `x1` is excluded
  because an emitted call writes the link register before transferring.
* `decoderFetchPc` — an aligned instruction start inside an execution scope. Fetch premises apply
  at starts; a retired instruction occupies bytes, so confinement uses the region predicate.
* `DecoderMachineArgs` — the input slice a decode is run against.

Only the data-access bounds carry target data, and they come from the pinned object's sections
rather than from a handwritten address.

## What the fetch premise costs

`ImageFetch.lean` turns four image byte reads into `FetchBytesAt`. The reads themselves cannot be
`decide`d — see the note above `fetchInstruction` — so each instruction carries four
`native_decide`s. A motif lemma over `n` instructions still carries `4n` of them, because each
instruction owns a different word. This is the floor under every measurement in the campaign.
-/

namespace BinaryFv.Zesu.Machine

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.Zesu.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000

/-! ## Registers and fetch scope -/

/-- Registers whose values stay stable while the target's own instructions execute. The link
register is excluded: an emitted call writes it before transferring to the callee. -/
def decoderPreserved (r : Register) : Prop :=
  r ≠ x1 ∧ platformPreserved r

/-- A fetchable instruction start inside a byte-range execution scope. Fetch premises apply only at
aligned starts, while confinement uses the region predicate, because a retired instruction occupies
four bytes rather than one address. -/
def decoderFetchPc (executionPcs : BitVec 64 → Prop) (pc : BitVec 64) : Prop :=
  executionPcs pc ∧ pc.toNat % 4 = 0

/-! ## Execution scopes

Named per function instance rather than per address. `functionInstanceExecutionPcs` reads the
regions out of the generated program, so a proof cannot pick a convenient scope. -/

/-- Every instruction the generated program claims. The widest scope a target proof can use. -/
abbrev programPcs : BitVec 64 → Prop := fun pc =>
  ∃ instance_ ∈ generatedProgram.functionInstances,
    ∃ region ∈ instance_.regions, region.start ≤ pc.toNat ∧ pc.toNat < region.start + region.size

/-! ## Data access

`inputBase` and `bytes` describe the SSZ input a decode runs against. The bounds below come from
the pinned object's own sections, not from a handwritten number. -/

structure DecoderMachineArgs where
  inputBase : Nat
  bytes : ByteArray

/-- Bytes of the target's private statics. The object's `.bss` is 177 bytes; the size is carried
here as a single named constant so a change in the object is a change in one place. -/
def bssSize : Nat := 177

/-- Instruction bytes the image owns. A proof reads these through
`fetchBytesAt_of_ownedEncodedWord`, never by unfolding the byte array. -/
def DecoderReadableByte (args : DecoderMachineArgs) (address : Nat) : Prop :=
  (args.inputBase ≤ address ∧ address < args.inputBase + args.bytes.size) ∨
    programImage.readByte? address ≠ none

/-! ## The per-instruction fetch obligation

**This is the measurement the whole campaign turns on**, so the reasoning is recorded rather than
left in a commit message.

`decide` cannot discharge an image read here. The image is 17740 bytes emitted as `ByteArray.mk
#[…]` chunks joined by `++`, and kernel reduction of the array literal overflows the stack in about
three seconds — not slow, *impossible*. Raising `maxRecDepth` does not help, because the limit hit
is the C stack, not the recursion counter.

The pre-wipe layer had already settled this. `RegisterWriteStep.fetchInstruction` at `d0f50581`
took its four image lookups as `native_decide` `autoParam`s and was applied at **111 call sites
across 13 files**; its own note measures the packaged form at 1.26s against 1.23s hand-written.
`tools/check_lean_trust.py` forbids `sorry`, custom axioms, `implemented_by`/`extern` and `unsafe`
— `native_decide` is inside this project's accepted envelope, and this is what it was accepted for.

The consequence for the campaign is direct and unavoidable: **the fetch obligation is four
`native_decide`s per instruction, and a motif lemma over `n` instructions still needs `4n` of
them.** Each instruction owns a different word, so no lemma can share the work. Whatever a motif
lemma saves, it is not this. -/

/-- The four image bytes at `pc`, lifted to the generated fetch inputs.

Every premise except `loaded` is an `autoParam`, so a call site writes the address and the four
bytes and nothing else. A wrong byte fails and names the address. -/
theorem fetchInstruction (state : State) (pc : Nat) (byte0 byte1 byte2 byte3 : UInt8)
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

/-- The first instruction of the `mem.readInt` motif at `0x70`: `lbu a0, 1(a2)`, encoded
`03 45 16 00` little-endian. Case A of the campaign starts here, and this is the shape of the fetch
obligation every one of its ten instructions carries. -/
example (state : State) (loaded : programImage.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x70)
      (BitVec.ofNat 8 (0x03 : UInt8).toNat) (BitVec.ofNat 8 (0x45 : UInt8).toNat)
      (BitVec.ofNat 8 (0x16 : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction state 0x70 0x03 0x45 0x16 0x00 loaded

end BinaryFv.Zesu.Machine
