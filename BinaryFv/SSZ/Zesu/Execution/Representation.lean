import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.SSZ.Zesu.Artifact.AbiManifest

namespace BinaryFv.SSZ.Zesu.Execution

open BinaryFv.RiscV

/-- A half-open, bytewise region of generated Sail sparse memory. -/
def MemoryBytes (state : State) (base : Nat) (bytes : ByteArray) : Prop :=
  ∀ index (h : index < bytes.size),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 (bytes[index]'h).toNat)

/-- A decoder slice that aliases caller-owned input rather than copying it into the heap. -/
def InputSliceRep (state : State) (inputBase inputOffset length sliceBase : Nat) : Prop :=
  sliceBase = inputBase + inputOffset ∧
    ∀ index, index < length → state.mem.get? (sliceBase + index) = state.mem.get? (inputBase + inputOffset + index)

/-- A heap array is a disjoint materialized sequence of fixed-width records. -/
def HeapArrayRep (state : State) (base count elementSize : Nat) : Prop :=
  base + count * elementSize ≤ 2 ^ 64 ∧
    ∀ index, index < count * elementSize → (state.mem.get? (base + index)).isSome

/-- The decoded root object occupies precisely the compiler-reflected RV64 ABI size. -/
def RawStatelessInputRep (state : State) (base : Nat) : Prop :=
  ∃ size, Artifact.rawStatelessInputSize = some size ∧ HeapArrayRep state base 1 size

theorem raw_stateless_input_rep_size (state : State) (base : Nat)
    (representation : RawStatelessInputRep state base) : HeapArrayRep state base 1 832 := by
  rcases representation with ⟨size, sizeH, representation⟩
  rw [Artifact.raw_stateless_input_layout.1] at sizeH
  injection sizeH with sizeH
  subst size
  exact representation

end BinaryFv.SSZ.Zesu.Execution
