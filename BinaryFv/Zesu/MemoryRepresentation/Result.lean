import BinaryFv.Zesu.MemoryRepresentation.RawV4

namespace BinaryFv.Zesu.MemoryRepresentation

open BinaryFv.RiscV

/-- A little-endian 16-bit Zesu result status in Sail sparse memory. -/
def ResultStatusLERep (state : State) (base status : Nat) : Prop :=
  status < 2 ^ 16 ∧
    state.mem.get? base = some (BitVec.ofNat 8 (status % 256)) ∧
      state.mem.get? (base + 1) = some (BitVec.ofNat 8 ((status / 256) % 256))

/-- Guarded result-status accessor used after `zesu_decode_raw` returns. -/
def observeResultStatus? (state : State) (resultBase : Nat) : Option Nat := do
  let low ← state.mem.get? (resultBase + 832)
  let high ← state.mem.get? (resultBase + 833)
  pure (low.toNat + 256 * high.toNat)

theorem observe_result_status_of_rep (state : State) (resultBase status : Nat)
    (representation : ResultStatusLERep state (resultBase + 832) status) :
    observeResultStatus? state resultBase = some status := by
  rcases representation with ⟨bound, low, high⟩
  unfold observeResultStatus?
  rw [low]
  have high' : state.mem.get? (resultBase + 832 + 1) =
      some (BitVec.ofNat 8 ((status / 256) % 256)) := by
    simpa [Nat.add_assoc] using high
  rw [high']
  simp
  omega

/-- A successful Zesu result carries a represented root payload followed by status zero. -/
structure RawV4SuccessResultRep (state : State) (inputBase : Nat) (input : ByteArray)
    (resultBase : Nat) (value : SszBridge.RawV4) : Prop where
  root : RawV4Rep state inputBase input resultBase value
  status : ResultStatusLERep state (resultBase + 832) 0

theorem observe_raw_v4_success_status (state : State) (inputBase : Nat) (input : ByteArray)
    (resultBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4SuccessResultRep state inputBase input resultBase value) :
    observeResultStatus? state resultBase = some 0 :=
  observe_result_status_of_rep state resultBase 0 representation.status

end BinaryFv.Zesu.MemoryRepresentation
