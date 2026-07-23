import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.StateBuilder
import BinaryFv.RiscV.Logic.Framing

/-!
# The built entry state satisfies the exported occurrence's entry binding

`buildZesuEntryState` (see `StateBuilder`) constructs the Sail state the exported `zesu_decode_raw`
call begins from. This module threads `Runs` through the whole builder and reads off the facts the
exported entry binding needs: the input in memory (`MemoryBytes`), the code and rodata intact
(`fileBytesMatchMemory` = the file-backed `CodeIntact`), the C-ABI argument registers, and the return
sentinel.

The threading splits at the one input-independent seam. `configureZesuMachine` is a closed program
(machine setup: `sail_model_init` + M-extension + the pinned PMA region), so its success is a finite
evaluation `native_decide` settles — this is the SSZ layer, where that is permitted, and it sidesteps
hand-threading `sail_model_init`'s ~40 register writes and its `misa`-dependent `legalize_*` reads.
Everything after configure is input-dependent and is threaded with the `ImageLoadFrame` establishment
lemmas: each loader sets its own addresses and frames the complement, so the earlier-established facts
survive because the runner's ranges are pairwise disjoint.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/-! ## The machine configuration succeeds -/

/-- Whether the configuration program runs to a normal (non-error) result from the empty initial
state. A closed finite computation, so `native_decide` settles it. -/
def configureSucceedsB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ _ => true
  | .error _ _ => false

theorem configure_succeeds : configureSucceedsB = true := by native_decide

/-- The machine configuration runs to some state. Its register/CSR values are deliberately left
abstract — the builder's final `writeReg` block pins the ABI registers the entry binding reads, and
the loaders set the memory, so nothing downstream needs the post-configuration register values. -/
theorem configure_runs : ∃ mid, Runs configureZesuMachine initialState mid () := by
  have h := configure_succeeds
  unfold configureSucceedsB at h
  cases hr : configureZesuMachine.run initialState with
  | error e s => rw [hr] at h; simp at h
  | ok u s =>
    refine ⟨s, ?_⟩
    show configureZesuMachine.run initialState = .ok () s
    rw [hr]

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
