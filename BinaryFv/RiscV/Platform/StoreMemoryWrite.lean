import BinaryFv.RiscV.Logic.Framing

/-!
# Store physical-write chain contract

This module proves that the generated Sail physical-write chain

  `mem_write_value_priv_meta` → `checked_mem_write` → `write_ram` → `sail_mem_write`

runs successfully under abstracted access-control preconditions, and that its only
state effect is the underlying `PreSail.writeBytes` at the physical address.

The access-control facts (`phys_access_check` returning `none`, `within_mmio_writable`
returning `false`) are supplied as `Runs` hypotheses rather than unfolded, keeping the
generated permission logic abstract. The concrete post-state `s'` is pinned by the
`writeBytes` hypothesis, which is threaded through every `bind`.

Two deviations from the stated goal, forced by the generated definitions:

* `physaddr` is an inductive with a single anonymous field, so there is no `paddr.toNat`;
  the physical address that `write_ram`/`sail_mem_write` actually use is
  `(bits_of_physaddr paddr).toNat`, which is what the hypotheses talk about.
* `write_ram` reduces the `internal_error` branches to a `throw` for the two "release"
  write kinds, so it only runs to `true` for `Write_plain` (and the conditional kinds).
  `write_ram_store_run` is therefore stated for `Write_plain` — exactly the kind the store
  chain produces via `write_kind_of_flags false false false`.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open mem_payload
open write_kind

/-- `Runs` of a `pure` leaves the state fixed and returns the pure value. -/
theorem run_pure {α : Type} (s : State) (x : α) : Runs (pure x) s s x := rfl

/-- `write_kind_of_flags false false false` runs purely to `Write_plain`. -/
theorem write_kind_of_flags_plain_run (s : State) :
    Runs (write_kind_of_flags false false false) s s Write_plain := rfl

/-- The generated `sail_mem_write`, on a request that stores `data`, reduces to the
underlying `writeBytes` at the request's physical address and succeeds. -/
theorem sail_mem_write_store_run [Sail.ConcurrencyInterfaceV1.Arch]
    (request : Sail.ConcurrencyInterfaceV1.Mem_write_request n vasize (BitVec pa_size) ts Arch)
    (data : BitVec (8 * n)) (s s' : State)
    (hval : request.value = some data)
    (hwrite : Runs (PreSail.writeBytes request.pa.toNat data) s s' true) :
    Runs (PreSail.ConcurrencyInterfaceV1.sail_mem_write request) s s' (.Ok (some true)) := by
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_write
  simp only [hval]
  exact Runs.bind hwrite (run_pure s' _)

/-- The generated `write_ram`, for a plain write, runs to `true` with the only state
effect being `writeBytes` at the physical address. -/
theorem write_ram_store_run (s s' : State) (paddr : physaddr) {width : Nat}
    (data : BitVec (8 * width))
    (hwrite : Runs (PreSail.writeBytes (bits_of_physaddr paddr).toNat data) s s' true) :
    Runs (write_ram Write_plain paddr width data ()) s s' true := by
  obtain ⟨addr⟩ := paddr
  unfold LeanRV64DExecutable.Functions.write_ram
  refine Runs.bind (show Runs _ s s _ from rfl) ?_
  refine Runs.bind (sail_mem_write_store_run _ data s s' rfl hwrite) ?_
  rfl

/-- The generated `checked_mem_write` for a data store, given that access control permits
the write (`phys_access_check` → `none`) and the target is not MMIO
(`within_mmio_writable` → `false`), runs to `.Ok true` with only the `writeBytes` effect. -/
theorem checked_mem_write_store_run (s s' : State) (paddr : physaddr) {width : Nat}
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (priv : Privilege)
    (physAccess :
      Runs (phys_access_check (Store Data) pbmt priv paddr width false) s s none)
    (noMMIO : Runs (within_mmio_writable paddr width) s s false)
    (hwrite : Runs (PreSail.writeBytes (bits_of_physaddr paddr).toNat data) s s' true) :
    Runs (checked_mem_write paddr width data (Store Data) pbmt priv () false false false)
      s s' (.Ok true) := by
  unfold checked_mem_write
  refine Runs.bind physAccess ?_
  refine Runs.bind noMMIO ?_
  refine Runs.bind (write_kind_of_flags_plain_run s) ?_
  refine Runs.bind (write_ram_store_run s s' paddr data hwrite) ?_
  rfl

/-- The top of the physical-write chain, `mem_write_value_priv_meta`, for an aligned-guard-free
data store (`rl = con = false`), runs to `.Ok true` with only the `writeBytes` effect. -/
theorem mem_write_value_priv_store_run (s s' : State) (paddr : physaddr) {width : Nat}
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (priv : Privilege)
    (physAccess :
      Runs (phys_access_check (Store Data) pbmt priv paddr width false) s s none)
    (noMMIO : Runs (within_mmio_writable paddr width) s s false)
    (hwrite : Runs (PreSail.writeBytes (bits_of_physaddr paddr).toNat data) s s' true) :
    Runs (mem_write_value_priv_meta paddr width data (Store Data) pbmt priv () false false false)
      s s' (.Ok true) := by
  unfold mem_write_value_priv_meta
  refine Runs.bind
    (checked_mem_write_store_run s s' paddr data pbmt priv physAccess noMMIO hwrite) ?_
  rfl

end BinaryFv.RiscV
