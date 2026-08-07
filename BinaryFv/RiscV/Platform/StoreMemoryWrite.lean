import BinaryFv.RiscV.Logic.Framing
import Std.Data.ExtHashMap.Lemmas

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

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open mem_payload
open write_kind

/-- `Runs` of a `pure` leaves the state fixed and returns the pure value. -/
theorem run_pure {α : Type} (s : State) (x : α) : Runs (pure x) s s x := rfl

/-- Apply a sequence of sparse-memory byte writes to a state, in program order. -/
def afterByteWrites (state : State) (writes : List (Nat × BitVec 8)) : State :=
  writes.foldl (fun current write =>
    { current with mem := current.mem.insert write.1 write.2 }) state

theorem writeByteList_run (writes : List (Nat × BitVec 8)) (state : State) :
    Runs (writes.forM fun write => PreSail.writeByte write.1 write.2)
      state (afterByteWrites state writes) () := by
  induction writes generalizing state with
  | nil => rfl
  | cons write writes ih =>
      unfold afterByteWrites List.foldl
      exact Runs.bind (writeByte_run state write.1 write.2)
        (by simpa [afterByteWrites] using
          ih { state with mem := state.mem.insert write.1 write.2 })

theorem afterByteWrites_regs (state : State) (writes : List (Nat × BitVec 8)) :
    (afterByteWrites state writes).regs = state.regs := by
  induction writes generalizing state with
  | nil => rfl
  | cons write writes ih =>
      simpa [afterByteWrites] using
        ih { state with mem := state.mem.insert write.1 write.2 }

theorem afterByteWrites_mem_get?_of_not_written (state : State)
    (writes : List (Nat × BitVec 8)) (address : Nat)
    (notWritten : ∀ write ∈ writes, write.1 ≠ address) :
    (afterByteWrites state writes).mem.get? address = state.mem.get? address := by
  induction writes generalizing state with
  | nil => rfl
  | cons write writes ih =>
      have head : write.1 ≠ address := notWritten write (by simp)
      have tail : ∀ tailWrite ∈ writes, tailWrite.1 ≠ address := by
        intro tailWrite member
        exact notWritten tailWrite (by simp [member])
      change (afterByteWrites { state with mem := state.mem.insert write.1 write.2 }
        writes).mem.get? address = state.mem.get? address
      rw [ih { state with mem := state.mem.insert write.1 write.2 } tail]
      change (state.mem.insert write.1 write.2).get? address = state.mem.get? address
      simp [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, head]

theorem fileBytesLoadedFaithfully_afterByteWrites (image : ProgramImage)
    (state : State) (writes : List (Nat × BitVec 8))
    (notFileBacked : ∀ write ∈ writes, image.readFileByte? write.1 = none)
    (code : image.fileBytesLoadedFaithfully state.mem) :
    image.fileBytesLoadedFaithfully (afterByteWrites state writes).mem := by
  induction writes generalizing state with
  | nil => simpa [afterByteWrites] using code
  | cons write writes ih =>
      have headNotFile : image.readFileByte? write.1 = none :=
        notFileBacked write (by simp)
      have tailNotFile : ∀ tailWrite ∈ writes,
          image.readFileByte? tailWrite.1 = none := by
        intro tailWrite member
        exact notFileBacked tailWrite (by simp [member])
      have afterHead := image.fileBytesLoadedFaithfully_insert_non_file
        (value := write.2) headNotFile code
      simpa [afterByteWrites] using
        ih { state with mem := state.mem.insert write.1 write.2 } tailNotFile afterHead

/-- Exact post-state of the generated fixed-width little-endian memory write. -/
def afterWriteBytes (state : State) (address : Nat) {width : Nat}
    (value : BitVec (8 * width)) : State :=
  afterByteWrites state
    (List.ofFn fun index : Fin width =>
      (address + index.val, value.extractLsb' (8 * index.val) 8))

theorem writeBytes_run_exact (state : State) (address : Nat) {width : Nat}
    (value : BitVec (8 * width)) :
    Runs (PreSail.writeBytes address value) state (afterWriteBytes state address value) true := by
  unfold PreSail.writeBytes afterWriteBytes
  exact Runs.bind (writeByteList_run _ state) rfl

theorem afterWriteBytes_regs (state : State) (address : Nat) {width : Nat}
    (value : BitVec (8 * width)) :
    (afterWriteBytes state address value).regs = state.regs :=
  afterByteWrites_regs state _

theorem afterWriteBytes_mem_get?_of_outside (state : State) (address : Nat) {width : Nat}
    (value : BitVec (8 * width)) (other : Nat)
    (outside : ∀ index : Fin width, address + index.val ≠ other) :
    (afterWriteBytes state address value).mem.get? other = state.mem.get? other := by
  apply afterByteWrites_mem_get?_of_not_written
  intro write member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact outside index

theorem fileBytesLoadedFaithfully_afterWriteBytes (image : ProgramImage)
    (state : State) (address : Nat) {width : Nat} (value : BitVec (8 * width))
    (notFileBacked : ∀ index : Fin width,
      image.readFileByte? (address + index.val) = none)
    (code : image.fileBytesLoadedFaithfully state.mem) :
    image.fileBytesLoadedFaithfully (afterWriteBytes state address value).mem := by
  apply fileBytesLoadedFaithfully_afterByteWrites image state _
  · intro write member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact notFileBacked index
  · exact code

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
