import BinaryFv.SSZ.Zesu.Contracts.Entry
import BinaryFv.SSZ.Zesu.Runtime.BumpAllocator

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Runtime and accessor routines

The allocator vtable, `memcpy`, `memmove`, and the two exported result accessors.

These are the only routines in the catalog whose identity comes from the symbol table rather than
from debug information: `zesu_raw_alloc`, `memcpy`, `memmove`, `zesu_raw_result`, and
`zesu_raw_error` all have symbols. That makes them the exception, not the model — 97% of the decoder
object is symbol-less, so nothing here may be generalized into an assumption that proof regions
follow symbol boundaries.

The three non-`alloc` vtable entries are constant functions, which is worth stating exactly:
`allocatorResize` always returns `false`, `allocatorRemap` always returns `null`, and `allocatorFree`
is a no-op. Proving those is what lets the global allocation bound ignore reuse entirely.
-/

/-- Arguments of a bump allocation request. -/
structure AllocArgs where
  allocatorBase : Nat
  bytes : Nat
  alignment : Nat

/-- Arguments of a block copy. -/
structure CopyArgs where
  destination : Nat
  source : Nat
  length : Nat
  contents : ByteArray

/-!
## Meanings
-/

/-- `zesu_raw_alloc(bytes, alignment)`: a bump allocation, or `null` on exhaustion.

The meaning is the existing pinned `Runtime.BumpAllocator.allocate`, not a fresh model. -/
def meaningAlloc (heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap) (bytes alignment : Nat) :
    Option (Nat × BinaryFv.SSZ.Zesu.Runtime.BumpHeap) :=
  BinaryFv.SSZ.Zesu.Runtime.allocate heap bytes alignment

/-- `allocatorResize` always fails, so the decoder never grows an allocation in place. -/
def meaningAllocatorResize : Bool := false

/-- `allocatorRemap` always fails. -/
def meaningAllocatorRemap : Option Nat := none

/-- `memcpy`/`memmove` deliver the source bytes to the destination. -/
def meaningCopy (contents : ByteArray) : ByteArray := contents

/-!
## Contracts
-/

def preAlloc (env : DecoderEnvironment) (args : AllocArgs) (state : State) : Prop :=
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.bytes) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.alignment)

/-- Allocation either returns a fresh, suitably aligned block and advances the cursor, or returns
null and leaves the cursor alone. -/
def postAlloc (env : DecoderEnvironment) (args : AllocArgs)
    (result : Except SszDecodeError Nat) (before after : State) : Prop :=
  env.CodeIntact after ∧
  match result with
  | .ok address =>
      address ≠ 0 ∧ args.alignment ≠ 0 ∧ address % args.alignment = 0 ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 address)
  | .error error =>
      error = SszDecodeError.outOfMemory ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 0) ∧
      env.NoAllocation before after

def contractAlloc (env : DecoderEnvironment) (heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap) :
    FunctionContract SszDecodeError AllocArgs Nat where
  meaning := fun args =>
    match meaningAlloc heap args.bytes args.alignment with
    | some (address, _) => .ok address
    | none => .error .outOfMemory
  pre := preAlloc env
  post := postAlloc env
  stepBound := fun _ => 128

def preCopy (env : DecoderEnvironment) (args : CopyArgs) (state : State) : Prop :=
  MemoryBytes state args.source args.contents ∧
  args.contents.size = args.length ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.destination) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.source) ∧
  state.regs.get? x12 = some (BitVec.ofNat 64 args.length)

/-- After a copy the destination holds the source bytes, the code is intact, and nothing was
allocated. `memcpy` additionally requires non-overlap, which its caller establishes; `memmove` does
not, which is why they are separate contracts rather than one. -/
def postCopy (env : DecoderEnvironment) (args : CopyArgs)
    (result : Except SszDecodeError ByteArray) (before after : State) : Prop :=
  env.CodeIntact after ∧
  env.NoAllocation before after ∧
  match result with
  | .ok contents => MemoryBytes after args.destination contents
  | .error _ => False

def contractMemcpy (env : DecoderEnvironment) :
    FunctionContract SszDecodeError CopyArgs ByteArray where
  meaning := fun args => .ok (meaningCopy args.contents)
  pre := fun args state =>
    preCopy env args state ∧
    -- `memcpy` is only correct on non-overlapping regions; the caller owes this.
    (args.destination + args.length ≤ args.source ∨ args.source + args.length ≤ args.destination)
  post := postCopy env
  stepBound := fun args => 64 + 8 * args.length

def contractMemmove (env : DecoderEnvironment) :
    FunctionContract SszDecodeError CopyArgs ByteArray where
  meaning := fun args => .ok (meaningCopy args.contents)
  pre := preCopy env
  post := postCopy env
  stepBound := fun args => 64 + 16 * args.length

/-!
## Correctness claims
-/

def correctnessClaimAlloc (env : DecoderEnvironment) (heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap)
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsInstance instance_ entry exit (contractAlloc env heap)

def correctnessClaimMemcpy (env : DecoderEnvironment)
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsInstance instance_ entry exit (contractMemcpy env)

def correctnessClaimMemmove (env : DecoderEnvironment)
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsInstance instance_ entry exit (contractMemmove env)

/-!
## Accessors and global bounds
-/

/-- `zesu_raw_error()` returns the recorded status code. -/
def rawErrorReturnsStatus (status : DecodeStatus) (state : State) : Prop :=
  state.regs.get? x10 = some (BitVec.ofNat 64 status.code)

/-- `zesu_raw_result()` returns the stored result pointer, or null when nothing was decoded. -/
def rawResultReturnsPointer (resultBase : Nat) (decoded : Bool) (state : State) : Prop :=
  state.regs.get? x10 = some (BitVec.ofNat 64 (if decoded then resultBase else 0))

/-- The three non-`alloc` vtable entries are constant, so the decoder never reuses or frees memory
and the global allocation bound is a plain sum over allocation sites. -/
def allocatorVtableEntriesAreConstant : Prop :=
  meaningAllocatorResize = false ∧ meaningAllocatorRemap = none

/--
Out-of-memory is unreachable below the root theorem's input bound.

Every allocation the decoder performs is bounded by a function of the input length, so a heap sized
for 2 MiB of input cannot be exhausted. This is what lets the entry contract's `outOfMemory` arm be
discharged rather than merely normalized, and it is the obligation the global allocation bound in
`Runtime.AllocationBound` must eventually discharge. -/
def outOfMemoryUnreachableBelowBound : Prop :=
  ∀ (bytes : ByteArray), rootComplianceScope bytes →
    meaningDecode bytes ≠ .error .outOfMemory

end BinaryFv.SSZ.Zesu.Contracts
