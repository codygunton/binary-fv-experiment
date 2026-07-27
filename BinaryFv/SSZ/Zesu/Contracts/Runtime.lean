import BinaryFv.SSZ.Zesu.Contracts.Entry
import BinaryFv.SSZ.Zesu.Contracts.ExportedDecoder
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
null and leaves the cursor alone.

The success arm bounds *how far* the cursor advances, not merely that it does. Without that clause
"advances the cursor" is only a docstring, and no amount of composing allocations could conclude the
arena does not fill — which is the whole content of the out-of-memory obligation. The bound is
`(alignment - 1) + bytes` rather than `bytes` because the bump allocator inserts alignment padding;
`Runtime.allocate_delta_le` is the matching fact about the pure model.

This is a strengthening: it adds an obligation to whoever proves the allocator implements its
contract, and gives callers a fact they did not have. Non-allocating routines need no analogue —
`NoAllocation` already pins every allocator-state byte, so `cursor_eq_of_noAllocation` derives their
zero delta. -/
def postAlloc (env : DecoderEnvironment) (args : AllocArgs)
    (result : Except SszDecodeError Nat) (before after : State) : Prop :=
  env.CodeIntact after ∧
  match result with
  | .ok address =>
      address ≠ 0 ∧ args.alignment ≠ 0 ∧ address % args.alignment = 0 ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 address) ∧
      ∃ cursorBefore cursorAfter,
        env.cursor? before = some cursorBefore ∧ env.cursor? after = some cursorAfter ∧
        cursorBefore ≤ cursorAfter ∧
        cursorAfter - cursorBefore ≤ (args.alignment - 1) + args.bytes ∧
        -- **The allocation is where the cursor moved.** Without this, `address` and the cursor pair
        -- appear in this same postcondition and are never related: the contract would permit an
        -- allocator that advances the cursor correctly and returns an aligned address *anywhere*.
        --
        -- Load-bearing, not tidiness. The ownership discipline needs `record ⊆ its own interval` to
        -- collapse sibling disjointness from quadratic to linear; that fact is true of
        -- `Runtime.allocate` (`BumpAllocator.lean:16-22` returns `position + padding` and sets
        -- `position' = address + bytes`) but was **not derivable from this contract**, so a
        -- composition consuming contracts could not use it.
        --
        -- Stated with `≤` rather than the equality the model happens to give, so an allocator that
        -- pads *after* the block still satisfies it.
        cursorBefore ≤ address ∧ address + args.bytes ≤ cursorAfter ∧
        -- **The ownership clause, at the one place the cursor pair was already bound.** The
        -- allocator's permitted region is the interval it just consumed, its own mutable state, and
        -- its stack frame. Neither of the last two is slack: advancing `ZKVM_HEAP_POS` is the memory
        -- write `Runtime.allocate` models and that address is in `allocatorState` rather than in the
        -- interval, and the compiled `zesu_raw_alloc` writes a frame like any other routine. The
        -- record component is empty because `zesu_raw_alloc` hands back a block it does not
        -- initialize; the block itself is inside the interval anyway, by the containment clause
        -- immediately above.
        WritesOnlyWithin (env.ownedRegion 0 0 cursorBefore cursorAfter) before after
  | .error error =>
      error = SszDecodeError.outOfMemory ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 0) ∧
      env.NoAllocation before after ∧
      -- Exhaustion allocates nothing and produces no block: the permission is its stack frame alone.
      env.WritesOnlyWithinOwnRecord 0 0 before after

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
  -- A copy's record is its destination block, and its length is a genuine runtime argument, so this
  -- is the one place the ownership clause needed no new ABI fact at all. The stack frame the compiled
  -- `memcpy` uses is permitted by `WritesOnlyWithinOwnRecord`, not by the destination range.
  env.WritesOnlyWithinOwnRecord args.destination args.length before after ∧
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
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractAlloc env heap)

def correctnessClaimMemcpy (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractMemcpy env)

def correctnessClaimMemmove (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractMemmove env)

def satisfiableAlloc (env : DecoderEnvironment) (heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractAlloc env heap)

def satisfiableMemcpy (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractMemcpy env)

def satisfiableMemmove (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractMemmove env)

/-!
## Exported accessors as contracts

`zesu_raw_result` and `zesu_raw_error` are exported symbols, so they get full contracts like every
other cataloged routine rather than bare predicates. Both read the private decoder globals rather
than taking arguments: their `Args` is the ghost `DecoderGlobalsModel` those globals represent, and
their entry binding *requires canonical global memory to represent it*. Neither takes the borrowed
input, neither allocates, and neither can fail: their `meaning` is total. These ghost values are not
ABI arguments — they name what the shared globals already hold.
-/

/-- `zesu_raw_error` returns the recorded 32-bit status held in the decoder globals. -/
def postRawError (env : DecoderEnvironment) (model : DecoderGlobalsModel)
    (result : Except SszDecodeError Nat) (before after : State) : Prop :=
  env.CodeIntact after ∧ env.NoAllocation before after ∧
  -- An accessor reads the globals and returns in `a0`; it owns no record, so the clause is at the
  -- empty record — its strongest instance, not a placeholder. It still permits the stack frame the
  -- compiled accessor writes, which is the difference between a strong clause and an unsatisfiable
  -- one.
  env.WritesOnlyWithinOwnRecord 0 0 before after ∧
  match result with
  | .ok code => code = model.status.code ∧ after.regs.get? x10 = some (BitVec.ofNat 64 code)
  | .error _ => False

def contractRawError (env : DecoderEnvironment) (globals : DecoderGlobalsLayout) :
    FunctionContract SszDecodeError DecoderGlobalsModel Nat where
  meaning := fun model => .ok model.status.code
  pre := fun model state => env.CodeIntact state ∧ DecoderGlobalsScalarRep globals model state
  post := postRawError env
  stepBound := fun _ => 16

/-- `zesu_raw_result` returns the address of the inline stored-result payload when a value is present,
and null otherwise. -/
def postRawResult (env : DecoderEnvironment) (resultBuffer : Nat) (model : DecoderGlobalsModel)
    (result : Except SszDecodeError Nat) (before after : State) : Prop :=
  env.CodeIntact after ∧ env.NoAllocation before after ∧
  -- Returns the *address* of the stored result and produces no record: the clause is at the empty
  -- record even though `resultBuffer` is in scope, so it permits nothing but the stack frame.
  env.WritesOnlyWithinOwnRecord 0 0 before after ∧
  match result with
  | .ok pointer =>
      pointer = (if model.stored.isSome then resultBuffer else 0) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 pointer)
  | .error _ => False

def contractRawResult (env : DecoderEnvironment) (globals : DecoderGlobalsLayout) (resultBuffer : Nat) :
    FunctionContract SszDecodeError DecoderGlobalsModel Nat where
  meaning := fun model => .ok (if model.stored.isSome then resultBuffer else 0)
  pre := fun model state =>
    env.CodeIntact state ∧ StoredResultDiscriminantRep globals model state
  post := postRawResult env resultBuffer
  stepBound := fun _ => 32

def correctnessClaimRawError (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractRawError env globals)

def correctnessClaimRawResult (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractRawResult env globals resultBuffer)

def satisfiableRawError (env : DecoderEnvironment) (globals : DecoderGlobalsLayout) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractRawError env globals)

def satisfiableRawResult (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractRawResult env globals resultBuffer)

/-!
## Allocator vtable routines

`allocatorAlloc` forwards to `zesu_raw_alloc`; the other three vtable thunks are constant
(`allocatorResize` fails, `allocatorRemap` fails, `allocatorFree` is a no-op), and `allocator`
constructs the `std.mem.Allocator` value. Each is cataloged with a contract so the coverage proof
can account for every reachable runtime routine rather than leaving the allocator closure implicit.
-/

/-- `allocatorResize` unconditionally returns `false`; it neither reads nor writes memory. -/
def contractAllocatorResize (env : DecoderEnvironment) :
    FunctionContract SszDecodeError Unit Bool where
  meaning := fun _ => .ok meaningAllocatorResize
  pre := fun _ state => env.CodeIntact state
  post := fun _ result before after =>
    env.CodeIntact after ∧ env.NoAllocation before after ∧
      result = .ok false ∧ after.regs.get? x10 = some (BitVec.ofNat 64 0)
  stepBound := fun _ => 8

/-- `allocatorRemap` unconditionally returns `null`. -/
def contractAllocatorRemap (env : DecoderEnvironment) :
    FunctionContract SszDecodeError Unit Nat where
  meaning := fun _ => .ok 0
  pre := fun _ state => env.CodeIntact state
  post := fun _ result before after =>
    env.CodeIntact after ∧ env.NoAllocation before after ∧
      result = .ok 0 ∧ after.regs.get? x10 = some (BitVec.ofNat 64 0)
  stepBound := fun _ => 8

/-- `allocatorFree` is a no-op: it returns nothing and leaves every byte outside its own stack frame,
the allocator state included, exactly as it was.

**This used to state an unrestricted total memory frame, and that was the same defect the ownership
clause was added to remove.** A total frame is satisfiable only by a routine that never touches the
stack — true of a compiled `ret`, false the moment the compiler emits any prologue — so it was one
recompilation away from being an *unsatisfiable* conjunct on an assumed hypothesis, which is how a
conditional root goes vacuous. `env.WritesOnlyWithinOwnRecord 0 0` is the strongest clause a compiled
routine can satisfy, and it still says the allocator state and every caller-visible byte survive
untouched, which is the whole content of "free is a no-op" here. -/
def contractAllocatorFree (env : DecoderEnvironment) :
    FunctionContract SszDecodeError Unit Unit where
  meaning := fun _ => .ok ()
  pre := fun _ state => env.CodeIntact state
  post := fun _ result before after =>
    env.CodeIntact after ∧ env.NoAllocation before after ∧
      env.WritesOnlyWithinOwnRecord 0 0 before after ∧ result = .ok ()
  stepBound := fun _ => 8

/-- `allocatorAlloc(len, alignment)` is the vtable thunk that forwards to `zesu_raw_alloc`, so its
contract is the allocation contract under the same `heap`. -/
def contractAllocatorAlloc (env : DecoderEnvironment) (heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap) :
    FunctionContract SszDecodeError AllocArgs Nat :=
  contractAlloc env heap

/-- `allocator()` constructs the `std.mem.Allocator` value: a context pointer and the static vtable
address. It performs no allocation. -/
structure AllocatorCtorArgs where
  contextBase : Nat
  vtableBase : Nat
  resultBase : Nat

/-- **The ownership clause, at the one contract in the layer that was writing a record without
one.** `allocator()` publishes the two-word `std.mem.Allocator` value at `args.resultBase` and its
postcondition said nothing about anything else it might write — the hole `postFixedContainer` and the
leaf readers had closed and this had not. The record is `env.record.allocatorObject`, exactly the
span `AllocatorObjectRep` pins, so the size is the one the representation already commits to rather
than a fresh guess. -/
def contractAllocatorCtor (env : DecoderEnvironment) :
    FunctionContract SszDecodeError AllocatorCtorArgs Unit where
  meaning := fun _ => .ok ()
  pre := fun _ state => env.CodeIntact state
  post := fun args result before after =>
    env.CodeIntact after ∧ env.NoAllocation before after ∧
      env.WritesOnlyWithinOwnRecord args.resultBase env.record.allocatorObject before after ∧
      result = .ok () ∧
      AllocatorObjectRep after args.resultBase args.contextBase args.vtableBase
  stepBound := fun _ => 16

def correctnessClaimAllocatorResize (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractAllocatorResize env)

def correctnessClaimAllocatorRemap (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractAllocatorRemap env)

def correctnessClaimAllocatorFree (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractAllocatorFree env)

def correctnessClaimAllocatorAlloc (env : DecoderEnvironment)
    (heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractAllocatorAlloc env heap)

def correctnessClaimAllocatorCtor (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractAllocatorCtor env)

def satisfiableAllocatorResize (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractAllocatorResize env)

def satisfiableAllocatorRemap (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractAllocatorRemap env)

def satisfiableAllocatorFree (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractAllocatorFree env)

def satisfiableAllocatorAlloc (env : DecoderEnvironment)
    (heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractAllocatorAlloc env heap)

def satisfiableAllocatorCtor (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractAllocatorCtor env)

/-- The three non-`alloc` vtable entries are constant, so the decoder never reuses or frees memory
and the global allocation bound is a plain sum over allocation sites.

**What this does not establish.** It is `rfl`: `meaningAllocatorResize` and `meaningAllocatorRemap`
are *defined* as `false` and `none` just above, so the conjunct is `false = false ∧ none = none` and
carries no information about the binary. What it records is the catalog's *choice* of meaning for
those two routines; the obligation that the compiled vtable entries really return those constants is
the function instance contract's, discharged by the local proof, not here. It is kept as a conjunct so the
choice is reviewed rather than buried in two definitions. -/
def allocatorVtableEntriesAreConstant : Prop :=
  meaningAllocatorResize = false ∧ meaningAllocatorRemap = none

/--
Out-of-memory is unreachable below the root theorem's input bound.

Every allocation the decoder performs is bounded by a function of the input length, so a heap sized
for 2 MiB of input cannot be exhausted.

**What this does not establish, and it is less than the name suggests.** It is stated against
`meaningDecode`, which is built from pure reads and the oracle and has **no allocation-failure
outcome at all** — so it holds for a reason that has nothing to do with the arena, and the scope
hypothesis goes unused. It does **not** discharge the entry contract's `outOfMemory` arm. That arm is
about the machine, and the theorem that closes it is `raw_allocation_bound_fits_arena` in
`Runtime.AllocationBound`. This conjunct is the specification-side half: it says the *meaning* the
binary is being held to never demands an allocation failure, so an exhausted arena can only ever be a
divergence from the spec rather than agreement with it. -/
def outOfMemoryUnreachableBelowBound : Prop :=
  ∀ (bytes : ByteArray), rootComplianceScope bytes →
    meaningDecode bytes ≠ .error .outOfMemory

end BinaryFv.SSZ.Zesu.Contracts
