import BinaryFv.Zesu.Contracts.Canonicality

namespace BinaryFv.Zesu.Contracts

open SizzLean.Spec
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.DecodedValue
open LeanRV64DExecutable.Functions Register

/-!
# Collection decoders

The fixed-stride collections (`decodeVersionedHashes`, `decodeWithdrawals`, the three request
families, `decodePublicKeys`) and the one offset-table collection, `decodeByteListList`.

Every source function here **allocates**, so unlike the option and leaf families their postconditions must
describe the allocation rather than deny it. `decodeByteListList` allocates even for a zero-length
input: the source's `if (data.len == 0) return alloc.alloc([]const u8, 0)` takes the allocator path.

`decodeByteListList` is also the only source function with a genuine loop, and its guard is subtler than it
looks — the source assigns `previous = start`, not `previous = end`. The invariant it maintains is
therefore *nondecreasing starts*, not disjointness or non-overlap. The contract states it as written;
stating the "obviously intended" stronger version would be unprovable against the actual binary.
-/

/-- Arguments of an allocating collection decoder.

`allocatorBase` is the allocator object the caller passes; the result descriptor is written through
`resultBase`. Both are genuine runtime arguments. -/
structure CollectionArgs where
  base : Nat
  bytes : ByteArray
  allocatorBase : Nat
  resultBase : Nat

/-!
## Meanings

Each fixed-stride collection is `decodeCanonical` at its element list schema. The Zig stride and
count bound are not restated here: they are consequences of the schema, and duplicating them would
create a second source of truth that could drift.
-/

def versionedHashesType : SSZType :=
  .list (BinaryFv.Specs.SSZ.byteVector 32) BinaryFv.Specs.SSZ.maxBlobCommitmentsPerBlock

def withdrawalsType : SSZType :=
  .list BinaryFv.Specs.SSZ.withdrawalType BinaryFv.Specs.SSZ.maxWithdrawalsPerPayload

def depositRequestsType : SSZType :=
  .list BinaryFv.Specs.SSZ.depositRequestType BinaryFv.Specs.SSZ.maxDepositRequestsPerPayload

def withdrawalRequestsType : SSZType :=
  .list BinaryFv.Specs.SSZ.withdrawalRequestType BinaryFv.Specs.SSZ.maxWithdrawalRequestsPerPayload

def consolidationRequestsType : SSZType :=
  .list BinaryFv.Specs.SSZ.consolidationRequestType BinaryFv.Specs.SSZ.maxConsolidationRequestsPerPayload

def publicKeysType : SSZType :=
  .list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys

def meaningVersionedHashes (bytes : ByteArray) :
    Except DecodeError (Array (BinaryFv.Specs.SSZ.RawByteVector 32)) :=
  match BinaryFv.Specs.SSZ.decodeCanonical versionedHashesType bytes with
  | .ok value => .ok value.1
  | .error error => .error (sszToDecodeError error)

def meaningWithdrawals (bytes : ByteArray) :
    Except DecodeError (Array BinaryFv.Specs.SSZ.RawWithdrawal) :=
  match BinaryFv.Specs.SSZ.decodeCanonical withdrawalsType bytes with
  | .ok value => .ok (value.1.map BinaryFv.Specs.SSZ.rawWithdrawalOf)
  | .error error => .error (sszToDecodeError error)

def meaningDepositRequests (bytes : ByteArray) :
    Except DecodeError (Array BinaryFv.Specs.SSZ.RawDepositRequest) :=
  match BinaryFv.Specs.SSZ.decodeCanonical depositRequestsType bytes with
  | .ok value => .ok (value.1.map BinaryFv.Specs.SSZ.rawDepositRequestOf)
  | .error error => .error (sszToDecodeError error)

def meaningWithdrawalRequests (bytes : ByteArray) :
    Except DecodeError (Array BinaryFv.Specs.SSZ.RawWithdrawalRequest) :=
  match BinaryFv.Specs.SSZ.decodeCanonical withdrawalRequestsType bytes with
  | .ok value => .ok (value.1.map BinaryFv.Specs.SSZ.rawWithdrawalRequestOf)
  | .error error => .error (sszToDecodeError error)

def meaningConsolidationRequests (bytes : ByteArray) :
    Except DecodeError (Array BinaryFv.Specs.SSZ.RawConsolidationRequest) :=
  match BinaryFv.Specs.SSZ.decodeCanonical consolidationRequestsType bytes with
  | .ok value => .ok (value.1.map BinaryFv.Specs.SSZ.rawConsolidationRequestOf)
  | .error error => .error (sszToDecodeError error)

def meaningPublicKeys (bytes : ByteArray) :
    Except DecodeError (Array (BinaryFv.Specs.SSZ.RawByteVector BinaryFv.Specs.SSZ.publicKeyBytes)) :=
  match BinaryFv.Specs.SSZ.decodeCanonical publicKeysType bytes with
  | .ok value => .ok value.1
  | .error error => .error (sszToDecodeError error)

/-- `decodeByteListList(data, maxItems, maxItemBytes)`: the SSZ `List[ByteList[b], n]` schema.

`maxItems` and `maxItemBytes` are **runtime arguments** of the one `decodeByteListList` function —
it is a single source function called at four sites (transactions, witness state, codes, headers), not four
functions — so they belong in `ByteListListArgs`, not in the contract's parameters. Collapsing them
into the contract would have implied four separate catalog identities for one source function. -/
def byteListListType (maxItems maxItemBytes : Nat) : SSZType :=
  .list (BinaryFv.Specs.SSZ.byteList maxItemBytes) maxItems

def meaningByteListList (maxItems maxItemBytes : Nat) (bytes : ByteArray) :
    Except DecodeError (Array BinaryFv.Specs.SSZ.RawBytes) :=
  match BinaryFv.Specs.SSZ.decodeCanonical (byteListListType maxItems maxItemBytes) bytes with
  | .ok value => .ok (value.1.map fun item => item.1)
  | .error error => .error (sszToDecodeError error)

/-- Arguments of `decodeByteListList`: a collection call plus its two runtime bounds. -/
structure ByteListListArgs extends CollectionArgs where
  maxItems : Nat
  maxItemBytes : Nat

/-!
## Allocation effects

An allocating source function's postcondition has to say *what* it allocated, not merely that memory
changed. `AllocatedDescriptorArray` is the shape every collection produces: a heap array of
`count` elements of `elementSize` bytes, with a slice descriptor at the result pointer.
-/

/-- The source function allocated exactly one array and published a descriptor for it. -/
def AllocatedDescriptorArray (state : State) (resultBase dataBase count elementSize : Nat) : Prop :=
  SliceDescriptorRep state resultBase dataBase count ∧
  HeapArrayRep state dataBase count elementSize

def preCollection (env : DecoderEnvironment) (args : CollectionArgs) (state : State) : Prop :=
  MemoryBytes state args.base args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.resultBase) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
  state.regs.get? x12 = some (BitVec.ofNat 64 args.base) ∧
  state.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size)

/--
The shared shape of a collection postcondition.

`elementSize` is the Zig stride of the produced element, supplied by the caller because it is an ABI
fact. On every path the borrowed input and the code image are preserved; the borrowed-slice
discipline means elements of a byte-list collection *alias* the caller's input rather than copying it.

The error arm admits `invalidSsz` and `outOfMemory` and excludes `unknownFork`: no collection decoder
reads a fork index.

**The ownership clause.** Every collection allocates, so it takes the allocating form: its permitted
region is the slice descriptor it publishes at `args.resultBase`, the arena interval its allocations
consumed, the allocator's own state, and its stack frame. The heap array itself needs no separate mention — it was
allocated by the same call, so it is inside the interval, which is precisely the containment
`postAlloc`'s `cursorBefore ≤ address ∧ address + bytes ≤ cursorAfter` was added to make derivable.
The record is the descriptor, not the array, and `env.record.sliceDescriptor` is its ABI size.

Note `_before` is no longer unused: the clause is the first thing in this predicate that relates the
two states rather than describing `after` absolutely. The docstring on `postEntry` explaining why the
binder was decorative describes the shape these predicates *used* to have.
-/
def postCollection {α : Type} (env : DecoderEnvironment) (args : CollectionArgs)
    (elementSize : Nat) (count : α → Nat)
    (result : Except DecodeError α) (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  env.WritesOnlyWithinOwnAllocation args.resultBase env.record.sliceDescriptor before after ∧
  match result with
  | .ok value =>
      ∃ dataBase,
        AllocatedDescriptorArray after args.resultBase dataBase (count value) elementSize
  | .error error =>
      error = DecodeError.invalidSsz ∨ error = DecodeError.outOfMemory

/-!
## Contracts
-/

def contractVersionedHashes (env : DecoderEnvironment) :
    FunctionContract DecodeError CollectionArgs (Array (BinaryFv.Specs.SSZ.RawByteVector 32)) where
  meaning := fun args => meaningVersionedHashes args.bytes
  pre := preCollection env
  post := fun args => postCollection env args 32 Array.size
  stepBound := fun args => 128 + 64 * (args.bytes.size / 32 + 1)

def contractWithdrawals (env : DecoderEnvironment) :
    FunctionContract DecodeError CollectionArgs (Array BinaryFv.Specs.SSZ.RawWithdrawal) where
  meaning := fun args => meaningWithdrawals args.bytes
  pre := preCollection env
  post := fun args => postCollection env args 44 Array.size
  stepBound := fun args => 128 + 256 * (args.bytes.size / 44 + 1)

def contractDepositRequests (env : DecoderEnvironment) :
    FunctionContract DecodeError CollectionArgs (Array BinaryFv.Specs.SSZ.RawDepositRequest) where
  meaning := fun args => meaningDepositRequests args.bytes
  pre := preCollection env
  post := fun args => postCollection env args 192 Array.size
  stepBound := fun args => 128 + 512 * (args.bytes.size / 192 + 1)

def contractWithdrawalRequests (env : DecoderEnvironment) :
    FunctionContract DecodeError CollectionArgs (Array BinaryFv.Specs.SSZ.RawWithdrawalRequest) where
  meaning := fun args => meaningWithdrawalRequests args.bytes
  pre := preCollection env
  post := fun args => postCollection env args 76 Array.size
  stepBound := fun args => 128 + 256 * (args.bytes.size / 76 + 1)

def contractConsolidationRequests (env : DecoderEnvironment) :
    FunctionContract DecodeError CollectionArgs (Array BinaryFv.Specs.SSZ.RawConsolidationRequest) where
  meaning := fun args => meaningConsolidationRequests args.bytes
  pre := preCollection env
  post := fun args => postCollection env args 116 Array.size
  stepBound := fun args => 128 + 256 * (args.bytes.size / 116 + 1)

def contractPublicKeys (env : DecoderEnvironment) :
    FunctionContract DecodeError CollectionArgs
      (Array (BinaryFv.Specs.SSZ.RawByteVector BinaryFv.Specs.SSZ.publicKeyBytes)) where
  meaning := fun args => meaningPublicKeys args.bytes
  pre := preCollection env
  post := fun args => postCollection env args BinaryFv.Specs.SSZ.publicKeyBytes Array.size
  stepBound := fun args => 128 + 128 * (args.bytes.size / BinaryFv.Specs.SSZ.publicKeyBytes + 1)

/-- `decodeByteListList` produces 16-byte slice descriptors, one per item. One contract, one
identity; the bounds ride in `ByteListListArgs`. -/
def contractByteListList (env : DecoderEnvironment) :
    FunctionContract DecodeError ByteListListArgs (Array BinaryFv.Specs.SSZ.RawBytes) where
  meaning := fun args => meaningByteListList args.maxItems args.maxItemBytes args.bytes
  pre := fun args => preCollection env args.toCollectionArgs
  post := fun args => postCollection env args.toCollectionArgs 16 Array.size
  stepBound := fun args => 256 + 256 * (args.bytes.size / 4 + 1)

/-!
## Correctness claims
-/

def correctnessClaimVersionedHashes (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractVersionedHashes env)

def correctnessClaimWithdrawals (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractWithdrawals env)

def correctnessClaimDepositRequests (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractDepositRequests env)

def correctnessClaimWithdrawalRequests (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractWithdrawalRequests env)

def correctnessClaimConsolidationRequests (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractConsolidationRequests env)

def correctnessClaimPublicKeys (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractPublicKeys env)

def correctnessClaimByteListList (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractByteListList env)

/-!
## Satisfiability
-/

def satisfiableVersionedHashes (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractVersionedHashes env)

def satisfiableWithdrawals (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractWithdrawals env)

def satisfiableDepositRequests (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractDepositRequests env)

def satisfiableWithdrawalRequests (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractWithdrawalRequests env)

def satisfiableConsolidationRequests (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractConsolidationRequests env)

def satisfiablePublicKeys (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractPublicKeys env)

def satisfiableByteListList (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractByteListList env)

/-!
## Loop invariant and characterizations
-/

/--
The `decodeByteListList` loop invariant, **as written in the source**.

`previous` tracks the previous item's *start*, not its end, so the guard `start < previous` enforces
nondecreasing starts and nothing more. Two items may therefore overlap. Stating the stronger
non-overlap property here would make the contract unprovable against the actual binary, and stating
nothing would let a wrong loop proof through.
-/
def byteListListLoopInvariant (bytes : ByteArray) (maxItemBytes : Nat)
    (starts ends : List Nat) : Prop :=
  Nondecreasing starts ∧
  starts.length = ends.length ∧
  ∀ pair ∈ starts.zip ends,
    pair.1 ≤ pair.2 ∧ pair.2 ≤ bytes.size ∧ pair.2 - pair.1 ≤ maxItemBytes

/-- A zero-length input decodes to the empty array rather than failing.

**Renamed from `emptyByteListListIsEmptyArray`, and the old name overclaimed.** A zero-length input
does still allocate — the source takes `alloc.alloc(_, 0)` rather than returning a static empty
slice, so "no allocation" would be the wrong postcondition even here — but *this statement says
nothing about that*. It is about the meaning, which has no allocation effect to observe. The
allocation claim is `postCollection`'s `AllocatedDescriptorArray`, and restating it here would create
a second source for a proof-relevant fact, which is what this project rejects everywhere else. -/
def emptyByteListListIsEmptyArray : Prop :=
  ∀ maxItems maxItemBytes,
    meaningByteListList maxItems maxItemBytes ByteArray.empty = .ok #[]

/-- No collection decoder can produce `unknownFork`: none of them reads a fork index. -/
def collectionsNeverUnknownFork : Prop :=
  ∀ (bytes : ByteArray),
    meaningVersionedHashes bytes ≠ .error .unknownFork ∧
    meaningWithdrawals bytes ≠ .error .unknownFork ∧
    meaningDepositRequests bytes ≠ .error .unknownFork ∧
    meaningWithdrawalRequests bytes ≠ .error .unknownFork ∧
    meaningConsolidationRequests bytes ≠ .error .unknownFork ∧
    meaningPublicKeys bytes ≠ .error .unknownFork

end BinaryFv.Zesu.Contracts
