import ZesuExec.Fn.TX.Spec

/-!
# DTF `rlp_decode.decodeTxFields` (`0x8000050c`, 2,825 instructions) — draft contract

**Draft, unreviewed** (no prior contract exists). Drafted from the pinned Zig source
(`src/stateless/rlp_decode.zig:308-418` and the field helpers `:420-588` at zesu `b5483dda`), the
binary (`OPEN/DTF/BLOCKERS.md`: calling convention, the jump table and its `tx_type ≤ 4`
precondition) and the debug object's layout of `input.Transaction`. The EVM-Sail transaction
decoder (`vendor/evm-sail-lean/Evm/Lib/Rlp/Codecs/Transactions.lean`, `decode_*_tx`) is the
compliance side, not part of `Post`. Open points are listed in `STATEMENTS.md`, section DTF.

`a0` = result `anyerror!input.Transaction` (0x128 bytes: the Transaction at `+0`, the u16 error
code at `+0x120`), `a1` = allocator object `{ctx, vtable}`, `a2` = `tx_type`, `a3`/`a4` = the
payload slice `{ptr, len}` (an RLP list payload). Frame 0x370 bytes; the deepest callee is
`txAccessList` (704 bytes).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec

def entry : Nat := 0x8000050c

/-! ## The reference decoder (`decodeTxFields` and its field helpers) over `F2.decode` -/

/-- A field parser: consumes a prefix of the payload (`rest`), or fails (`error.InvalidBlock`). -/
abbrev P := StateT (List Byte) Option

/-- One `rlp.decodeItem` on `rest`; `rest` advances by the consumed length. -/
def item : P (Bool × List Byte) := fun rest =>
  match F2.decode rest with
  | .success isList h p => some ((isList, TX.itemPayload rest h p), TX.itemRest rest h p)
  | .error => none

/-- Big-endian value of a byte string. -/
def be (b : List Byte) : Nat := F2.bigEndian b

/-- `txBytesView`. -/
def bytesView : P (List Byte) := do
  let (isList, b) ← item
  if isList then failure else pure b

/-- `txU64`. -/
def u64 : P Nat := do
  let b ← bytesView
  if b.length > 8 then failure else pure (be b)

/-- `txNonce`: more than 8 bytes clamps to `maxInt(u64)`. -/
def nonce : P Nat := do
  let b ← bytesView
  pure (if b.length > 8 then 2 ^ 64 - 1 else be b)

/-- `txU128`: more than 16 bytes clamps to `maxInt(u128)`. -/
def u128 : P Nat := do
  let b ← bytesView
  pure (if b.length > 16 then 2 ^ 128 - 1 else be b)

/-- `txU256`. -/
def u256 : P Nat := do
  let b ← bytesView
  if b.length > 32 then failure else pure (be b)

/-- `txAddr`: the empty string is `null` (contract creation), else exactly 20 bytes. -/
def addr : P (Option (List Byte)) := do
  let (isList, b) ← item
  if isList then failure
  else if b.length = 0 then pure none
  else if b.length = 20 then pure (some b)
  else failure

/-- `txAccessList`, as the reference decoder of TX (`TX.candidate`). -/
def accessList : P (List TX.EntryValue) := fun rest =>
  match TX.candidate rest with
  | .accepted es n => some (es, rest.drop n)
  | .rejected _ => none

/-- The payload of the next item, which must be a list. -/
def listPayload : P (List Byte) := do
  let (isList, p) ← item
  if isList then pure p else failure

/-- Items of a list payload, each by `f` on the remaining payload (fuel = the byte count). -/
def walkList {α : Type} (f : P α) : Nat → List Byte → Option (List α)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, p@(_ :: _) =>
    match f p with
    | some (a, p') => (walkList f fuel p').map (a :: ·)
    | none => none

/-- One versioned hash: a 32-byte string. -/
def hash : P (List Byte) := do
  let b ← bytesView
  if b.length = 32 then pure b else failure

/-- `txHashList`. -/
def hashList : P (List (List Byte)) := do
  let p ← listPayload
  match walkList hash p.length p with
  | some hs => pure hs
  | none => failure

/-- `input.AuthorizationTuple`. -/
structure Auth where
  chainId : Nat
  address : List Byte
  nonce : Nat
  v : Nat
  r : Nat
  s : Nat
  deriving DecidableEq, Repr

/-- One authorization tuple: a list `[chainId, address, nonce, v, r, s]`; bytes after `s` inside
the tuple are not read. -/
def auth : P Auth := do
  let ep ← listPayload
  let r : P Auth := do
    let c ← u256
    let a ← bytesView
    if a.length ≠ 20 then failure
    let n ← u64
    let v ← u64
    let rr ← u256
    let ss ← u256
    pure ⟨c, a, n, v, rr, ss⟩
  match r ep with
  | some (t, _) => pure t
  | none => failure

/-- `txAuthList`. -/
def authList : P (List Auth) := do
  let p ← listPayload
  match walkList auth p.length p with
  | some ts => pure ts
  | none => failure

/-- `input.Transaction`; `none` fields are Zig's `null`. -/
structure Tx where
  txType : Nat
  chainId : Option Nat
  nonce : Nat
  gasPrice : Nat
  gasPriorityFee : Option Nat
  gasLimit : Nat
  to : Option (List Byte)
  value : Nat
  data : List Byte
  accessList : List TX.EntryValue
  blobHashes : List (List Byte)
  maxFeePerBlobGas : Nat
  authorizationList : List Auth
  v : Nat
  r : Nat
  s : Nat

/-- The fields every typed transaction shares before its access list:
`[chainId, nonce, (maxPriorityFee,) gasPrice/maxFee, gasLimit, to, value, data]`. -/
def typedHead (priority : Bool) : P (Nat × Nat × Option Nat × Nat × Nat × Option (List Byte) × Nat × List Byte) := do
  let c ← u64
  let n ← nonce
  let pf ← if priority then (some <$> u128) else pure none
  let gp ← u128
  let gl ← u64
  let t ← addr
  let val ← u256
  let d ← bytesView
  pure (c, n, pf, gp, gl, t, val, d)

/-- Legacy `v`: EIP-155 `v = chainId·2 + 35 + yParity`, else `v = 27 + yParity`; the `@intCast`s
truncate to 64 bits (checked against the disassembly at `0x80002a88..0x80002b28`). -/
def legacyV (vRaw : Nat) : Option Nat × Nat :=
  if 35 ≤ vRaw then (some ((vRaw - 35) / 2 % 2 ^ 64), (vRaw - 35) % 2)
  else if 27 ≤ vRaw then (none, (vRaw - 27) % 2 ^ 64)
  else (none, 0)

/-- `decodeTxFields` for `tx_type ≤ 4`; the rest of the payload after the last field is not read. -/
def body (t : Nat) : P Tx :=
  match t with
  | 0 => do
    let n ← nonce
    let gp ← u128
    let gl ← u64
    let to ← addr
    let val ← u256
    let d ← bytesView
    let vRaw ← u256
    let r ← u256
    let s ← u256
    let (c, v) := legacyV vRaw
    pure ⟨0, c, n, gp, none, gl, to, val, d, [], [], 0, [], v, r, s⟩
  | 1 | 2 => do
    let (c, n, pf, gp, gl, to, val, d) ← typedHead (t == 2)
    let al ← accessList
    let v ← u64
    let r ← u256
    let s ← u256
    pure ⟨t, some c, n, gp, pf, gl, to, val, d, al, [], 0, [], v, r, s⟩
  | 3 => do
    let (c, n, pf, gp, gl, to, val, d) ← typedHead true
    let al ← accessList
    let bf ← u128
    let bh ← hashList
    let v ← u64
    let r ← u256
    let s ← u256
    pure ⟨3, some c, n, gp, pf, gl, to, val, d, al, bh, bf, [], v, r, s⟩
  | _ => do
    let (c, n, pf, gp, gl, to, val, d) ← typedHead true
    let al ← accessList
    let au ← authList
    let v ← u64
    let r ← u256
    let s ← u256
    pure ⟨t, some c, n, gp, pf, gl, to, val, d, al, [], 0, au, v, r, s⟩

def decode (t : Nat) (payload : List Byte) : Option Tx := (body t).run' payload

/-- The `rest` slice `txAccessList` is called on, when the fields before it decode. -/
def accessListInput (t : Nat) (payload : List Byte) : Option (List Byte) :=
  if t = 0 then none
  else ((typedHead (t == 2 || 3 ≤ t) *> get) : P (List Byte)).run' payload

/-- The number of top-level items `body t` reads. -/
def fieldCount : Nat → Nat
  | 0 => 9
  | 1 => 11
  | 2 => 12
  | 3 => 14
  | _ => 13

/-- `TX.HeaderFits` for the first `n` items of `b`, each reached while the items before it
decode (`decodeItem` successes, `rest` advancing by `TX.itemRest`); `inner` for the payload of every
list item among them. -/
def ItemsFit (inner : List Byte → Prop) : Nat → List Byte → Prop
  | 0, _ => True
  | n + 1, b => TX.HeaderFits b ∧
    match F2.decode b with
    | .success isList h p =>
      (isList = true → inner (TX.itemPayload b h p)) ∧ ItemsFit inner n (TX.itemRest b h p)
    | .error => True

/-- Header fit for every `decodeItem` call `body t` can reach: the first `fieldCount t` top-level
items, the items of a top-level list's payload (the access list's entries, the versioned hashes, the
authorization tuples) and the items of those items' list payloads (an authorization tuple's
fields). It over-approximates the calls reached: it does not stop at a field check that fails, and
descends into a list item at any position. -/
def Fits (t : Nat) (payload : List Byte) : Prop :=
  ItemsFit (fun p => ItemsFit (fun q => ItemsFit (fun _ => True) q.length q) p.length p)
    (fieldCount t) payload

/-- Domain: the access list, when reached, is in `txAccessList`'s domain (`TX.Domain`), and every
item header the decoder reaches fits in 64 bits (`Fits`, as TX's `HeaderFits` on its calls):
`decodeItem` accepts a header whose `h + p` wraps `2^64`, and the `data` field would then ask the
allocator for `p ≥ 2^63` bytes (`STATEMENTS.md` § DTF point 6). -/
def Domain (t : Nat) (payload : List Byte) : Prop :=
  (∀ r, accessListInput t payload = some r → TX.Domain r) ∧ Fits t payload

/-! ## Machine contract -/

def stackBytes : Nat := 0x370 + TX.stackBytes
def resultBytes : Nat := 0x128
def errOff : Nat := 0x120

/-- Little-endian bytes of `v` (`n` bytes). -/
def leBytes (n v : Nat) : List Byte := (List.range n).map fun j => BitVec.ofNat 8 (v / 256 ^ j)

/-- A Zig slice `{ptr, len}` at `a` whose `len` items of `size` bytes are `bytes` (the pointer is
unconstrained when `len = 0`). -/
def SliceAt (m : Machine) (a : Word) (len : Nat) (bytes : List Byte) : Prop :=
  ∃ p : Word, m.load a 8 = some p ∧ m.load (a + 8) 8 = some (BitVec.ofNat 64 len) ∧
    (bytes ≠ [] → RamRange p bytes.length ∧ BytesAt m p bytes)

/-- One `input.AuthorizationTuple` (0x90 bytes) at `a`: `chainId` `+0`, `r` `+0x20`, `s` `+0x40`,
`nonce` `+0x60`, `v` `+0x68`, `address` `+0x70`. -/
def AuthAt (m : Machine) (a : Word) (t : Auth) : Prop :=
  BytesAt m a (leBytes 32 t.chainId) ∧ BytesAt m (a + 0x20) (leBytes 32 t.r) ∧
  BytesAt m (a + 0x40) (leBytes 32 t.s) ∧ BytesAt m (a + 0x60) (leBytes 8 t.nonce) ∧
  BytesAt m (a + 0x68) (leBytes 8 t.v) ∧ BytesAt m (a + 0x70) t.address

/-- The decoded transaction at `res`, in the layout of `input.Transaction` (debug object):
`gas_price` `+0`, `gas_priority_fee` `+0x10` (tag `+0x20`), `value` `+0x30`,
`max_fee_per_blob_gas` `+0x50`, `r` `+0x60`, `s` `+0x80`, `chain_id` `+0xa0` (tag `+0xa8`),
`nonce` `+0xb0`, `gas_limit` `+0xb8`, the slices `data` `+0xc0`, `access_list` `+0xd0`,
`blob_hashes` `+0xe0`, `authorization_list` `+0xf0`, `v` `+0x100`, `tx_type` `+0x108`, `to`
`+0x109` (tag `+0x11d`). -/
def TxAt (m : Machine) (res : Word) (tx : Tx) : Prop :=
  BytesAt m res (leBytes 16 tx.gasPrice) ∧
  (match tx.gasPriorityFee with
   | some f => BytesAt m (res + 0x10) (leBytes 16 f) ∧ m.mem (res + 0x20) = some 1
   | none => m.mem (res + 0x20) = some 0) ∧
  BytesAt m (res + 0x30) (leBytes 32 tx.value) ∧
  BytesAt m (res + 0x50) (leBytes 16 tx.maxFeePerBlobGas) ∧
  BytesAt m (res + 0x60) (leBytes 32 tx.r) ∧ BytesAt m (res + 0x80) (leBytes 32 tx.s) ∧
  (match tx.chainId with
   | some c => BytesAt m (res + 0xa0) (leBytes 8 c) ∧ m.mem (res + 0xa8) = some 1
   | none => m.mem (res + 0xa8) = some 0) ∧
  BytesAt m (res + 0xb0) (leBytes 8 tx.nonce) ∧ BytesAt m (res + 0xb8) (leBytes 8 tx.gasLimit) ∧
  SliceAt m (res + 0xc0) tx.data.length tx.data ∧
  (∃ is : List TX.EntryImage, is.length = tx.accessList.length ∧
    SliceAt m (res + 0xd0) tx.accessList.length (TX.entriesBytes tx.accessList is) ∧
    ∀ x ∈ List.zip tx.accessList is, x.2.padding.length = 4 ∧
      (x.1.keys ≠ [] → RamRange x.2.keysPtr (TX.keySize * x.1.keys.length) ∧
        BytesAt m x.2.keysPtr x.1.keys.flatten)) ∧
  SliceAt m (res + 0xe0) tx.blobHashes.length tx.blobHashes.flatten ∧
  (∃ p : Word, m.load (res + 0xf0) 8 = some p ∧
    m.load (res + 0xf8) 8 = some (BitVec.ofNat 64 tx.authorizationList.length) ∧
    (tx.authorizationList ≠ [] → RamRange p (0x90 * tx.authorizationList.length)) ∧
    ∀ k (h : k < tx.authorizationList.length),
      AuthAt m (p + BitVec.ofNat 64 (0x90 * k)) tx.authorizationList[k]) ∧
  BytesAt m (res + 0x100) (leBytes 8 tx.v) ∧ m.mem (res + 0x108) = some (BitVec.ofNat 8 tx.txType) ∧
  (match tx.to with
   | some a => BytesAt m (res + 0x109) a ∧ m.mem (res + 0x11d) = some 1
   | none => m.mem (res + 0x11d) = some 0)

/-- The parameters of one call: the payload bytes and the allocator's live blocks. -/
structure Params where
  payload : List Byte
  L : List (Word × Nat)

section
variable (A : AllocContract zesuImage) (g : Params)

/-- Entry (draft): result 0x128 bytes in RAM, the allocator object `{ctx, alt_fl_alloc.vtable}`,
`tx_type ≤ 4` (the binary has no range check before its jump table), the payload in the input
buffer or RAM and in the domain, the scratch word, the allocator state, separation. -/
def Pre (m : Machine) : Prop :=
  let res := m.reg 10; let ao := m.reg 11; let t := (m.reg 12).toNat
  let inp := m.reg 13; let len := (m.reg 14).toNat; let sp := m.reg 2
  let fr := sp - BitVec.ofNat 64 stackBytes
  RodataLoaded zesuImage m ∧ StackOk m stackBytes ∧ RetAligned m ∧
  RamRange res resultBytes ∧ Present m res resultBytes ∧
  RamRange ao 16 ∧ ao.toNat % 8 = 0 ∧ (m.load ao 8).isSome ∧
  m.load (ao + 8) 8 = some (BitVec.ofNat 64 TX.vtable) ∧
  t ≤ 4 ∧
  TX.InputArea inp len ∧ BytesAt m inp g.payload ∧ g.payload.length = len ∧ Domain t g.payload ∧
  Present m TX.scratch 8 ∧ A.Heap g.L m ∧
  TX.Apart res resultBytes ao 16 ∧ TX.Apart inp len res resultBytes ∧ TX.Apart inp len ao 16 ∧
  TX.Apart fr stackBytes res resultBytes ∧ TX.Apart fr stackBytes ao 16 ∧
  TX.Apart fr stackBytes inp len ∧
  TX.Apart TX.scratch 8 res resultBytes ∧ TX.Apart TX.scratch 8 ao 16 ∧
  TX.Apart TX.scratch 8 inp len ∧ TX.Apart TX.scratch 8 fr stackBytes ∧
  (∀ a, InRange res resultBytes a ∨ InRange ao 16 a ∨ InRange inp len a ∨
    InRange fr stackBytes a ∨ InRange TX.scratch 8 a → ¬ A.Priv g.L a)

/-- Exit (draft): on success the error code is 0 and the result holds the reference decoder's
transaction; otherwise the error code is 3 (`error.InvalidBlock`, which the source also returns for
every allocation failure). The heap gains blocks (returned slices, or leaked ones on error). -/
def Post (m m' : Machine) : Prop :=
  let res := m.reg 10; let sp := m.reg 2
  Returns m m' ∧
  SameOutside (fun a => InRange res resultBytes a ∨
    InRange (sp - BitVec.ofNat 64 stackBytes) stackBytes a ∨ InRange TX.scratch 8 a ∨
    A.Priv g.L a) m m' ∧
  Present m' TX.scratch 8 ∧
  (∃ fresh : List (Word × Nat), (∀ b ∈ fresh, 0 < b.2 ∧ RamRange b.1 b.2) ∧
    ∃ L', L'.Perm (g.L ++ fresh) ∧ A.Heap L' m') ∧
  ((∃ tx, decode (m.reg 12).toNat g.payload = some tx ∧
      m'.load (res + BitVec.ofNat 64 errOff) 2 = some 0 ∧ TxAt m' res tx) ∨
   m'.load (res + BitVec.ofNat 64 errOff) 2 = some 3)

end

/-! ## The decoder on small inputs -/

/-- Legacy, all fields empty strings (nine `80`): every number 0, `to = null`, `v_raw = 0`. -/
example : (decode 0 (List.replicate 9 0x80)).map (fun tx => (tx.nonce, tx.to, tx.v, tx.chainId)) =
    some (0, none, 0, none) := by decide

/-- EIP-155 legacy `v_raw = 37` (`0x25`): chain id 1, parity 0. -/
example : (decode 0 (List.replicate 6 0x80 ++ [0x25, 0x80, 0x80])).map (·.chainId) =
    some (some 1) := by decide

/-- A list where the nonce should be fails. -/
example : decode 0 (0xc0 :: List.replicate 8 0x80) = none := by decide

/-- EIP-1559 with an empty access list. -/
example : (decode 2 (List.replicate 8 0x80 ++ [0xc0] ++ List.replicate 3 0x80)).map
    (fun tx => (tx.chainId, tx.gasPriorityFee, tx.accessList.length)) =
    some (some 0, some 0, 0) := by decide

end ZesuExec.Fn.DTF
