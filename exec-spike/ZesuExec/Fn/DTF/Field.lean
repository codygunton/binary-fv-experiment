import ZesuExec.Fn.DTF.Regions

/-!
# DTF item values held at cuts and call sites (programme plan S7, open assertion items 1 and 4)

The data of a `cutFieldsTable`/`siteFieldsTable` row (`Rows.lean`); their meaning (`FieldVal.At`,
`FieldsOk`) is in `Cuts.lean`.
-/

namespace ZesuExec.Fn.DTF

/-- A value derived from a top-level item `k`, held in a register or frame word: its payload
pointer as `decodeItem` reports it, its payload length, limb `i` of its number of at most `n` bytes
(`numVal`: `u64`/`nonce` `n = 8`, `u128` `n = 16`, `u256` `n = 32`), whether it is nonempty
(`txAddr`'s tag), bytes `o .. o+n-1` of its payload (the address copy), or a byte loop's
accumulator over it (`acc`: limb `i` of the payload bytes before the cursor register `cur`, the end
register `fin` at the payload's end, at most `n` bytes). -/
inductive FieldVal
  | ptr (k : Nat)
  | len (k : Nat)
  | num (k n i : Nat)
  | nz (k : Nat)
  | raw (k o n : Nat)
  | acc (k n i cur fin : Nat)
  deriving DecidableEq, Repr

def FieldVal.k : FieldVal → Nat
  | .ptr k | .len k | .num k _ _ | .nz k | .raw k _ _ | .acc k _ _ _ _ => k

/-- The value does not mention the machine (all but a byte loop's accumulator, whose cursor and
end registers it states). -/
def FieldVal.free : FieldVal → Bool
  | .acc .. => false
  | _ => true

/-- An item value `v` held at `loc` when the transaction type is one of `arms` (any when empty):
the same location holds a different item on each arm reaching a cut (`nonce` is item 0 of the
legacy arm and item 1 of the typed ones). -/
structure Field where
  loc : Loc
  arms : List Nat
  v : FieldVal
  deriving DecidableEq, Repr

end ZesuExec.Fn.DTF
