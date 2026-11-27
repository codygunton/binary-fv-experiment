/-!
# Known divergence classes between the stock Zesu binary and EVM-Sail

Transcribes zesislar's `ZesuSsz/Compliance/KnownBugs.v` (`KnownBug`, `knownBugs`). Each class
names inputs on which the binary's result differs from EVM-Sail's. A compliance statement
(`ZesuExec/Compliance/<Id>.lean`) says which classes may excuse a result of its function; the
fixed list keeps later proofs from adding exceptions.
-/

namespace ZesuExec.Compliance

inductive KnownBug
  /-- `rlp.decodeItem` adds the long-form header and payload lengths modulo `2^64`
  (`rlp.zig:52`, `:67`); EVM-Sail adds them as integers and rejects an item longer than its
  source. -/
  | rlpLongLengthWrap
  /-- `decodeParentHeader` rejects fewer than twelve fields; EVM-Sail accepts any count. -/
  | parentHeaderMissingRequiredField
  /-- `decodeParentHeader` never reads bytes after the outer item; EVM-Sail rejects them. -/
  | parentHeaderTrailingBytes
  /-- `decodeParentHeader` skips fields 0..8, 12..14, 16 whatever their shape; EVM-Sail decodes
  fields 0 and 3 as words. -/
  | parentHeaderSkippedFieldShape
  /-- `decodeParentHeader` returns blob gas used as read; EVM-Sail checks its alignment and
  blob count. -/
  | parentHeaderBlobGasUnaligned
  /-- `nextUint64` folds any payload of at most 8 bytes; EVM-Sail rejects a non-canonical
  integer (leading zero byte, or a header that is not the short canonical form). -/
  | rlpUintNonCanonical
  /-- `nextUint64` rejects a payload longer than 8 bytes; EVM-Sail decodes base fee as a
  256-bit integer. -/
  | parentHeaderUintOver8
  /-- `decodeParentHeader` rejects fields 9..11 that are lists or longer than 8 bytes; EVM-Sail
  does not decode them as integers. -/
  | parentHeaderUndecodedFieldRejected
  /-- `decodeParentHeader` returns excess blob gas as read; EVM-Sail bounds it. -/
  | parentHeaderExcessBlobGasAboveLimit
  /-- `decodeParentHeader` never reads the outer payload after field 18; EVM-Sail decodes
  every further item. -/
  | parentHeaderTrailingItemMalformed
  /-- `rlp_decode.txAccessList` requires a 20-byte address; EVM-Sail accepts up to 32 bytes. -/
  | accessListAddressLength
  /-- `rlp_decode.txAccessList` requires a 32-byte storage key; EVM-Sail accepts fewer. -/
  | accessListKeyLength
  /-- `rlp_decode.txAccessList` never reads bytes after an entry's keys; EVM-Sail rejects
  them. -/
  | accessListEntryTrailingBytes
  deriving DecidableEq, Repr

/-- `knownBugs`: every reviewed class, in the Rocq order. -/
def knownBugs : List KnownBug :=
  [.rlpLongLengthWrap, .parentHeaderMissingRequiredField, .parentHeaderTrailingBytes,
   .parentHeaderSkippedFieldShape, .parentHeaderBlobGasUnaligned, .rlpUintNonCanonical,
   .parentHeaderUintOver8, .parentHeaderUndecodedFieldRejected,
   .parentHeaderExcessBlobGasAboveLimit, .parentHeaderTrailingItemMalformed,
   .accessListAddressLength, .accessListKeyLength, .accessListEntryTrailingBytes]

end ZesuExec.Compliance
