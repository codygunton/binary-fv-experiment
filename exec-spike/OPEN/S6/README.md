# S6 open items

- F3 (`nextUint64`): `ZesuExec/Fn/F3/Proof.lean` has no `f3_spec` (checked 2026-11-27), so no
  `Compliance/F3.lean`. Rocq has no stand-alone `nextUint64` meaning; its classes are
  `RlpUintNonCanonical` and `ParentHeaderUintOver8` inside `ParentHeaderMeaningModuloKnownBugs`
  (`ParentHeaderRung2.v:32`). The Sail side is `rlp_decode_uint64` (`Evm/Lib/Rlp/Decoding.lean:625`)
  after `rlp_decode_item`; `ZesuExec/Compliance/RlpItem.lean` already evaluates the latter.
- F6: not attempted.
- `ZesuExec/Axioms.lean` has no guards for `f2_candidate_agrees`, `f2_compliance`,
  `f2_compliance_sail`; they are in `ZesuExec/Compliance/F2.lean`.
