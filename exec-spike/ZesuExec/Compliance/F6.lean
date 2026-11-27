import ZesuExec.Compliance.ParentHeaderAgree
import ZesuExec.Fn.F6.Sail

/-!
# F6 `rlp_decode.decodeParentHeader`: compliance with EVM-Sail's parent-header decoding

Transcribes zesislar's `ParentHeaderMeaningModuloKnownBugs` (`ZesuSsz/Contracts/ParentHeaderRung2.v`)
with `parentHeaderSailAgrees`, `ParentHeaderSuccess`/`ParentHeaderRejects`/
`ParentHeaderSharedFields` (`ZesuSsz/Compliance/ProjectionParentHeader.v`) and the triggers of
`ZesuSsz/Contracts/ParentHeaderBugTriggers.v`.

(a) The candidate is `ZesuExec.Fn.F6.walk` (`candidateParentHeader`); `f6_spec`'s `Post` states
the 80 result bytes through it.

(b) `sailRun input σ` is EVM-Sail's decoding of one parent header (`parentAction`:
`rlp_node_cursor`, then `decode_parent_header_fields cursor 0 EMPTY_PARENT_HEADER_FIELDS`, as in
`_rec_index_witness_header_cursor`), the stateless input holding `input`, from register state
`σ` whose `k_execution_profile` register holds `prof`. `f6_candidate_agrees`: Sail's result
relates to `walk input` (`SailRelates`: both reject, or both accept and Sail's base fee, blob gas
used and excess blob gas, each with its `have_` flag, are the candidate's values 3, 4, 5, below
`2^64`; Sail does not return gas limit, gas used or timestamp), or a listed known bug's trigger
holds (`trig`). The blob and excess-blob-gas triggers use `prof`'s blob maximum and limit.

(c) `f6_compliance` / `f6_compliance_sail`: as for F2, combined with `f6_spec` / `f6_sail`.
-/

namespace ZesuExec.Compliance.F6
open ZesuExec ZesuExec.Fn.F6 ZesuExec.Compliance

/-! ## EVM-Sail on an input -/

abbrev SailParentResult :=
  EStateM.Result (Sail.Error Unit) SailRegs (Evm.Defs.ParentHeaderFields × Evm.HostState)

/-- `sailParentHeaderRun`: `parentAction` with the stateless input holding `input`. -/
def sailRun (input : List Byte) (σ : SailRegs) : SailParentResult :=
  ((parentAction input).run (hostOf input)).run σ

/-- `parentHeaderSailAgrees`: Sail rejects (`fatal_error RlpDecode`) where the candidate rejects;
where the candidate returns `vals`, Sail returns fields whose base fee, blob gas used and excess
blob gas are `vals[3]?`, `vals[4]?`, `vals[5]?`, all values below `2^64`. Any other Sail failure
relates to nothing. -/
def SailRelates : SailParentResult → Option (List Nat) → Prop
  | .ok (f, _) _, some vals => sharedOf f = ⟨vals[3]?, vals[4]?, vals[5]?⟩ ∧ ∀ v ∈ vals, v < 2 ^ 64
  | .error .Exit _, none => True
  | _, _ => False

/-! ## Known bugs -/

/-- `parentHeaderBugTrigger`, with the profile's blob maximum `maxB` and excess-blob-gas limit
`limit`. The reached-field triggers are evaluated along the candidate's walk (`AtField`). -/
def trig (maxB limit : Nat) : KnownBug → List Byte → Prop
  | .rlpLongLengthWrap, input => AtField (fun _ rem => wrapAt rem) input
  | .parentHeaderMissingRequiredField, input => missing input
  | .parentHeaderTrailingBytes, input => trailingBytes input
  | .parentHeaderSkippedFieldShape, input => AtField shapeAt input
  | .parentHeaderBlobGasUnaligned, input => AtField (blobAt maxB) input
  | .rlpUintNonCanonical, input => AtField nonCanonAt input
  | .parentHeaderUintOver8, input => AtField over8At input
  | .parentHeaderUndecodedFieldRejected, input => AtField undecodedAt input
  | .parentHeaderExcessBlobGasAboveLimit, input => AtField (excessAt limit) input
  | .parentHeaderTrailingItemMalformed, input => trailingItems input
  | .accessListAddressLength, _ | .accessListKeyLength, _ | .accessListEntryTrailingBytes, _ =>
    False

/-! ## (b) The candidate agrees with Sail modulo known bugs -/

theorem atField_split (maxB limit : Nat) (input : List Byte)
    (h : AtField (stepTrig maxB limit) input) : ∃ bug ∈ knownBugs, trig maxB limit bug input := by
  obtain ⟨pl, hpl, e, he, ht⟩ := h
  rcases ht with t | t | t | t | t | t | t
  · exact ⟨.rlpLongLengthWrap, by simp [knownBugs], pl, hpl, e, he, t⟩
  · exact ⟨.parentHeaderSkippedFieldShape, by simp [knownBugs], pl, hpl, e, he, t⟩
  · exact ⟨.parentHeaderUndecodedFieldRejected, by simp [knownBugs], pl, hpl, e, he, t⟩
  · exact ⟨.rlpUintNonCanonical, by simp [knownBugs], pl, hpl, e, he, t⟩
  · exact ⟨.parentHeaderUintOver8, by simp [knownBugs], pl, hpl, e, he, t⟩
  · exact ⟨.parentHeaderBlobGasUnaligned, by simp [knownBugs], pl, hpl, e, he, t⟩
  · exact ⟨.parentHeaderExcessBlobGasAboveLimit, by simp [knownBugs], pl, hpl, e, he, t⟩

theorem f6_candidate_agrees (input : List Byte) (σ : SailRegs) (prof : Evm.Defs.ExecutionProfile)
    (hσ : σ.regs.get? .k_execution_profile = some prof) :
    SailRelates (sailRun input σ) (walk input) ∨
      ∃ bug ∈ knownBugs, trig (profMax prof) (profLimit prof) bug input := by
  have he := parent_eval input σ prof hσ
  rcases parent_agree (profMax prof) (profLimit prof) input with hr | ht | hm | htb | hti
  · left
    unfold sailRun
    revert he hr
    cases sailParent (profMax prof) (profLimit prof) input with
    | none =>
      cases walk input with
      | none => intro he _; simp only [RunRel] at he; rw [he]; trivial
      | some _ => intro _ hr; exact hr.elim
    | some s' =>
      cases walk input with
      | none => intro _ hr; exact hr.elim
      | some vals =>
        intro he hr
        obtain ⟨f', hf, hsf⟩ := he
        rw [hf]
        exact ⟨hsf.trans hr.1, hr.2⟩
  · exact .inr (atField_split _ _ _ ht)
  · exact .inr ⟨.parentHeaderMissingRequiredField, by simp [knownBugs], hm⟩
  · exact .inr ⟨.parentHeaderTrailingBytes, by simp [knownBugs], htb⟩
  · exact .inr ⟨.parentHeaderTrailingItemMalformed, by simp [knownBugs], hti⟩

/-! ## (c) Compliance of the binary -/

/-- `ParentHeaderMeaningModuloKnownBugs`'s Sail conjunct for the input bytes: for every Sail
register state holding an execution profile, agreement or a listed bug's trigger. (The domain
and candidate-result conjuncts are `Pre` and `Post`.) -/
def ParentHeaderMeaningModuloKnownBugs (input : List Byte) : Prop :=
  ∀ σ prof, σ.regs.get? .k_execution_profile = some prof →
    SailRelates (sailRun input σ) (walk input) ∨
      ∃ bug ∈ knownBugs, trig (profMax prof) (profLimit prof) bug input

/-- The final-state property of `f6_compliance`: `Post`, and the input satisfies the meaning. -/
def Compliant (m m' : Machine) : Prop :=
  Post m m' ∧
  ∀ input, BytesAt m (m.reg 11) input → input.length = (m.reg 12).toNat →
    ParentHeaderMeaningModuloKnownBugs input

theorem f6_compliance (m : Machine) (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    Reaches zesuImage 2178 (Compliant m) m :=
  (f6_spec m hpc hpre).mono (Nat.le_refl _) fun _ hp =>
    ⟨hp, fun input _ _ σ prof hσ => f6_candidate_agrees input σ prof hσ⟩

/-- `f6_compliance` on the Sail RISC-V model, by `sail_reaches`. -/
theorem f6_compliance_sail {m : Machine} {s : BinaryFv.RiscV.State}
    (h : SailLink.Rel zesuImage m s) (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailLink.SailReaches zesuImage 2178
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ Compliant m m') s :=
  SailLink.sail_reaches h (f6_compliance m hpc hpre)

/-! ## Witnesses -/

/-- `missingFieldWitness` (`c0`, an empty header list): the binary rejects, Sail accepts. -/
example : walk [0xc0] = none ∧ sailParent 0 0 [0xc0] = some ⟨none, none, none⟩ ∧
    missing [0xc0] := by
  refine ⟨by decide, ?_, [], by decide, by decide⟩
  have hn : sailNode [0xc0] = some (1, 0) := by decide
  simp only [sailParent, hn]
  exact fieldsSpec_nil _ _ _ _

/--
info: 'ZesuExec.Compliance.F6.f6_candidate_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f6_candidate_agrees

/--
info: 'ZesuExec.Compliance.F6.f6_compliance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f6_compliance

/--
info: 'ZesuExec.Compliance.F6.f6_compliance_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f6_compliance_sail

end ZesuExec.Compliance.F6
