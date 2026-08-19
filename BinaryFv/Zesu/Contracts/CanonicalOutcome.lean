import BinaryFv.Zesu.Contracts.DecodedResultRelation

/-! Computable common outcomes for the Zesu and EVM-Sail decoders. -/

namespace BinaryFv.Zesu

open BinaryFv.Specs.SSZ

/-- Observable result of the concrete Zesu endpoint runner. -/
inductive ZesuDecodeOutcome where
  | rejected
  | decoded (value : ZesuDecodedResult)
  | machineError
  | fuelExhausted
  | invalidObservation
  deriving BEq, Repr

/-- Common result used by the public equality theorem. The last four constructors can arise only
from the machine side or from a disagreement that is not one of the seven reviewed divergences. -/
inductive CanonicalOutcome where
  | rejected
  | decoded (value : CanonicalDecodedResult)
  | machineError
  | fuelExhausted
  | invalidObservation
  | unexpectedMismatch
  deriving BEq, DecidableEq, Repr

def CanonicalOutcome.ofEvmSail (input : Array UInt8) : CanonicalOutcome :=
  match decode input with
  | none => .rejected
  | some sail => .decoded (CanonicalDecodedResult.ofEvmSail input sail).normalizeKnownBugs

def reviewedDomainDivergence (input : Array UInt8) (decoded : ZesuDecodedResult) : Bool :=
  knownBugs.any fun bug => decide (KnownBugApplies input decoded bug)

theorem reviewedDomainDivergence_eq_true_iff (input : Array UInt8)
    (decoded : ZesuDecodedResult) :
    reviewedDomainDivergence input decoded = true ↔
      ∃ bug ∈ knownBugs, KnownBugApplies input decoded bug := by
  simp [reviewedDomainDivergence, List.any_eq_true]

/-- Normalize only the concrete Zesu result. This function never invokes EVM-Sail: it canonicalizes
the reviewed chain-id divergence and collapses exactly the six reviewed Zesu-only domains. -/
def CanonicalOutcome.ofZesuKnownBugs (input : Array UInt8)
    (outcome : ZesuDecodeOutcome) : CanonicalOutcome :=
  match outcome with
  | .machineError => .machineError
  | .fuelExhausted => .fuelExhausted
  | .invalidObservation => .invalidObservation
  | .rejected => .rejected
  | .decoded zesu =>
      if reviewedDomainDivergence input zesu then .rejected
      else .decoded (CanonicalDecodedResult.ofZesu zesu).normalizeKnownBugs

def ZesuDecodeOutcome.AllowedModuloKnownBugs (input : Array UInt8) : ZesuDecodeOutcome → Prop
  | .rejected => ¬∃ decoded, SailDecode input decoded
  | .decoded zesu =>
      (∃ sail, SailDecode input sail ∧ decodedResultRelModuloKnownBugs input zesu sail ∧
        AvoidsReviewedDomainDivergences input zesu) ∨
      ((¬∃ sail, SailDecode input sail) ∧
        ∃ bug ∈ knownBugs, KnownBugApplies input zesu bug)
  | .machineError | .fuelExhausted | .invalidObservation => False

theorem canonicalOutcome_eq_of_allowed (input : Array UInt8) (outcome : ZesuDecodeOutcome)
    (allowed : outcome.AllowedModuloKnownBugs input) :
    CanonicalOutcome.ofZesuKnownBugs input outcome = CanonicalOutcome.ofEvmSail input := by
  cases outcome with
  | rejected =>
      unfold ZesuDecodeOutcome.AllowedModuloKnownBugs at allowed
      rw [← decode_eq_none_iff] at allowed
      simp [CanonicalOutcome.ofZesuKnownBugs, CanonicalOutcome.ofEvmSail, allowed]
  | decoded zesu =>
      cases h : decode input with
      | none =>
          rcases allowed with accepted | ⟨_rejected, bug, listed, applies⟩
          · rcases accepted with ⟨sail, decoded, _related⟩
            have decodedEq := (decode_eq_some_iff input sail).2 decoded
            simp_all
          · have divergence : reviewedDomainDivergence input zesu = true :=
              (reviewedDomainDivergence_eq_true_iff input zesu).2 ⟨bug, listed, applies⟩
            simp [CanonicalOutcome.ofZesuKnownBugs, CanonicalOutcome.ofEvmSail, h, divergence]
      | some sail =>
          rcases allowed with ⟨other, decoded, related, avoids⟩ | rejected
          · have otherEq : other = sail := by
              have decodedEq := (decode_eq_some_iff input other).2 decoded
              simpa [h] using decodedEq.symm
            subst other
            have noDivergence : reviewedDomainDivergence input zesu = false := by
              rw [Bool.eq_false_iff]
              intro divergence
              obtain ⟨bug, listed, applies⟩ :=
                (reviewedDomainDivergence_eq_true_iff input zesu).1 divergence
              exact avoids bug listed applies
            simp [CanonicalOutcome.ofZesuKnownBugs, CanonicalOutcome.ofEvmSail, h,
              noDivergence, normalized_eq_of_decodedResultRelModuloKnownBugs _ _ _ related]
          · exact False.elim (rejected.1 ⟨sail, (decode_eq_some_iff input sail).1 h⟩)
  | machineError => exact False.elim allowed
  | fuelExhausted => exact False.elim allowed
  | invalidObservation => exact False.elim allowed

end BinaryFv.Zesu
