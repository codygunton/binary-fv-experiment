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
  | some sail => .decoded (CanonicalDecodedResult.ofEvmSail input sail)

def reviewedDomainDivergence (input : Array UInt8) (decoded : ZesuDecodedResult) : Bool :=
  knownBugs.any fun bug => decide (KnownBugApplies input decoded bug)

theorem reviewedDomainDivergence_eq_true_iff (input : Array UInt8)
    (decoded : ZesuDecodedResult) :
    reviewedDomainDivergence input decoded = true ↔
      ∃ bug ∈ knownBugs, KnownBugApplies input decoded bug := by
  simp [reviewedDomainDivergence, List.any_eq_true]

/-- Compare the machine result with the independently computed EVM-Sail result. Successful chain-id
normalization is accepted only through `decodedResultRelModuloKnownBugs`; a Zesu-only success is
collapsed to rejection only when one of the six reviewed domain predicates holds. -/
def CanonicalOutcome.ofZesuKnownBugs (input : Array UInt8)
    (outcome : ZesuDecodeOutcome) : CanonicalOutcome :=
  match outcome with
  | .machineError => .machineError
  | .fuelExhausted => .fuelExhausted
  | .invalidObservation => .invalidObservation
  | .rejected =>
      match decode input with
      | none => .rejected
      | some _ => .unexpectedMismatch
  | .decoded zesu =>
      match decode input with
      | some sail =>
          if decodedResultRelModuloKnownBugs input zesu sail then
            .decoded (CanonicalDecodedResult.ofEvmSail input sail)
          else
            .unexpectedMismatch
      | none =>
          if reviewedDomainDivergence input zesu then .rejected else .unexpectedMismatch

def ZesuDecodeOutcome.AllowedModuloKnownBugs (input : Array UInt8) : ZesuDecodeOutcome → Prop
  | .rejected => ¬∃ decoded, SailDecode input decoded
  | .decoded zesu =>
      (∃ sail, SailDecode input sail ∧ decodedResultRelModuloKnownBugs input zesu sail) ∨
      ((¬∃ sail, SailDecode input sail) ∧
        ∃ bug ∈ knownBugs, KnownBugApplies input zesu bug)
  | .machineError | .fuelExhausted | .invalidObservation => False

theorem canonicalOutcome_eq_iff_allowed (input : Array UInt8) (outcome : ZesuDecodeOutcome) :
    CanonicalOutcome.ofZesuKnownBugs input outcome = CanonicalOutcome.ofEvmSail input ↔
      outcome.AllowedModuloKnownBugs input := by
  cases outcome with
  | rejected =>
      unfold ZesuDecodeOutcome.AllowedModuloKnownBugs
      rw [← decode_eq_none_iff]
      cases h : decode input <;> simp [CanonicalOutcome.ofZesuKnownBugs,
        CanonicalOutcome.ofEvmSail, h]
  | decoded zesu =>
      cases h : decode input with
      | none =>
          have noDecode : ∀ sail, ¬SailDecode input sail := by
            intro sail decoded
            have := (decode_eq_some_iff input sail).2 decoded
            simp_all
          simp [CanonicalOutcome.ofZesuKnownBugs, CanonicalOutcome.ofEvmSail,
            ZesuDecodeOutcome.AllowedModuloKnownBugs, h, noDecode,
            reviewedDomainDivergence_eq_true_iff]
      | some sail =>
          have decodeUnique : ∀ other, SailDecode input other ↔ other = sail := by
            intro other
            rw [← decode_eq_some_iff]
            simp [h, eq_comm]
          simp [CanonicalOutcome.ofZesuKnownBugs, CanonicalOutcome.ofEvmSail,
            ZesuDecodeOutcome.AllowedModuloKnownBugs, h, decodeUnique]
  | machineError =>
      cases h : decode input <;> simp [CanonicalOutcome.ofZesuKnownBugs,
        CanonicalOutcome.ofEvmSail, ZesuDecodeOutcome.AllowedModuloKnownBugs, h]
  | fuelExhausted =>
      cases h : decode input <;> simp [CanonicalOutcome.ofZesuKnownBugs,
        CanonicalOutcome.ofEvmSail, ZesuDecodeOutcome.AllowedModuloKnownBugs, h]
  | invalidObservation =>
      cases h : decode input <;> simp [CanonicalOutcome.ofZesuKnownBugs,
        CanonicalOutcome.ofEvmSail, ZesuDecodeOutcome.AllowedModuloKnownBugs, h]

end BinaryFv.Zesu
