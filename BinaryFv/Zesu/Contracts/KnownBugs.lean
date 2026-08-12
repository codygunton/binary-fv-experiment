import BinaryFv.Specs.SSZ.Decode

/-!
# Reviewed Zesu compatibility exceptions

These constructors name demonstrated differences between the pinned Zesu implementation and the
pinned EVM-Sail SSZ decoder. They are Zesu-specific policy, not part of the reusable SSZ
specification.
-/

namespace BinaryFv.Zesu

/-- Reviewed divergence classes between the pinned Zesu and EVM-Sail revisions. -/
inductive KnownBug where
  | chainIdZeroNormalization
  | legacyRequestTableArity
  | legacyPayloadSize
  | futureForkActivation
  | extraDataLength
  | publicKeyCount
  | versionedHashCount
  deriving DecidableEq, Repr

/-- The fixed exception set. Callers of `root_compliance` cannot add exceptions. -/
def knownBugs : List KnownBug :=
  [.chainIdZeroNormalization, .legacyRequestTableArity, .legacyPayloadSize,
    .futureForkActivation, .extraDataLength, .publicKeyCount, .versionedHashCount]

theorem mem_knownBugs (bug : KnownBug) : bug ∈ knownBugs := by
  cases bug <;> decide

end BinaryFv.Zesu
