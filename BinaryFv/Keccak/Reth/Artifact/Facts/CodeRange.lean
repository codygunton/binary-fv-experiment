import BinaryFv.Keccak.Reth.Artifact.Image
import BinaryFv.RiscV.Platform.FetchMmio

namespace BinaryFv.Keccak

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The parser-derived load-image start, or zero when parsing the fixed artifact fails. -/
def artifactCodeRangeStart : Nat :=
  match Artifact.codeRange with
  | .ok code => code.start
  | .error _ => 0

/-- The parser-derived load-image stop, or zero when parsing the fixed artifact fails. -/
def artifactCodeRangeStop : Nat :=
  match Artifact.codeRange with
  | .ok code => code.stop
  | .error _ => 0

/-- A four-byte fetch lies in the parser-derived half-open load image. -/
def ArtifactCodeFetchPc (pc : BitVec 64) : Prop :=
  artifactCodeRangeStart ≤ pc.toNat ∧ pc.toNat + 4 ≤ artifactCodeRangeStop

private def artifactCodeRangeEndsBefore (limit : Nat) : Bool :=
  decide (artifactCodeRangeStop ≤ limit)

/-- Closed artifact/layout fact; no target address is written into this theorem. -/
private theorem artifact_code_range_before_clint :
    artifactCodeRangeEndsBefore (BitVec.toNat plat_clint_base) = true := by
  native_decide

/-- Closed artifact/layout fact; no target address is written into this theorem. -/
private theorem artifact_code_range_before_sig :
    artifactCodeRangeEndsBefore (BitVec.toNat plat_sig_base) = true := by
  native_decide

/-- Every parser-owned four-byte code fetch avoids the fixed CLINT and signature layouts. -/
theorem artifact_code_fetch_mmio_address_excluded (pc : BitVec 64)
    (inCode : ArtifactCodeFetchPc pc) : FetchMMIOAddressExcluded pc := by
  have codeBeforeClint : artifactCodeRangeStop ≤ BitVec.toNat plat_clint_base :=
    of_decide_eq_true artifact_code_range_before_clint
  have codeBeforeSig : artifactCodeRangeStop ≤ BitVec.toNat plat_sig_base :=
    of_decide_eq_true artifact_code_range_before_sig
  unfold ArtifactCodeFetchPc at inCode
  exact fetch_mmio_address_excluded_of_before_layout pc
    (Nat.le_trans inCode.2 codeBeforeClint) (Nat.le_trans inCode.2 codeBeforeSig)

end BinaryFv.Keccak
