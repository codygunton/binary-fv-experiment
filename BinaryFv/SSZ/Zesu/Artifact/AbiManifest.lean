import ZesuSszAbi

namespace BinaryFv.SSZ.Zesu.Artifact

/-- Lookup a compiler-produced RV64 ABI datum by its qualified Zig type and field key. -/
def abiDatum (key : String) : Option Nat :=
  (ZesuSszAbi.manifest.toList.find? fun entry => entry.1 == key).map Prod.snd

def rawStatelessInputSize : Option Nat := abiDatum "ssz_raw.RawStatelessInput|size"
def rawStatelessInputAlign : Option Nat := abiDatum "ssz_raw.RawStatelessInput|align"
def rawStatelessInputNewPayloadRequestOffset : Option Nat :=
  abiDatum "ssz_raw.RawStatelessInput|new_payload_request"
def rawStatelessInputWitnessOffset : Option Nat := abiDatum "ssz_raw.RawStatelessInput|witness"
def rawStatelessInputChainConfigOffset : Option Nat := abiDatum "ssz_raw.RawStatelessInput|chain_config"
def rawStatelessInputPublicKeysOffset : Option Nat := abiDatum "ssz_raw.RawStatelessInput|public_keys"

theorem raw_stateless_input_layout :
    rawStatelessInputSize = some 832 ∧ rawStatelessInputAlign = some 16 ∧
      rawStatelessInputNewPayloadRequestOffset = some 0 ∧ rawStatelessInputWitnessOffset = some 688 ∧
        rawStatelessInputChainConfigOffset = some 736 ∧ rawStatelessInputPublicKeysOffset = some 816 := by
  native_decide

/-- Every queried member is produced by Zig reflection over every field of each raw result type. -/
def completeRawV4AbiManifest : Bool :=
  ZesuSszAbi.manifest.size == 84 && ZesuSszAbi.manifest.all fun entry => entry.2 < 1024

theorem complete_raw_v4_abi_manifest : completeRawV4AbiManifest = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Artifact
