import BinaryFv.Zesu.ProofProgress.MachineProofManifest
import BinaryFv.Zesu.MachineExecution.Level4DecodeRawPrologueSteps
import BinaryFv.Zesu.MachineExecution.Level4DecodeRawEpilogueSteps

namespace BinaryFv.Zesu.ProofProgress

open BinaryFv.RiscV
open BinaryFv.Zesu.MachineExecution
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

def level4DecodeRawPrologueManifest : MachineProofManifest where
  id := "level4.decodeRaw.prologue"
  owner := "ssz_raw.decodeRaw"
  sourceIdentity := "ssz_raw.decodeRaw:entry"
  theoremName := "BinaryFv.Zesu.MachineExecution.level4_decode_raw_entry_prologue"
  theoremFile := "BinaryFv/Zesu/MachineExecution/Level4DecodeRawPrologueSteps.lean"
  instructionSchema := "save-frame-prologue"
  frameSchema := "saved-ra-s0-s11+post-stack+input"
  prerequisiteContracts := []
  pcs := level4DecodeRawEntryProloguePcs
  region := Level4DecodeRawEntryProloguePcs
  exactRegion := fun _ => Iff.rfl
  compositionClaim :=
    ∀ {margs : DecoderMachineArgs} {state : State}
      (pre : Level4DecodeRawEntryProloguePre margs state) (fromStep : Nat),
      ∃ after s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
        Level4DecodeRawEntryEnvelopeOffsetsHandoff fromStep state after pre s0 s1 s2 s3 s4 s5 s6 s7
          s8 s9 s10 s11
  composition := level4_decode_raw_entry_prologue
  connection := .local

def level4DecodeRawEpilogueManifest : MachineProofManifest where
  id := "level4.decodeRaw.epilogue"
  owner := "ssz_raw.decodeRaw"
  sourceIdentity := "ssz_raw.decodeRaw:return"
  theoremName := "BinaryFv.Zesu.MachineExecution.level4_decode_raw_epilogue"
  theoremFile := "BinaryFv/Zesu/MachineExecution/Level4DecodeRawEpilogueSteps.lean"
  instructionSchema := "restore-frame-epilogue"
  frameSchema := "restore-ra-s0-s11+stack+return"
  prerequisiteContracts := []
  pcs := level4DecodeRawEpiloguePcs
  region := Level4DecodeRawEpiloguePcs
  exactRegion := fun _ => Iff.rfl
  compositionClaim :=
    ∀ {margs : DecoderMachineArgs} {base state : State}
      (pre : Level4DecodeRawEpiloguePre margs base state) (fromStep : Nat),
      ∃ after, Level4DecodeRawEpilogueResult fromStep state after pre
  composition := level4_decode_raw_epilogue
  connection := .local

def level4MachineProofManifests : List MachineProofManifest :=
  [level4DecodeRawPrologueManifest, level4DecodeRawEpilogueManifest]

theorem level4MachineProofManifestIds_unique :
    (level4MachineProofManifests.map (·.id)).Nodup := by decide

theorem level4MachineProofManifestPcs_disjoint :
    ∀ pc, pc ∈ level4DecodeRawPrologueManifest.pcs →
      pc ∉ level4DecodeRawEpilogueManifest.pcs := by native_decide

end BinaryFv.Zesu.ProofProgress
