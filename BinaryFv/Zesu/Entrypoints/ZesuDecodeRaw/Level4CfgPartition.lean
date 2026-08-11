import BinaryFv.Binary.Elfling.Program
import GeneratedProgram

/-!
# Level 4 `decodeRaw` CFG partition

`ssz_raw.decodeRaw` has 172 instructions attributed directly to its generated function instance.
They exclude all nine inlined child instances.  In particular, the two reached `*.deinit` regions
are excluded-function regions absorbed by `decodeRaw`; their 74 instructions are not among these
172 cataloged function-instance PCs.

The three phases below classify only direct parent instructions.  Their typed interfaces state the
parent PCs.  The Level 4 hierarchy artifact owns the separate 18-boundary contract inventory,
including the distinction between function instances and excluded regions.  This module deliberately
does not assign argument bindings, result locations, write sets, register frames, exits, or bounds
to any child boundary.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary BinaryFv.Binary.Elfling
open BinaryFv.Zesu.Elflings.Generated

/-- The three disjoint semantic work streams for direct `decodeRaw` instructions. -/
inductive DecodeRawCfgPhase where
  | entryEnvelopeOffsets
  | specializedDispatchReturnsSuccess
  | rejectionCleanupStatusCopyEpilogue
deriving DecidableEq, Repr

/-- Every direct inlined child of the emitted `ssz_raw.decodeRaw` instance, in generated child
order. -/
def decodeRawInlinedChildren : List FunctionInstance :=
  [ functionInstance_ssz_raw_requireU32Length_in_ssz_raw_decodeRaw_at_191_25
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_202_23
  , functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61
  , functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48
  , functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48
  , functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46
  ]

theorem decodeRawInlinedChildren_match_generated :
    decodeRawInlinedChildren.map (·.id) = functionInstance_ssz_raw_decodeRaw.children.toList := rfl

/-- Instruction-start PCs in generated address ranges. -/
def instructionPcs (ranges : Array AddressRange) : List Nat :=
  ranges.toList.flatMap fun range =>
    (List.range (range.size / 4)).map fun index => range.start + 4 * index

/-- The PCs attributed to the direct inlined children, never to the parent phase proof. -/
def decodeRawInlinedChildPcs : List Nat :=
  decodeRawInlinedChildren.flatMap fun child => instructionPcs child.regions

/-- The 172 cataloged PCs directly attributed to `ssz_raw.decodeRaw` itself. -/
def decodeRawDirectPcs : List Nat :=
  (instructionPcs functionInstance_ssz_raw_decodeRaw.regions).filter fun pc =>
    !decodeRawInlinedChildPcs.contains pc

theorem decodeRawDirectPcs_count : decodeRawDirectPcs.length = 172 := by
  native_decide

/-- The separately attributed cleanup regions reached directly from `decodeRaw`.
They are absorbed for execution ownership, but are not direct `decodeRaw` function-instance PCs. -/
def decodeRawAbsorbedExcludedPcs : List Nat :=
  instructionPcs (Program.absorbedRanges generatedProgram functionInstance_ssz_raw_decodeRaw)

theorem decodeRawAbsorbedExcludedPcs_count : decodeRawAbsorbedExcludedPcs.length = 74 := by
  native_decide

/-- Entry, envelope validation, four direct `readOffset` preparations, and canonical-offset
setup. -/
def decodeRawEntryEnvelopeOffsetsPcs : List Nat :=
  [ 0x10444, 0x10448, 0x1044c, 0x10450, 0x10454, 0x10458, 0x1045c, 0x10460
  , 0x10464, 0x10468, 0x1046c, 0x10470, 0x10474, 0x10478, 0x1047c, 0x10480
  , 0x10490, 0x10498
  , 0x104a8, 0x104ac, 0x104b0, 0x104b4, 0x104b8, 0x104bc, 0x104c0, 0x104c4
  , 0x104c8, 0x104cc, 0x104d0, 0x104d4, 0x104d8
  , 0x105d4, 0x105d8, 0x105dc, 0x105e0, 0x105e4, 0x105e8, 0x105ec, 0x105f0
  , 0x105f4, 0x105f8, 0x105fc, 0x10600, 0x10604, 0x10608 ]

/-- Parent dispatches, child returns, result-record construction, and the successful result
route. -/
def decodeRawSpecializedDispatchReturnsSuccessPcs : List Nat :=
  [ 0x10614, 0x10618, 0x10638, 0x1063c, 0x10640
  , 0x10740, 0x10744, 0x10748, 0x1074c, 0x10750, 0x10754, 0x10758, 0x1075c
  , 0x126f8, 0x126fc, 0x12700, 0x12704, 0x12708, 0x1270c
  , 0x12720, 0x12724
  , 0x12794, 0x12798, 0x1279c
  , 0x12908
  , 0x12924, 0x12928, 0x1292c, 0x12930, 0x12934, 0x12938, 0x1293c, 0x12940
  , 0x12944, 0x12948, 0x12950, 0x12954, 0x12958
  , 0x12e64, 0x12e68, 0x12e6c, 0x12e70, 0x12e74, 0x12e78, 0x12e7c, 0x12e80
  , 0x12e84, 0x12e88, 0x12e8c, 0x12e90, 0x12e94, 0x12e98, 0x12e9c, 0x12ea0
  , 0x12ea4, 0x12ea8, 0x12eac, 0x12eb0, 0x12eb4, 0x12eb8
  , 0x12f90, 0x12f94, 0x12f98, 0x12f9c, 0x12fa0, 0x12fa4, 0x12fa8 ]

/-- All remaining direct PCs: rejection routes, terminal cleanup calls, status writes, copies,
and return. -/
def decodeRawRejectionCleanupStatusCopyEpiloguePcs : List Nat :=
  decodeRawDirectPcs.filter fun pc =>
    !decodeRawEntryEnvelopeOffsetsPcs.contains pc &&
      !decodeRawSpecializedDispatchReturnsSuccessPcs.contains pc

/-- The exact direct-PC partition, represented as a single list for computable audit checks. -/
def decodeRawPhasePcs : List Nat :=
  decodeRawEntryEnvelopeOffsetsPcs ++ decodeRawSpecializedDispatchReturnsSuccessPcs ++
    decodeRawRejectionCleanupStatusCopyEpiloguePcs

def decodeRawPhasePartitionB : Bool :=
  (decodeRawPhasePcs.all decodeRawDirectPcs.contains) &&
    (decodeRawDirectPcs.all decodeRawPhasePcs.contains) &&
      (decodeRawPhasePcs.eraseDups.length == decodeRawPhasePcs.length)

/-- The three phase lists are pairwise disjoint and exhaust exactly the 172 direct parent PCs. -/
theorem decodeRawPhasePartition_exact : decodeRawPhasePartitionB = true := by
  native_decide

theorem decodeRawEntryEnvelopeOffsetsPcs_count : decodeRawEntryEnvelopeOffsetsPcs.length = 45 := rfl

theorem decodeRawSpecializedDispatchReturnsSuccessPcs_count :
    decodeRawSpecializedDispatchReturnsSuccessPcs.length = 67 := rfl

theorem decodeRawRejectionCleanupStatusCopyEpiloguePcs_count :
    decodeRawRejectionCleanupStatusCopyEpiloguePcs.length = 60 := by
  native_decide

def DecodeRawCfgPhase.pcs : DecodeRawCfgPhase → List Nat
  | .entryEnvelopeOffsets => decodeRawEntryEnvelopeOffsetsPcs
  | .specializedDispatchReturnsSuccess => decodeRawSpecializedDispatchReturnsSuccessPcs
  | .rejectionCleanupStatusCopyEpilogue => decodeRawRejectionCleanupStatusCopyEpiloguePcs

/-- The typed, static hand-off for one independently proved parent phase.
The separate hierarchy artifact will attach selected contract boundaries to this static PC set. -/
structure DecodeRawCfgPhaseInterface where
  phase : DecodeRawCfgPhase
  pcs : List Nat

def decodeRawCfgPhaseInterface : DecodeRawCfgPhase → DecodeRawCfgPhaseInterface
  | .entryEnvelopeOffsets =>
      { phase := .entryEnvelopeOffsets
        pcs := decodeRawEntryEnvelopeOffsetsPcs }
  | .specializedDispatchReturnsSuccess =>
      { phase := .specializedDispatchReturnsSuccess
        pcs := decodeRawSpecializedDispatchReturnsSuccessPcs }
  | .rejectionCleanupStatusCopyEpilogue =>
      { phase := .rejectionCleanupStatusCopyEpilogue
        pcs := decodeRawRejectionCleanupStatusCopyEpiloguePcs }

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
