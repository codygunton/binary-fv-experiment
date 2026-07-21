import BinaryFv.Binary.Elfling.Instance

/-!
# Generated Elfling data — `decodeOptionalBlobSchedule` vertical slice (milestone 3)

Deterministically extracted from the validated DWARF sidecar
(`zesu-raw-ssz-decoder.o`, decoder `.text` sha256 f946b25e…, DIE 0x00004039) by
`docs/ai/plan/artifacts/extract_blob_schedule_instance.py`. Object-relative DWARF ranges are
mapped to canonical-ELF PCs by `+0x102b0` (the decoder object `.text` base, Amendment A).
This is address-bearing generated data (untrusted); `BlobScheduleMapping.lean` validates it
against the canonical trace and binds it to the address-free catalog identity and contract.
-/

namespace BinaryFv.SSZ.Zesu.Elfling

open BinaryFv.Binary.Elfling

def decoderSourceFile : SourceFile := { path := "src/stateless/stateless/ssz_raw.zig" }

/-- Address-free identity of the single inline occurrence of `decodeOptionalBlobSchedule`. -/
def blobScheduleInstanceId : InstanceId :=
  { function := { declaration := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeOptionalBlobSchedule" }, specialization := #[] },
    inlineStack := [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeRaw" }, callSite := { line := 211, column := 48 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeChainConfig" }, callSite := { line := 355, column := 44 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeForkConfig" }, callSite := { line := 371, column := 56 } }] }

/-- The enclosing occurrence (`decodeForkConfig`) this instance is inlined into. -/
def blobScheduleParentId : InstanceId :=
  { function := { declaration := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeForkConfig" }, specialization := #[] },
    inlineStack := [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeRaw" }, callSite := { line := 211, column := 48 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeChainConfig" }, callSite := { line := 355, column := 44 } }] }

/-- `readU64` reading blob-schedule field 0 (source line 400). -/
def readU64Field0Id : InstanceId :=
  { function := { declaration := { file := decoderSourceFile, qualifiedName := "ssz_raw.readU64" }, specialization := #[] },
    inlineStack := [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeRaw" }, callSite := { line := 211, column := 48 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeChainConfig" }, callSite := { line := 355, column := 44 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeForkConfig" }, callSite := { line := 371, column := 56 } }] ++ [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeOptionalBlobSchedule" }, callSite := { line := 400, column := 34 } }] }

/-- `readU64` reading blob-schedule field 1 (source line 401). -/
def readU64Field1Id : InstanceId :=
  { function := { declaration := { file := decoderSourceFile, qualifiedName := "ssz_raw.readU64" }, specialization := #[] },
    inlineStack := [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeRaw" }, callSite := { line := 211, column := 48 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeChainConfig" }, callSite := { line := 355, column := 44 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeForkConfig" }, callSite := { line := 371, column := 56 } }] ++ [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeOptionalBlobSchedule" }, callSite := { line := 401, column := 31 } }] }

/-- `readU64` reading blob-schedule field 2 (source line 402). -/
def readU64Field2Id : InstanceId :=
  { function := { declaration := { file := decoderSourceFile, qualifiedName := "ssz_raw.readU64" }, specialization := #[] },
    inlineStack := [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeRaw" }, callSite := { line := 211, column := 48 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeChainConfig" }, callSite := { line := 355, column := 44 } }, { caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeForkConfig" }, callSite := { line := 371, column := 56 } }] ++ [{ caller := { file := decoderSourceFile, qualifiedName := "ssz_raw.decodeOptionalBlobSchedule" }, callSite := { line := 402, column := 52 } }] }

def readU64Field0Instance : FunctionInstance :=
  { id := readU64Field0Id, regions := #[{ start := 76988, size := 32 }, { start := 77036, size := 28 }, { start := 77080, size := 8 }, { start := 77104, size := 4 }, { start := 77204, size := 8 }, { start := 77228, size := 4 }, { start := 77240, size := 4 }], entryPc := 76988, exitPcs := #[77244],
    parent? := some blobScheduleInstanceId, children := #[], externalCalls := #[],
    declProvenance := { sourceFileHash := "ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131", declSpan := { line := 563, column := 1 } },
    provenance := { sidecarHash := "f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b", entryOffset := 16441, extractorVersion := "blob-schedule-slice-v1" }, symbol? := none }

def readU64Field1Instance : FunctionInstance :=
  { id := readU64Field1Id, regions := #[{ start := 77020, size := 16 }, { start := 77064, size := 16 }, { start := 77088, size := 16 }, { start := 77108, size := 12 }, { start := 77136, size := 8 }, { start := 77156, size := 4 }, { start := 77212, size := 8 }, { start := 77232, size := 4 }, { start := 77244, size := 4 }], entryPc := 77020, exitPcs := #[77248],
    parent? := some blobScheduleInstanceId, children := #[], externalCalls := #[],
    declProvenance := { sourceFileHash := "ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131", declSpan := { line := 563, column := 1 } },
    provenance := { sidecarHash := "f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b", entryOffset := 16441, extractorVersion := "blob-schedule-slice-v1" }, symbol? := none }

def readU64Field2Instance : FunctionInstance :=
  { id := readU64Field2Id, regions := #[{ start := 77120, size := 16 }, { start := 77144, size := 12 }, { start := 77160, size := 44 }, { start := 77220, size := 8 }, { start := 77236, size := 4 }, { start := 77248, size := 8 }], entryPc := 77120, exitPcs := #[77256],
    parent? := some blobScheduleInstanceId, children := #[], externalCalls := #[],
    declProvenance := { sourceFileHash := "ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131", declSpan := { line := 563, column := 1 } },
    provenance := { sidecarHash := "f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b", entryOffset := 16441, extractorVersion := "blob-schedule-slice-v1" }, symbol? := none }

/-- The generated `decodeOptionalBlobSchedule` occurrence: three discontiguous canonical-ELF
    fragments, three nested `readU64` field reads, inlined into `decodeForkConfig`. -/
def blobScheduleInstance : FunctionInstance :=
  { id := blobScheduleInstanceId, regions := #[{ start := 76888, size := 8 }, { start := 76936, size := 48 }, { start := 76988, size := 268 }], entryPc := 76888, exitPcs := #[77256],
    parent? := some blobScheduleParentId, children := #[readU64Field0Id, readU64Field1Id, readU64Field2Id], externalCalls := #[],
    declProvenance := { sourceFileHash := "ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131", declSpan := { line := 396, column := 1 } },
    provenance := { sidecarHash := "f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b", entryOffset := 16441, extractorVersion := "blob-schedule-slice-v1" }, symbol? := none }

/-- The instance together with its nested children, as extracted. -/
def blobScheduleInstances : Array FunctionInstance :=
  #[blobScheduleInstance, readU64Field0Instance, readU64Field1Instance, readU64Field2Instance]

end BinaryFv.SSZ.Zesu.Elfling
