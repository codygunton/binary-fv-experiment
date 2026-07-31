import BinaryFv.Zesu.SpecBridge.Decode
import BinaryFv.Zesu.Artifact.Image
import BinaryFv.Zesu.Artifact.AbiManifest
import BinaryFv.Zesu.Artifact.Layout
import BinaryFv.Zesu.Artifact.Symbols
import BinaryFv.Zesu.Artifact.AllocatorCalls
import BinaryFv.Zesu.Artifact.PrimitiveReadInventory
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.ControlFlow.FunctionWords
import BinaryFv.Zesu.Elfling.GeneratedValidationBridges
import BinaryFv.Zesu.Elfling.GeneratedProgramValidation
import BinaryFv.Zesu.Elfling.GeneratedProvenanceCheck
import BinaryFv.Zesu.Elfling.GeneratedProgramCfg
import BinaryFv.Zesu.Elfling.GeneratedReachabilityExact
import BinaryFv.Zesu.Elfling.GeneratedProgramEdgeClass
import BinaryFv.Zesu.Elfling.GeneratedProgramInstructions
import BinaryFv.Zesu.Elfling.GeneratedProgramNesting
import BinaryFv.Zesu.Elfling.GeneratedProgramReachablePartition
import BinaryFv.Zesu.Elfling.GeneratedDecoderGlobals
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.BlobScheduleAndResultStores
import BinaryFv.Zesu.MachineExecution.ParserBlocks
import BinaryFv.Zesu.MemoryRepresentation.RawV4
import BinaryFv.Zesu.MemoryRepresentation.Observers
import BinaryFv.Zesu.MemoryRepresentation.Result
import BinaryFv.Zesu.Runtime.AllocatorVtable
import BinaryFv.Zesu.Runtime.BumpAllocator
import BinaryFv.Zesu.Runtime.AllocationBound
import BinaryFv.Zesu.Runtime.MemoryCopy
import BinaryFv.Zesu.Contracts.Error
import BinaryFv.Zesu.Contracts.Environment
import BinaryFv.Zesu.Contracts.Options
import BinaryFv.Zesu.Contracts.Catalog
import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Contracts.ProgramCorrectness
import BinaryFv.Zesu.Contracts.CatalogAudit
import BinaryFv.Zesu.Contracts.Runtime
import BinaryFv.Zesu.Contracts.Entry
import BinaryFv.Zesu.Contracts.ExportedDecoder
import BinaryFv.Zesu.Contracts.Containers
import BinaryFv.Zesu.Contracts.Collections
import BinaryFv.Zesu.Contracts.Canonicality
import BinaryFv.Zesu.Contracts.Leaves
import BinaryFv.Zesu.SpecCorrespondence.PrimitiveReads
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Execution
import BinaryFv.Zesu.Interface
import BinaryFv.Zesu.Root

/-!
# `BinaryFv.Zesu`

Umbrella for verification of the Zesu Amsterdam V4 decoder. The specification bridge is specific to
the decoded Amsterdam `RawV4` value, while the artifact, machine execution, and proof layers bind that
behavior to the pinned Zesu binary without introducing a reverse dependency into generic RISC-V code.
-/
