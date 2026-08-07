import BinaryFv.Specs.SSZ.Decode
import BinaryFv.Zesu.Artifacts.Image
import BinaryFv.Zesu.Artifacts.AbiManifest
import BinaryFv.Zesu.Artifacts.Layout
import BinaryFv.Zesu.Artifacts.Symbols
import BinaryFv.Zesu.Artifacts.AllocatorCalls
import BinaryFv.Zesu.Artifacts.PrimitiveReadInventory
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.ControlFlow.FunctionWords
import BinaryFv.Zesu.Elflings.GeneratedValidationBridges
import BinaryFv.Zesu.Elflings.GeneratedProgramValidation
import BinaryFv.Zesu.Elflings.GeneratedProvenanceCheck
import BinaryFv.Zesu.Elflings.GeneratedProgramCfg
import BinaryFv.Zesu.Elflings.GeneratedReachabilityExact
import BinaryFv.Zesu.Elflings.GeneratedProgramInstructions
import BinaryFv.Zesu.Elflings.GeneratedProgramReachablePartition
import BinaryFv.Zesu.Elflings.GeneratedDecoderGlobals
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.BlobScheduleAndResultStores
import BinaryFv.Zesu.MachineExecution.ParserBlocks
import BinaryFv.Zesu.MemoryRepresentation.StatelessInput
import BinaryFv.Zesu.MemoryRepresentation.Observers
import BinaryFv.Zesu.MemoryRepresentation.Result
import BinaryFv.Zesu.Runtime.AllocatorVtable
import BinaryFv.Zesu.Runtime.BumpAllocator
import BinaryFv.Zesu.Runtime.AllocationBound
import BinaryFv.Zesu.Contracts.Error
import BinaryFv.Zesu.Contracts.Environment
import BinaryFv.Zesu.Contracts.Options
import BinaryFv.Zesu.Contracts.Catalog
import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Contracts.ContractComposition
import BinaryFv.Zesu.Contracts.CatalogAudit
import BinaryFv.Zesu.Contracts.Runtime
import BinaryFv.Zesu.Contracts.Entry
import BinaryFv.Zesu.Contracts.ExportedDecoder
import BinaryFv.Zesu.Contracts.Containers
import BinaryFv.Zesu.Contracts.Collections
import BinaryFv.Zesu.Contracts.Canonicality
import BinaryFv.Zesu.Contracts.PrimitiveReadsAndSlices
import BinaryFv.Zesu.MemoryRepresentation.PrimitiveReads
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Execution
import BinaryFv.Zesu.ControlFlow.MachineRegions
import BinaryFv.Zesu.Interface
import BinaryFv.Zesu.Root

/-!
# `BinaryFv.Zesu`

Umbrella for verification of the Zesu stateless-input decoder. The target-specific artifact, machine
execution, and proof layers bind the implementation-independent `BinaryFv.Specs.SSZ` behavior to the
pinned Zesu binary without introducing a reverse dependency into generic RISC-V code.
-/
