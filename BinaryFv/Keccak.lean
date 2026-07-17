import BinaryFv.Keccak.ABI
import BinaryFv.Keccak.Artifact
import BinaryFv.Keccak.ArtifactCodeRange
import BinaryFv.Keccak.ArtifactFetch
import BinaryFv.Keccak.ArtifactFetchMmio
import BinaryFv.Keccak.CallArtifactFetch
import BinaryFv.Keccak.CallClosure
import BinaryFv.Keccak.CallStepContract
import BinaryFv.Keccak.Concrete
import BinaryFv.Keccak.Contracts
import BinaryFv.Keccak.CopyFromSliceContract
import BinaryFv.Keccak.CopyFromSliceDispatch
import BinaryFv.Keccak.CoreFetchMemoryContract
import BinaryFv.Keccak.CoreStepContract
import BinaryFv.Keccak.CoreStoreStepContract
import BinaryFv.Keccak.CoreTryStepContract
import BinaryFv.Keccak.CumulativeImports
import BinaryFv.Keccak.Decode
import BinaryFv.Keccak.Execution
import BinaryFv.Keccak.FrameCoverage
import BinaryFv.Keccak.HelperArithDispatch
import BinaryFv.Keccak.HelperArtifactFetch
import BinaryFv.Keccak.HelperDecodeFacts
import BinaryFv.Keccak.MemcpyContract
import BinaryFv.Keccak.MemsetContract
import BinaryFv.Keccak.ReachabilityInventory
import BinaryFv.Keccak.Root
import BinaryFv.Keccak.Stack
import BinaryFv.Keccak.StackBound
import BinaryFv.Keccak.StackFlow
import BinaryFv.Keccak.StackFrames
import BinaryFv.Keccak.StoreArtifactFetch
import BinaryFv.Keccak.StoreDecodeFact
import BinaryFv.Keccak.StoreStepTriple
import BinaryFv.Keccak.XorBlockArtifactFetch
import BinaryFv.Keccak.XorBlockContract
import BinaryFv.Keccak.XorBlockDecodeFacts

/-!
# `BinaryFv.Keccak`

Umbrella for the Keccak target layer: the pinned Reth artifact and its ABI/layout, static analyses of
that artifact, executable machine setup, and the proofs connecting it to `Spec.Keccak`.
-/
