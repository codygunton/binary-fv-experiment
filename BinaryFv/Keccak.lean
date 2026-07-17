import BinaryFv.Keccak.CumulativeImports
import BinaryFv.Keccak.Reth.Analysis.CallClosure
import BinaryFv.Keccak.Reth.Analysis.Decode
import BinaryFv.Keccak.Reth.Analysis.FrameCoverage
import BinaryFv.Keccak.Reth.Analysis.FunctionWordSets
import BinaryFv.Keccak.Reth.Analysis.Reachability
import BinaryFv.Keccak.Reth.Analysis.StackFlow
import BinaryFv.Keccak.Reth.Artifact.Facts.CallWords
import BinaryFv.Keccak.Reth.Artifact.Facts.CodeRange
import BinaryFv.Keccak.Reth.Artifact.Facts.HelperBytes
import BinaryFv.Keccak.Reth.Artifact.Facts.ImageByte
import BinaryFv.Keccak.Reth.Artifact.Facts.StoreWord
import BinaryFv.Keccak.Reth.Artifact.Facts.Words
import BinaryFv.Keccak.Reth.Artifact.Facts.XorBlockBytes
import BinaryFv.Keccak.Reth.Artifact.Image
import BinaryFv.Keccak.Reth.Artifact.Layout
import BinaryFv.Keccak.Reth.Execution.Concrete
import BinaryFv.Keccak.Reth.Execution.DirectCall
import BinaryFv.Keccak.Reth.Proof.Common.ArtifactFetch
import BinaryFv.Keccak.Reth.Proof.Common.CallFetch
import BinaryFv.Keccak.Reth.Proof.Common.CallSites
import BinaryFv.Keccak.Reth.Proof.Common.FetchMmio
import BinaryFv.Keccak.Reth.Proof.Common.StackFrames
import BinaryFv.Keccak.Reth.Proof.Common.StackWindow
import BinaryFv.Keccak.Reth.Proof.Helpers.ArithDispatch
import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSlice
import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSliceDispatch
import BinaryFv.Keccak.Reth.Proof.Helpers.Decode
import BinaryFv.Keccak.Reth.Proof.Helpers.Fetch
import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy
import BinaryFv.Keccak.Reth.Proof.Helpers.Memset
import BinaryFv.Keccak.Reth.Proof.Legacy.CoreFetchMemory
import BinaryFv.Keccak.Reth.Proof.Legacy.CoreStep
import BinaryFv.Keccak.Reth.Proof.Legacy.CoreTryStep
import BinaryFv.Keccak.Reth.Proof.Legacy.XorContracts
import BinaryFv.Keccak.Reth.Proof.Store.Decode
import BinaryFv.Keccak.Reth.Proof.Store.Fetch
import BinaryFv.Keccak.Reth.Proof.Store.StepContract
import BinaryFv.Keccak.Reth.Proof.Store.Triple
import BinaryFv.Keccak.Reth.Proof.XorBlock.Contract
import BinaryFv.Keccak.Reth.Proof.XorBlock.Decode
import BinaryFv.Keccak.Reth.Proof.XorBlock.Fetch
import BinaryFv.Keccak.Reth.Root
import BinaryFv.Keccak.SpecBridge.Lanes

/-!
# `BinaryFv.Keccak`

Umbrella for the Keccak target layer: the pinned Reth artifact and its ABI/layout, static analyses of
that artifact, executable machine setup, and the proofs connecting it to `Spec.Keccak`.
-/
