import BinaryFv.Keccak.CallStepContract
import BinaryFv.Keccak.CallArtifactFetch
import BinaryFv.Keccak.StackBound
import BinaryFv.Keccak.MemcpyContract
import BinaryFv.Keccak.MemsetContract
import BinaryFv.Keccak.CopyFromSliceContract
import BinaryFv.Keccak.HelperFraming
import BinaryFv.Keccak.Root
import BinaryFv.Keccak.Concrete
import BinaryFv.Keccak.ArtifactFetchMmio
import BinaryFv.Keccak.ReachabilityInventory
import BinaryFv.Keccak.FrameRuntime
import BinaryFv.Keccak.StoreStepTriple
import BinaryFv.Keccak.TraceRunner
import BinaryFv.Keccak.XorBlockDecodeFacts
import BinaryFv.Keccak.XorBlockArtifactFetch
import BinaryFv.RiscV.TryStepFetchMemoryContract
import BinaryFv.RiscV.DecodeFrame
import BinaryFv.RiscV.ShiftOrExecuteContract

/-!
# Cumulative import / co-elaboration check

This module exists purely as a **build check**: it imports the whole root-facing stage stack into a
*single* Lean environment, so that `lake build` fails loudly if any two branches of the development
stop being importable side by side.

It is not a reduced manifest.  The imports above are the *antichain* of `BinaryFv.lean` -- the
root-facing modules that no other root import already subsumes -- so their transitive closure is
exactly the full root surface (every module `BinaryFv.lean` names is either listed here or is an
ancestor of one that is).  Importing them together therefore exercises the real cumulative
environment, not a subset.  The first seven are additionally named because they are the stage-4 /
inherited-PR-#23 modules this check was introduced to protect: `CallStepContract` /
`CallArtifactFetch` alongside `MemcpyContract` / `MemsetContract` / `CopyFromSliceContract` /
`StackBound` / `HelperFraming`.

## Why this check earns its keep

Some declarations are *realized lazily, per-module*: a tactic that needs a reserved auxiliary
constant builds it on demand and records it in the `.olean` of whichever module happened to trigger
it first.  Two sibling modules can then each realize their own copy, and each module still builds
perfectly well on its own -- the failure only appears when something imports both:

```
import BinaryFv.Keccak.CallStepContract failed, environment already contains
'Register.enumToBitVec' from BinaryFv.Keccak.MemcpyContract
```

That is precisely what happened here: `bv_decide`'s enum preprocessing pass independently realized
`Register.enumToBitVec` / `Register.eq_iff_enumToBitVec_eq` (and the same pair for `Privilege`) in
both `MemcpyContract` and `CallStepContract`, which made the inherited call imports un-restorable in
`BinaryFv.lean` until the auxiliaries were hoisted into the shared ancestor
`BinaryFv.RiscV.SailEnumAux`.

Because per-module builds cannot detect this class of breakage, and a root manifest can be made to
"pass" simply by dropping the offending import, this module pins the property down explicitly: the
cumulative stack co-elaborates.

## Sanity checks

The `example`s below force the capstone contracts of the separate branches to be simultaneously
elaborable and type-correct in this one environment -- i.e. the co-import is genuine and the
constants are really usable together, not merely present.  They restate nothing: each just names an
existing theorem at its existing type.
-/

namespace BinaryFv.Keccak.CumulativeImports

open BinaryFv.Keccak

/-- The three helper capstones and the inherited call/stack surface all resolve in one environment. -/
example := @memcpy_contract
example := @memset_contract
example := @copy_from_slice_contract
example := @callWord_fetchBytesAt
example := @tryStepCallRetires
example := @SpDepthInWindow.entry

/-- The reviewed helper framing conclusions co-elaborate with the call branch. -/
example := @MemFramed.mem_unchanged_outside
example := @MemFramed.source_preserved

end BinaryFv.Keccak.CumulativeImports
