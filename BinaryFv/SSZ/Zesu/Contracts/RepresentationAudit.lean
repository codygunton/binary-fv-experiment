import BinaryFv.SSZ.Zesu.Contracts.Ownership
import BinaryFv.SSZ.Zesu.Contracts.CanonicalParams

/-!
# Auditing the canonical representations against `LocalTo`

`Ownership.localTo_is_a_real_obligation` proves a representation reading any non-memory component of
`State` is `LocalTo` **no** region — not even the universal one. So the ownership discipline only
applies to a container once that container's representation has been shown memory-determined. This
module runs that audit.

## What is proved here, and what is not

`MemDetermined` is `LocalTo` at the universal region, stated directly on state predicates so it
composes bottom-up over the representation primitives. Proving it for a representation establishes
the representation is **memory-only** — it closes the `localTo_is_a_real_obligation` hole and makes
the container eligible for the discipline.

It does **not** give disjointness. That needs the representation's actual *footprint* — the region it
is local to — which is a strictly stronger and more laborious result: for `RawV4Rep` the footprint is
the root allocation, ten heap arrays, the descriptor table and every borrowed input slice. Footprints
are not computed here.

So a container appearing below is eligible for the discipline, not yet protected by it.

## Audit status

**Memory-determined, proved below:** `canonicalRepForkActivation`, `canonicalRepForkConfig`,
`canonicalRepChainConfig` — the three non-allocating chain containers.

**Not yet audited:** `canonicalRepRawV4`, `canonicalRepExecutionWitness`,
`canonicalRepExecutionRequests`, `canonicalRepExecutionPayload`, `canonicalRepNewPayloadRequest`.
A mechanical scan found no reference to `regs`, `pc`, `choiceState`, `tags`, `cycleCount` or
`sailOutput` anywhere under `MemoryRepresentation/`, so these are *expected* to be memory-determined
too — but a grep is not a proof and this row has been bitten three times by exactly that substitution.
They are listed as open rather than assumed.
-/

namespace BinaryFv.SSZ.Zesu.Contracts.RepresentationAudit

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Contracts.Ownership

/-- A state predicate transports across states that agree on all of memory.

This is `LocalTo` at the universal region, phrased on bare state predicates so the representation
primitives can be composed bottom-up before being packaged back into a
`ContainerRepresentation`. -/
def MemDetermined (P : State → Prop) : Prop :=
  ∀ s1 s2, (∀ address, s1.mem.get? address = s2.mem.get? address) → P s1 → P s2

theorem memDetermined_and {P Q : State → Prop}
    (hp : MemDetermined P) (hq : MemDetermined Q) :
    MemDetermined (fun s => P s ∧ Q s) :=
  fun s1 s2 agree h => ⟨hp s1 s2 agree h.1, hq s1 s2 agree h.2⟩

/-! ## The primitives

Every container representation bottoms out in these two. Both are pointwise claims about
`state.mem.get?`, so both transport by rewriting with the agreement hypothesis — which is exactly
what "memory-only" means, made mechanical. -/

theorem memDetermined_optionTag (base : Nat) (present : Bool) :
    MemDetermined (fun s => OptionTagRep s base present) :=
  fun _ _ agree h => (agree base).symm.trans h

theorem memDetermined_word64 (base value : Nat) :
    MemDetermined (fun s => Word64LERep s base value) :=
  fun _ _ agree h index hindex => (agree _).symm.trans (h index hindex)

/-! ## The option and blob-schedule layers -/

theorem memDetermined_optionU64 (base : Nat) (value : Option UInt64) :
    MemDetermined (fun s => OptionU64Rep s base value) := by
  cases value with
  | none => exact memDetermined_optionTag _ _
  | some v =>
      exact memDetermined_and (memDetermined_word64 base v.toNat) (memDetermined_optionTag _ _)

theorem memDetermined_blobSchedule (base : Nat) (value : SszBridge.RawBlobSchedule) :
    MemDetermined (fun s => BlobScheduleRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _)
    (memDetermined_and (memDetermined_word64 _ _) (memDetermined_word64 _ _))

theorem memDetermined_optionBlobSchedule (base : Nat)
    (value : Option SszBridge.RawBlobSchedule) :
    MemDetermined (fun s => OptionBlobScheduleRep s base value) := by
  cases value with
  | none => exact memDetermined_optionTag _ _
  | some v => exact memDetermined_and (memDetermined_blobSchedule base v) (memDetermined_optionTag _ _)

/-! ## The three chain containers -/

theorem memDetermined_forkActivation (base : Nat) (value : SszBridge.RawForkActivation) :
    MemDetermined (fun s => ForkActivationRep s base value) :=
  memDetermined_and (memDetermined_optionU64 _ _) (memDetermined_optionU64 _ _)

theorem memDetermined_forkConfig (base : Nat) (value : SszBridge.RawForkConfig) :
    MemDetermined (fun s => ForkConfigRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _)
    (memDetermined_and (memDetermined_forkActivation _ _) (memDetermined_optionBlobSchedule _ _))

theorem memDetermined_chainConfig (base : Nat) (value : SszBridge.RawChainConfig) :
    MemDetermined (fun s => ChainConfigRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _) (memDetermined_forkConfig _ _)

/-! ## The audit results, stated as `LocalTo`

`LocalTo` at the universal region is the eligibility fact the discipline needs. Stated on the
canonical representations themselves, so these are claims about the objects the root actually uses
rather than about the primitives. -/

theorem localTo_canonicalRepForkActivation :
    LocalTo canonicalRepForkActivation (fun _ _ => True) :=
  fun _ _ value s1 s2 base agree h =>
    memDetermined_forkActivation base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepForkConfig :
    LocalTo canonicalRepForkConfig (fun _ _ => True) :=
  fun _ _ value s1 s2 base agree h =>
    memDetermined_forkConfig base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepChainConfig :
    LocalTo canonicalRepChainConfig (fun _ _ => True) :=
  fun _ _ value s1 s2 base agree h =>
    memDetermined_chainConfig base value s1 s2 (fun a => agree a trivial) h

end BinaryFv.SSZ.Zesu.Contracts.RepresentationAudit
