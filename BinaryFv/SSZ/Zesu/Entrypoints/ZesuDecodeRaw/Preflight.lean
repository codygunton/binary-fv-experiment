import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Layout

/-!
# Rejecting the wrong binary or an oversized input

Before constructing Sail state, the runner checks the caller-supplied ELF and input.

First, `RiscvSpec.execute` takes a `ValidatedElf`. Its
`parsed_ok`/`layout` fields already guarantee it parses and has an executable load layout, but not
that it is *this* proof's binary — a caller could hand a different, well-formed ELF. So the gate
compares its bytes to `Artifact.bytes`, the one Nix-built image the whole proof is about. A
mismatched artifact is rejected with `.invalidArtifact`; a matching one is, by parser determinism,
the canonical `SSZ.binary`, so everything the artifact layer proved about `Artifact` transfers
to it.

Second, the public theorem only claims correctness for
`input.size < 2 MiB`; the runner makes that a runtime guard so no address computed from the input
length can exceed the pinned input buffer. An input at or above the bound is rejected before the
buffer base is ever touched.

Neither check reads machine memory or runs a Sail step — they are decidable facts about the caller's
`ByteArray`s — so "before any address arithmetic" is literal.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.SSZ
open BinaryFv.SSZ.Zesu

/-- Whether a caller-supplied validated ELF is the canonical pinned artifact. The `parsed_ok` and
`layout` fields already establish well-formedness; this is the one remaining check — that the bytes
are the proof's own image and not some other well-formed ELF.

`ByteArray` has `DecidableEq` but not `LawfulBEq`, so the check is `decide (… = …)` rather than `==`,
which gives a clean bridge to the propositional byte equality the framing proofs consume. -/
def artifactIsCanonical (binary : RiscvSpec.ValidatedElf) : Bool :=
  decide (binary.bytes = Artifact.bytes)

/-- Whether an input is within the theorem's admissible size. Identical to the public theorem's
premise, so the runtime guard and the stated theorem cannot diverge. -/
def inputWithinBound (input : ByteArray) : Bool :=
  decide (input.size < Runtime.maximumInputBytes)

/-- The preflight result: `ok` if the caller's ELF is the pinned artifact and the input is within the
theorem's bound, `error .invalidArtifact` otherwise.

Both rejection reasons map to `.invalidArtifact` deliberately: a non-canonical artifact is genuinely
invalid, and an oversized input is *outside the public theorem entirely* (which only claims anything
for `input.size < 2 MiB`), so no specific outcome is owed for it — rejecting is the safe choice and
the exact error is unconstrained. The distinction that the *proof* cares about is exposed as the two
separate `Bool` predicates, which the accepted-run correspondence consumes individually; the `Except`
here is only the proceed/stop decision. -/
def preflight (binary : RiscvSpec.ValidatedElf) (input : ByteArray) :
    Except RiscvSpec.ExecutionError Unit :=
  if artifactIsCanonical binary then
    if inputWithinBound input then .ok ()
    else .error .invalidArtifact
  else .error .invalidArtifact

/-! ## The gate does what it says

These are stated generically over *any* `binary` the gate accepts, so `Root.lean` — where the
concrete `SSZ.binary` lives — can apply them without this module depending on the root. The concrete
`SSZ.binary` satisfies `artifactIsCanonical` by `rfl`, which the runner discharges at the call site. -/

/-- A canonical caller-supplied ELF has exactly the artifact's parse, so it *is* the proof's binary
up to the parsed ELF. Parser determinism is the load-bearing step: two byte-identical inputs parse to
the same `Elf64`. -/
theorem canonical_parses_as_artifact {binary : RiscvSpec.ValidatedElf}
    (h : artifactIsCanonical binary = true) :
    BinaryFv.RiscV.Elf64.parse binary.bytes = .ok Artifact.elf := by
  have hbytes : binary.bytes = Artifact.bytes := by
    unfold artifactIsCanonical at h; exact of_decide_eq_true h
  rw [hbytes]; exact Artifact.parsed_ok

/-- A canonical ELF's parsed image is the canonical program image the contracts pin. So once the gate
passes, `Artifact.programImage`-based framing (the runner layout's `loaded_disjoint_from_runner`, the
occurrence regions) applies to the caller's binary without re-deriving anything. -/
theorem canonical_image_is_programImage {binary : RiscvSpec.ValidatedElf}
    (h : artifactIsCanonical binary = true) :
    binary.elf.programImage = Artifact.programImage := by
  have hparse := canonical_parses_as_artifact h
  have hbin : BinaryFv.RiscV.Elf64.parse binary.bytes = .ok binary.elf := binary.parsed_ok
  have : Artifact.elf = binary.elf := by
    have := hparse.symm.trans hbin; exact (Except.ok.injEq _ _).mp this
  have himg : Artifact.programImage = Artifact.elf.programImage := by
    unfold Artifact.programImage; rw [Artifact.parsed_ok]
  rw [himg, this]

/-- An admissible input passes the bound gate. -/
theorem within_bound_of_admissible {input : ByteArray} (h : input.size < Runtime.maximumInputBytes) :
    inputWithinBound input = true := by
  unfold inputWithinBound; simpa using h

/-- Preflight accepts any canonical binary on any admissible input. -/
theorem preflight_ok {binary : RiscvSpec.ValidatedElf} (hcanon : artifactIsCanonical binary = true)
    {input : ByteArray} (h : input.size < Runtime.maximumInputBytes) :
    preflight binary input = .ok () := by
  unfold preflight
  rw [hcanon, if_pos rfl, within_bound_of_admissible h, if_pos rfl]

/-- **Negative — a non-canonical artifact is rejected.** Any ELF whose bytes differ from the pinned
image fails the gate, whatever else is well-formed about it. -/
theorem preflight_rejects_wrong_artifact {binary : RiscvSpec.ValidatedElf} (input : ByteArray)
    (h : binary.bytes ≠ Artifact.bytes) :
    preflight binary input = .error .invalidArtifact := by
  unfold preflight artifactIsCanonical
  rw [decide_eq_false h, if_neg (by simp)]

/-- **Negative — an oversized input is rejected** before any address arithmetic, even on a canonical
binary. -/
theorem preflight_rejects_oversized_input {binary : RiscvSpec.ValidatedElf}
    (hcanon : artifactIsCanonical binary = true) {input : ByteArray}
    (h : Runtime.maximumInputBytes ≤ input.size) :
    preflight binary input = .error .invalidArtifact := by
  unfold preflight
  rw [hcanon, if_pos rfl]
  have hb : inputWithinBound input = false := by
    unfold inputWithinBound; exact decide_eq_false (by omega)
  rw [hb, if_neg (by simp)]

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
