# Level 4 proof-authoring meta-analysis

Date: 2026-08-10. This study supports the active `PLAN_FLAME_REFINEMENT.md` Level 4 work. It
compares the four optimized `readOffset` occurrences, both selected deinit regions, and a first
deterministic retrieval prototype over the existing machine-proof corpus.

## Verdict

The current proofs are sound but too bottom-up. Proof authors repeatedly discover optimized value
carriers, child-return requirements, writable regions, and instruction schedules while constructing
Lean steps. That discovery produced useful interface corrections, but it does not scale to all of
Zesu. Machine geometry and routine frame transport should be generated before proof writing;
source-specific meanings and boundary carriers should remain explicit reviewed obligations.

The immediate target is not an end-to-end learned prover. It is a deterministic *proof preparation
packet* for each selected boundary and each parent-owned region:

1. source identity and semantic operation schedule;
2. exact optimized CFG, calls, returns, instruction operands, and memory effects;
3. candidate source-value to register/stack bindings, with LLVM/DWARF provenance and empirical
   validation where measurable;
4. the caller-use contract: values read after return, exact return PC, preserved registers, and
   protected memory regions;
5. nearest existing proof templates, followed by generated instruction wrappers, `Seg` composition,
   and frame obligations.

Lean still checks every generated term. Retrieval or probabilistic ranking may suggest a template;
it never admits a semantic claim.

## What the case studies found

### Four `readOffset` occurrences

All four instances implement one source meaning and each owns exactly ten optimized instructions:
four `lbu`, three `slli`, and three `or`. Their forty instructions are interleaved, with fragment
counts `2/3/3/1`; therefore the reusable object is an occurrence descriptor and generic fragment
theorem, not a contiguous function theorem.

The non-final reader phase contains 563 lines across nine repetitive leaf units. Their only material
parameters are source offset, generated instance/schedule, temporary register bank, final register,
and sibling-preservation set. A descriptor plus one generic leaf theorem projects this to about 207
lines, a 356-line or 63% reduction. The measured build saving is probably below one second; the main
gain is authoring speed and eliminating transcription/frame drift. The 204 lines composing the real
interleaving and the ordered final edges should remain explicit until a generated schedule language
can represent register lifetimes faithfully.

The validated prototype is `tools/studies/read_offset_occurrences.py`; the detailed study is
`READ_OFFSET_META_STUDY.md`.

### Selected deinit regions

`RawExecutionWitness.deinit` has 29 instructions and three external calls;
`RawNewPayloadRequest.deinit` has 45 instructions and five calls. A normalized sequence matcher
aligns 21 of the 29 witness instructions with the payload region, finds 15 shared three-grams,
11 shared five-grams, and a genuine 13-instruction packet:

```text
ld ld ld ld sd sd sd sd addi auipc jalr ld ld
```

The packet is structural, not semantically identical: record offsets, base registers, nested target,
and caller frames differ. The larger partial proof required 1,323 step-module lines plus a 135-line
parent adapter while locally composing only twelve instructions before correctly consuming its
selected contract. That history shows the high-value abstractions are:

- generated prologue/epilogue schedules from frame size and saved registers;
- a typed `free(slice)` call packet over descriptor offsets, temporary stack slots, and target;
- a heterogeneous cleanup schedule distinguishing slice frees from nested deinit calls;
- caller-visible contract generation before body proof work begins.

The detailed, regression-tested study is `docs/research/level4-deinit-proof-reuse-study.md`; its
matcher is `tools/compare_deinit_regions.py`.

### Corpus retrieval prototype

`tools/analyze_machine_proof_corridors.py` joins literal Lean PC inventories with the pinned
machine-region database, normalizes register roles across sequences, and performs length-aware
subsequence retrieval. It distinguishes all inventories from a deliberately weak source-level
signal that a nearby theorem names the inventory and uses a composition combinator. It does *not*
prove that the theorem compiled or discharged every PC.

The integration corpus currently exposes 23 literal inventories but only three such
composition-backed candidates, so retrieval quality is not yet broadly measurable. On a development
branch containing the fi16 producer proof, the intended `sub; li` and six-store queries retrieve
useful shapes. On the reviewed integration tip, the same queries demonstrate the current index's
sparsity rather than a reliable ranking. This prototype is useful evidence that normalization is
feasible, but not yet evidence of corpus-wide precision.

The next correction is an explicit kernel-checked or generated `MachineProofManifest` emitted by
each completed region proof: PC inventory, composing theorem, instruction/frame schema, source
identity, and prerequisite contract tokens. Retrieval should index that manifest instead of guessing
proof completion from Lean source text.

## How effectively source is used today

Source use is real but incomplete:

- source meanings define semantic contracts and independent probes validate outcomes;
- DWARF/source identities and inline stacks connect emitted regions to pinned Zig locations;
- generated CFG/disassembly checks the shipped ELF exactly;
- production traces falsify measurable carrier and route claims.

What is missing is the compiler middle layer. The retained artifacts do not include normalized LLVM
IR, Machine IR, optimization remarks, or a stable value-location history. Consequently, facts such
as “source slice bound becomes `s8`, then `sp+0x250`, then r7 `a3`” are rediscovered by reverse
dataflow plus runtime snapshots. Retaining reproducibly tied LLVM/MIR artifacts is the highest-value
source-linkage pre-work.

## Prioritized improvements

### P0: prepare contracts and value flow before Lean

1. Generate a caller-use report for every selected child: exact entry/return, registers and memory
   consumed after return, protected parent resources, and source values those carriers represent.
2. Retain normalized LLVM IR, inline/optimization records, and Machine IR/value-location data tied to
   the pinned object and production ELF. Keep DWARF as corroboration, not the sole value map.
3. Extend production capture selectively for unresolved carriers, with vector/PC/edge correlation and
   deletion/value/route mutations, as done for fi16 x2/x19/x24.
4. Review and admit the complete boundary contract before dispatching instruction proof work.

This would have exposed the excluded-deinit return frame, reader source lanes, and r7 temporary slots
before hundreds of proof lines were written.

### P1: generate routine Lean structure

1. Emit typed region descriptors containing PCs, decoded instruction classes, successors, writes,
   memory regions, live inputs/outputs, and selected-child edges.
2. Generate instruction-class wrapper invocations and a `Seg` skeleton, leaving named semantic,
   access, alignment, and frame goals.
3. Generate exact ownership/subset/write-disjointness facts instead of repeating `native_decide`
   at every site.
4. Add generic, reviewed schemas for reader fragments, save/restore prologues, store packets,
   call/return packets, and typed memory-slot transport.
5. Generate occurrence-specific thin wrappers so the proof tree remains readable and UI identities
   remain explicit.

### P2: build a trustworthy reuse index

1. Add `MachineProofManifest` records to completed proofs; never infer “discharged” from filenames or
   a `...Pcs` definition.
2. Index deterministic features separately: source identity, CFG/call topology, normalized opcode
   sequence, cross-instruction register flow, memory-effect shape, frame signature, and contract-token
   requirements.
3. Maintain a reviewer-labelled evaluation set of useful/non-useful template matches. Measure
   precision at `k`, coverage, and authoring reduction before expanding automation.
4. Only then add graph embeddings or learned ranking to improve recall under scheduling and register
   allocation. Learned results remain suggestions checked against exact deterministic features.

## Recommended workflow

For each new region:

1. generate the proof-preparation packet;
2. run deterministic similarity retrieval and show parameter differences;
3. review the source/compiler carrier map and selected contract;
4. generate the Lean skeleton;
5. write only the semantic and exceptional obligations by hand;
6. use Lean LSP for the inner loop, then focused/profile/root/trust gates at coherent checkpoints;
7. publish the proof manifest so later agents retrieve the completed pattern.

This also solves the coordination problem: agents need not remember or communicate every analogous
proof if all completed shapes and their prerequisites live in a shared generated index.

## Expected payoff and limits

The reader study supports a measured 63% reduction in repetitive leaf-proof lines. The deinit study
supports a preliminary 60–80% generation target for routine instruction wrappers, composition, and
frame transport, but not for semantic field meanings or nested-child contracts. These are authoring
estimates, not claims of equivalent build-time savings.

Probabilistic binary analysis is promising for ranking larger analogies, especially reordered call
packets and register-allocated variants. It should follow—not replace—the deterministic source/CFG/
effect representation and a labelled evaluation corpus. The immediate bottleneck is missing proof
preparation and compiler value provenance, not insufficient model sophistication.
