# Proving an Optimized SHA-3 Binary Correct in Lean

## Executive judgment

The proposed strategy is fundamentally sound, but it needs one important change of level. The
proof should not be organized as a direct equality between a large Sail state-monad expression and
a pure SHA-3 function. It should use symbolic execution of the machine semantics as an *inner proof
method*, while exposing each binary routine through a Hoare-style contract over an abstract machine
state. A modest separation logic, or an equivalent explicit frame discipline, is what makes those
contracts compositional.

For this experiment, the right first theorem concerns the binary's internal `sha3` routine, not its
C `main`. The routine accepts an input pointer and length and writes 32 digest bytes. That interface
represents every `ByteArray` and avoids argument decoding, startup, output formatting, and Linux
syscalls. A second theorem can later connect `_start` and `main` to the command-line behavior. The
clean public claim can still be essentially the desired one:

```lean
theorem root_compliance :
    ∀ msg : ByteArray,
      RiscvSpec.execute binary msg = .ok (Sha3Spec.hashData msg)
```

The complexity belongs in `RiscvSpec.execute`, not in this statement. Internally, the proof must
establish binary identity, ELF loading, the RISC-V calling convention, memory safety, termination,
and the correspondence between final output memory and the pure result. The explicit `.ok` makes
successful execution part of the claim.

This is a credible medium-sized proof-of-concept, but not a short exercise. The current linked
binary contains 312 instructions in total, with 286 instructions across the selected SHA-3 and
harness symbols. Arbitrary-length input introduces loops whose correctness cannot be discharged by
simply evaluating the executable semantics. The proof needs loop invariants and reusable contracts.

## 1. What claim is being proved?

Several claims that sound like "the binary implements SHA-3" have materially different trust
boundaries.

1. **Test conformance:** the binary agrees with published vectors on selected inputs.
2. **Binary-to-Lean refinement:** for every supported input, the fixed binary agrees with the
   imported executable Lean implementation.
3. **Binary-to-standard compliance:** for every input, the fixed binary agrees with a formalization
   proved equivalent to FIPS 202.
4. **Cryptographic security:** the implemented function has collision, preimage, or other security
   properties.

This project is currently positioned to attempt claim 2. It is not yet claim 3 or 4. The imported
[`gdncc/Cryptography`](../specs/sha-3/README.md) implementation is executable, uses dependent types
to prove array accesses are in bounds, constrains the sponge API's absorb/squeeze phases, and has
been tested with NIST vectors. Its accompanying paper explicitly describes functional correctness
as testing, while its machine-checked proofs concern bounds and API sequencing. There is no theorem
in the imported repository proving `SHA3_256.hashData` equal to the mathematical algorithms in
FIPS 202.

That is acceptable for the stated proof-of-concept because the project deliberately accepts a Lean
implementation believed correct as its specification. The report and theorem names should say
"agrees with the selected Lean specification," not claim formal FIPS 202 compliance. A later,
separate development could formalize the FIPS algorithms and prove the selected Lean implementation
equivalent to them.

There are also three different input domains:

- FIPS 202 specifies functions over binary strings, including lengths not divisible by eight.
- `SHA3_256.hashData` accepts `ByteArray`, so it covers all finite *byte strings*.
- the current CLI accepts a NUL-terminated `argv[1]`, so it cannot represent byte arrays containing
  zero and does not expose non-byte-aligned messages.

Thus `∀ msg : ByteArray` is a useful and strong claim, but it is not literally "all bit vectors" in
the FIPS sense, and it cannot currently be a theorem about the CLI input path.

## 2. The standard shape of a binary proof

A foundational binary proof usually has the following layers.

### 2.1 Artifact and loader

The exact ELF bytes must be part of the theorem's meaning. A digest in build metadata is useful for
humans, but the proof needs either the bytes embedded as data or a checked parser result tied to
those bytes. The loader establishes which bytes occupy which addresses, the entry point, executable
permissions, zero-filled regions, and any relocation assumptions.

Without this layer, proving a fact about an opcode manually inserted at the recorded entry address
does not prove a fact about the binary. The existing one-instruction theorem is a valid test of the
Sail execution path, but it stops exactly at this boundary.

### 2.2 ISA execution

The Sail-generated Lean code gives a small-step operational semantics over architectural state:
registers, memory, privilege state, and effects. This state-monad representation is an appropriate
semantic foundation. It answers what a fetched and decoded instruction does.

It is not, by itself, an effective proof interface for a whole function. Repeatedly unfolding the
full Sail model exposes irrelevant architectural cases and produces enormous terms. Normal practice
is to symbolically execute concrete instructions once and derive simpler step equations, or to prove
that a smaller machine model simulates the relevant fragment of Sail.

### 2.3 Function and basic-block contracts

A binary function is represented semantically by an entry address, an ABI precondition, and a set
of possible exits with postconditions. A contract for the internal SHA-3 routine should say roughly:

```text
Pre:
  PC is the address of sha3;
  a0 points to msg.length readable bytes containing msg;
  a1 is msg.length;
  a2 points to 32 writable bytes;
  a3 is 32;
  stack and return address satisfy the ABI;
  code memory contains the fixed program.

Post:
  execution returns to ra;
  the 32 bytes at a2 equal Sha3Spec.hashData msg;
  callee-saved registers and all framed memory are unchanged;
  only permitted caller-saved registers and owned work memory may differ.
```

This is a Hoare triple. It is the precise version of the proposed condition that each binary
function `f_i^B` has the same input/output semantics as a logical function `f_i^L`.

### 2.4 Algorithmic refinement

Symbolic execution reduces blocks of RISC-V instructions to bit-vector and memory transformations.
The source code is valuable here as a guide to the intended loop invariants and intermediate
abstractions. It is not a premise of the proof. The proof obligation is between the actual decoded
instructions and the logical SHA-3 operations.

For SHA-3, useful abstract stages are:

- byte input and padding;
- absorption into 25 little-endian 64-bit lanes;
- each Keccak round (`theta`, `rho`, `pi`, `chi`, `iota`);
- the 24-round permutation;
- squeezing 32 output bytes.

The source-level names may suggest these lemmas, but the binary contracts should be attached to
addresses and control-flow regions. Optimization can inline, clone, merge, reorder, or eliminate
source functions. A symbol is debugging metadata and a convenient address label, not evidence of a
semantic boundary.

### 2.5 Composition and observation

Function contracts compose from the permutation through `sha3`, and optionally through `main` and
`_start`. The final theorem projects the relevant observation, such as 32 output bytes, while hiding
registers and scratch memory.

If the theorem says the program returns a digest, termination and absence of traps are not optional
details. They can be hidden behind `RiscvSpec.execute`, but the `.ok` equality must prove them. A
partial-correctness statement of the form "if it returns, its output is correct" is weaker and
should not be disguised as total equality.

## 3. Hoare logic and separation logic

Hoare logic and separation logic are related but answer different questions.

A Hoare triple `{P} code {Q}` says that execution from a state satisfying `P` has the behavior
described by `Q`. For total correctness, it also says execution terminates; for partial correctness,
it only constrains terminating executions. At binary level, `P` and `Q` mention registers, memory,
the PC, code bytes, and ABI facts.

Separation logic is a language and proof discipline for writing those state predicates modularly.
An assertion such as

```text
input ↦ bytes(msg)  *  output ↦ bytes(32)  *  stack ↦ stackFrame
```

states both the contents and disjoint ownership of three memory regions. Its frame rule allows a
function proof to preserve arbitrary unrelated state without naming it. This is exactly the issue
that appears when composing machine-code functions: the Keccak permutation owns its 200-byte state
and some registers, but should not have to describe the rest of memory.

For a completely closed whole-program proof, one could avoid separation logic by defining a giant
initial state and evaluating or reasoning about it directly. That approach becomes brittle as soon
as functions, loops, stack frames, or arbitrary input buffers are introduced. Some form of framing
is therefore lurking in the goal even if it is encoded as explicit disjointness hypotheses rather
than called separation logic.

The project does not need the full generality of Iris. A sequential, first-order resource model for
registers and byte ranges is probably sufficient. The local `evm-asm` repository demonstrates this
design in Lean: `cpsTripleWithin` quantifies over an arbitrary frame, gives an explicit step bound,
and composes contracts; its separating conjunction splits partial register/memory states. The useful
lesson is the contract shape, not that this project must copy that implementation unchanged.

## 4. Why `evm-asm` starts from the other end

`evm-asm` is solving a related but different problem. It authors RISC-V programs as Lean data and
proves their contracts as the program is assembled. That buys it several things:

- instruction boundaries and control-flow structure are known by construction;
- macro and function boundaries are chosen for proof composition;
- no C compiler, ELF parser, linker transformation, or disassembler is needed in the main proof;
- a deliberately small RV64IM semantics makes routine proofs tractable;
- a separate simulation layer can relate that small semantics to Sail.

That is not a rejection of symbolic execution from machine state. Its Hoare triples are defined in
terms of repeated machine steps, and current design work in that repository explicitly bridges
pre-generated symbolic step equations back into those triples. It starts from assembly because its
goal is to *construct* verified code without trusting a compiler. This project starts with an
existing optimized ELF and must recover structure that `evm-asm` retains by construction.

There is a useful hybrid: decode the fixed ELF into a small Lean RV64 instruction map, prove that
the map is exactly what the ELF and Sail decoder produce, prove the program using the small model,
and rely on a once-for-all simulation theorem from the small step to Sail. This keeps Sail as the
authoritative foundation while avoiding direct manipulation of its entire state on every program
proof. The simulation bridge itself must be complete for every instruction and memory behavior the
SHA-3 binary uses; an incomplete prototype cannot simply be assumed.

## 5. Existing tools and their fit

### Islaris, Isla, Iris, and Lithium

[Islaris](https://doi.org/10.1145/3519939.3523434) is the closest existing system to the proposed
workflow. It takes concrete Arm or RISC-V machine code, uses Isla and an SMT solver to symbolically
execute the Sail model into a simplified trace, and proves a user specification over that trace in
an Iris-based separation logic. Lithium is the proof-search language that automates the separation
logic reasoning. For RISC-V, Islaris also provides optional translation validation from the Isla
trace to Sail-generated Coq.

This validates the central intuition: symbolic execution can prune an authoritative ISA model, and
the result should be consumed through a compositional program logic. It also shows why "just trace
the state monad" is not the end of the engineering problem. The trace must be simplified, memory
resources must be tracked, and proof search must avoid exploding.

Islaris is not a Lean library. Its foundational logic and automation are in Coq, its published
evaluation is mostly short systems examples, and the paper explicitly presents larger higher-layer
verification as future work. It is a strong reference design and potentially a useful parallel
prototype if the proof-assistant requirement is relaxed, but adopting it would no longer answer the
question "what is this like from scratch in Lean?"

### Lean

Lean is a viable choice. The necessary ingredients exist individually:

- executable Sail-generated Lean semantics;
- inductive relations, state monads, and bit vectors for the machine layer;
- metaprogramming for generating per-PC step equations;
- ordinary theorem proving for loop invariants and SHA-3 algebra;
- local evidence from `evm-asm` that bounded Hoare triples and a small separation logic can be
  implemented effectively in Lean.

What does not currently exist in this repository is an off-the-shelf Lean equivalent of the full
Islaris pipeline. Building the relevant subset is part of the experiment. The major engineering
question is whether a thin specialized layer is enough for this 312-instruction binary or whether
general symbolic-execution and framing automation becomes necessary.

### Other normal approaches

Binary verification commonly follows one of three paths:

1. reason directly over a detailed ISA semantics;
2. lift the binary to a simpler intermediate language and validate the translation;
3. prove source code and use a verified compiler or a binary-validation phase.

This project intentionally chooses the first path for its root of trust, but should borrow the
second path internally by deriving compact step equations or a validated small model. Proving the C
source and trusting GCC would answer a different question.

## 6. Side effects and the meaning of `main`

SHA-3 is mathematically pure, but its binary implementation is not. It reads an input region,
mutates a 200-byte state, uses stack memory and registers, writes an output region, and returns.
These effects are central to proving that the observed result is the mathematical digest. Purity is
recovered only after proving that the mutation is confined and projecting the output bytes.

At the internal `sha3` boundary, the environment is small: memory plus the RISC-V ABI. At `main`,
the environment additionally includes:

- `_start` stack layout and `argc`/`argv` construction;
- NUL-terminated message decoding;
- conversion of digest bytes to lowercase hexadecimal;
- `write` and `exit` syscall semantics, including short writes and failure;
- stdout, stderr, and exit status as observable behavior.

The current Sail ISA model does not by itself define Linux. Syscalls are platform behavior layered
on top of `ecall`. Consequently, proving `main` first adds many hypotheses or local semantics that
do not test SHA-3. It should be a later wrapper theorem.

If a program-level theorem for all byte arrays is desired, change the executable interface to a
total encoding such as hexadecimal or a length-delimited stdin protocol. Otherwise state the CLI
theorem only for NUL-free argument bytes and retain the all-`ByteArray` theorem at the internal
routine.

## 7. Recommended proof architecture

The following architecture keeps the root statement simple and localizes compiler-sensitive work.

### Layer A: fixed artifact

1. Embed or parse the exact SHA-3 ELF as proof data.
2. Prove its digest and parsed loadable segments by computation.
3. Define a deterministic user-mode loader and initial ABI state.
4. Prove that memory at each code address contains the ELF instruction bytes.

The current Nix metadata is useful input, but generated text files should not be trusted as axioms.
Their claims should be recomputed by Lean from the embedded artifact or checked by a small
proof-producing importer.

### Layer B: validated execution view

1. Decode every reachable instruction from the loaded bytes.
2. Generate one compact step theorem per PC or basic block.
3. Prove each theorem by reduction against the Sail-generated semantics, or prove a small RV64IM
   model simulates the specialized Sail model.
4. Give `ecall` separate platform rules rather than hiding it in ordinary instruction automation.

The specialized Sail generation currently includes source adaptations and an omitted-extension
fallback. Those changes must either be included explicitly in the trusted model choice or shown
equivalent to upstream Sail for all reachable execution. Specialization is reasonable, but it must
not silently change the semantics being claimed.

### Layer C: machine contracts

Define assertions for:

- register ownership and values;
- byte-range ownership and contents;
- installed immutable code;
- valid stack frames and return addresses;
- framed memory unchanged by a routine.

Use total-correctness contracts with explicit step bounds where practical. Step bounds make
termination concrete and make compositions easy to audit, though a well-founded termination
argument is also acceptable for input-dependent loops.

### Layer D: SHA-3 refinement

Work from the inside out:

1. prove a contract for one Keccak round;
2. prove the 24-round loop implements the Lean permutation;
3. prove absorption of one full rate block;
4. prove the input loop using a prefix invariant;
5. prove padding and final absorption;
6. prove extraction of 32 digest bytes;
7. compose these into the internal `sha3` contract.

The key loop invariant should relate concrete memory and registers to an abstract sponge state and
the consumed prefix of `msg`. This is where a hand-written Lean mirror of the C algorithm may help.
It should be introduced only if it gives a substantially simpler invariant than relating directly
to the imported spec's sponge state.

### Layer E: clean public execution theorem

Define `binary` as the fixed ELF artifact and define `RiscvSpec.execute` to load it, inject the
logical input at the internal `sha3` ABI boundary, execute it, and extract the digest or an explicit
error. Then prove:

```lean
theorem root_compliance :
    ∀ msg : ByteArray,
      RiscvSpec.execute binary msg = .ok (Sha3Spec.hashData msg)
```

Separately prove a wrapper theorem for the current CLI:

```lean
theorem cli_compliance
    (arg : ByteArray)
    (h_no_nul : 0 ∉ arg.data) :
    RiscvSpec.executeCli binary [arg] =
      { stdout := hex (Sha3Spec.hashData arg) ++ "\n",
        stderr := "",
        exitCode := 0 }
```

The exact Lean types can differ, but this split preserves the stupidly simple digest theorem
without pretending that `argv` represents arbitrary bytes.

## 8. Assessment of the current scaffold

The committed scaffold made several useful feasibility discoveries:

- the RISC-V Sail model can be generated as executable Lean under Nix;
- the SHA-3 spec and generated model can share a pinned Lean toolchain;
- a specialized RV64IM model is much smaller than the full generated target;
- the fixed `_start` opcode can be fetched, decoded, and executed to the expected `gp` and PC;
- the binary build emits stable artifact, entrypoint, segment, and symbol metadata.

It does not yet establish a binary-derived execution fact because the opcode in the closed theorem
is manually written into model memory. It also uses a proof-local fetch/decode/execute composition
that omits the privileged interrupt envelope. For a user-mode function proof this can be a sensible
abstraction, but it needs a theorem stating when that reduced step agrees with the selected Sail
step, or an explicit platform model whose assumptions are visible.

The next implementation milestone should therefore not be "execute more instructions." It should
be the artifact-to-code-memory lemma and the shape of one reusable function contract. Once those
interfaces are reviewed, a short basic block can test whether direct Sail step equations are usable
or whether the project should adopt a smaller validated machine model.

## 9. Expected robustness and cost

No proof tied to optimized machine code will be insensitive to compiler changes. The useful goal is
to localize the damage.

- A source or compiler change that preserves the binary requires no proof change.
- A binary change invalidates the artifact digest and decoded step equations immediately.
- Changed register allocation or instruction scheduling should affect low-level block proofs but not
  SHA-3 abstract lemmas or public theorem statements.
- Inlining or symbol elimination may change contract boundaries. Address/basic-block contracts are
  more robust than assuming source function symbols survive.
- A changed algorithm may invalidate loop invariants and refinement lemmas.
- A Sail or Lean upgrade may invalidate the model-generation and per-step validation layer while
  leaving higher contracts intact.

This localization is the main reason to introduce abstraction layers even in a proof-of-concept.
The desired maintenance experiment can then measure changed lines and re-proof time separately for
artifact import, symbolic traces, contracts, and algorithmic lemmas.

The present SHA-3 target is plausible but ambitious. Its 312 instructions are larger than the
RISC-V case studies reported in the original Islaris evaluation, and arbitrary input gives it
nontrivial loops. On the other hand, it has no concurrency, allocation, recursion, floating point,
or complicated data structures; its memory footprint and mathematical state are regular. It is a
better medium target than a decompressor for learning the proof architecture. DEFLATE is larger and
adds bitstream parsing, dynamic tables, variable control flow, and error states, so it is a useful
second validation target after the machinery works.

## 10. Derisking status

The plan is not fully derisked. A concrete execution spike substantially improves the evidence, but
it also exposes proof-engineering and theorem-statement risks that must be resolved before attempting
the SHA-3 refinement.

### What is now demonstrated

[`experiments/SailSha3Smoke.lean`](../experiments/SailSha3Smoke.lean) reads the actual Nix-built ELF,
loads its `PT_LOAD` bytes into the generated Sail memory, initializes an RV64 integer ABI call at the
internal `sha3` symbol, runs to a sentinel return address, and extracts the output buffer. The model
produced the expected digest for `abc`, the repository sample message, and a 200-byte message that
crosses the SHA3-256 rate boundary. The checked-in experiment uses the last case and executes 70,084
instructions.

This answers a narrow but important question: the generated Lean model is executable enough to run
the concrete integer-only SHA-3 path. The linked ELF uses only RV64I instructions plus `remw` from M;
it does not reach the floating-point, reservation, randomness, or terminal-operation placeholders in
the executable Sail support. The experiment must explicitly enable M in `misa`, initialize all
integer registers, install a writable/executable PMA region, and use bare address translation.

### What remains risky

1. **Artifact binding is not proved.** The experiment reads the ELF through `IO` and uses audited but
   hard-coded load offset, size, and symbol addresses. `binary` is still empty in the theorem. A Nix
   generator should emit the exact ELF as Lean data, after which Lean should compute the segment and
   entry bytes used by execution.
2. **Parametric proofs are not demonstrated.** Concrete `native_decide` and interpreted execution
   work. In contrast, exploratory symbolic lemmas for even `writeReg x3 v; readReg x3` and one
   `auipc` did not close by simplification. The generated dependent hash-map state and instrumentation
   callbacks remain in the goal. A dedicated monad/register/memory lemma library or a validated small
   RV64 model is required. The local `evm-asm` comparison contains roughly 3,000 lines in its Sail
   equivalence layer, which is evidence that this is real work rather than a missing tactic flag.
3. **The reduced step is not connected to the full model step.** Both the scaffold and smoke test use
   fetch/decode/execute/tick directly. They bypass interrupt dispatch, privileged trap handling, and
   other logic in `run_hart_active`/`try_step`. We need a theorem showing equivalence under explicit
   user-mode/no-interrupt assumptions, or a fully initialized platform execution using the official
   step.
4. **The root input domain is too broad.** Lean `ByteArray.size` is an unbounded `Nat`; an RV64 ABI
   has 64-bit `size_t` and addresses. There are byte arrays that cannot be represented in one RV64
   execution. The final theorem needs a representability bound, preferably expressed by quantifying
   over a transparent input subtype, unless `RiscvSpec.execute` is intentionally idealized beyond
   actual RV64 behavior.
5. **A total executable runner needs a proved fuel bound.** The smoke test uses a fixed 100,000-step
   budget. `RiscvSpec.execute` needs a computable bound derived from message length and a proof that it
   is sufficient, or the root statement must use a relational execution semantics instead of an
   executable function.
6. **The SHA-3 abstraction bridge is untested.** The selected Lean implementation exposes
   `hashData`, while most useful sponge internals are private. We have not yet shown that its
   definitions are convenient targets for binary loop invariants or whether a public logical mirror
   and a separate equivalence proof are needed.
7. **Model specialization needs validation.** The generated model applies source adaptations and an
   omitted-extension fallback. We must show the binary never depends on changed cases and that the
   reduced module selection preserves every instruction and memory behavior on the reachable path.

Before starting the full SHA-3 proof, four gates should pass:

1. agree on a representable-input root theorem;
2. prove one ELF-derived instruction theorem from embedded artifact bytes;
3. prove one genuinely symbolic basic-block contract, including register and memory framing;
4. connect the reduced user step to the selected authoritative Sail step.

Passing those gates would derisk the architecture. The 70,084-step concrete run shows that failure
to execute the binary is no longer the primary concern; scalable symbolic reasoning is.

## 11. Conclusions

The original plan has the right semantic core: execute the actual binary in a formal RISC-V model,
relate machine states to a pure Lean computation, and compose local results. The missing piece is
that local results should be expressed as contracts, not as ad hoc equalities of whole state-monad
terms.

For this project:

1. Keep Sail as the authoritative ISA semantics.
2. Derive a compact, validated execution view from the fixed ELF.
3. Use direct symbolic execution for blocks and induction for loops.
4. State routine correctness as total Hoare contracts.
5. Use a small separation logic or equivalent frame discipline for registers and memory.
6. Prove the internal `sha3` routine for all `ByteArray` inputs before proving CLI behavior.
7. Treat the imported Lean SHA-3 code as the selected executable reference, not yet a proved
   formalization of FIPS 202.

That path answers the educational question honestly: it exposes artifact identity, machine
semantics, symbolic execution, invariants, framing, refinement, and proof composition, while still
ending in a root theorem that a reader can understand without inspecting any of those layers.

## References

- NIST, [FIPS 202: SHA-3 Standard](https://doi.org/10.6028/NIST.FIPS.202), 2015.
- Gerald Doussot, [Cryptography Experiments in Lean 4: SHA-3
  Implementation](https://eprint.iacr.org/2024/1880), 2024.
- Michael Sammler et al., [Islaris: Verification of Machine Code Against Authoritative ISA
  Semantics](https://doi.org/10.1145/3519939.3523434), PLDI 2022.
- Michael Sammler et al., [Islaris artifact](https://github.com/rems-project/islaris).
- Michael Sammler et al., [RefinedC: Automating the Foundational Verification of C Code with
  Refined Ownership Types](https://plv.mpi-sws.org/refinedc/), PLDI 2021.
- Alasdair Armstrong et al., [Sail: a language for describing instruction-set
  architectures](https://doi.org/10.1145/3290384), POPL 2019.
- Local comparison implementation: [`evm-asm`](https://github.com/Verified-zkEVM/evm-asm),
  inspected at commit `a59d6ea5672dba114c21c0da4dd4952bac4b6b35`.
- Imported SHA-3 Lean implementation: [`gdncc/Cryptography`](https://github.com/gdncc/Cryptography),
  pinned at commit `883139dc0cd152a0f6f219b23aae35cbf6d67223`.
