# Repository instructions

These instructions apply repository-wide.

## Objective

- The final goal is to prove that the shipped Zesu `zesu_decode_raw` implementation conforms to the
  pinned Ethereum SSZ specification. State how local proof or tooling work advances that goal.
- Preserve useful earlier work, but do not retain a theorem, contract, or abstraction merely because
  it already exists. Reject or replace statements whose machine assumptions are false.

## Proof navigation

- `root_compliance` is the single public entry theorem for the compliance proof. Reserve the `root_`
  prefix for it: no theorem or definition in its transitive dependency tree may begin with `root_`.
  A reader searching for `root_compliance` must immediately find the unique top of the proof tree.
- Every conditional refinement level must expose a named edge that converts that level's assumptions
  into its parent's assumptions. The parent theorem must call that edge explicitly; do not leave the
  composition implicit in a bundle of hypotheses.
- Name refinement edges for the direction they establish, such as `exportedContracts_of_level1`.
  Keep logical premises distinct from bytecode-coverage obligations retained for later runtime proofs.

## Refinement strategy

- Work top-down from the exported program: state a conditional theorem over its immediate machine
  regions, prove the small regions, and further resolve only the large regions.
- At every level, select exactly the immediate calls in the reviewed call flamegraph for the function
  being resolved. Restate that function's contract in terms of contracts for those selected calls; do
  not substitute deeper descendants because their statements happen to be available. If the UI's
  hierarchy disagrees with the reviewed call relation, record and correct that discrepancy instead of
  silently changing the theorem's function set.
- Prove every selected function that calls no other selected function. Also prove the machine
  instructions owned by the parent but not owned by any selected child. A selected function that is
  too large to prove becomes the parent resolved at the next level.
- The theorem for each level must visibly consume every selected contract and derive the same
  meaningful parent contract. Keep that conditional parent result valid while deeper functions remain
  unproved; a list of unused contracts is not a refinement.
- Treat each resolution depth as a reviewable stacked change. Do not introduce a flat catalog of all
  discovered functions as though it were the proof architecture.
- Contracts describe actual optimized machine-code boundaries. Inlined source functions do not obey
  a source-level RISC-V function ABI; apply ABI assumptions only at genuine calls.
- Bind every semantic or ghost value used by a contract to registers or memory at that boundary.

## Contract admission

- Before investing in a proof, require three checks: structural correspondence to the production ELF,
  semantic review against source/specification, and empirical tests for every measurable clause.
- Use the production ELF for machine observations and an independently built source probe as an
  oracle. Add focused negative or mutation tests showing that each checker rejects relevant faults.
- Evidence guides admission but is not a proof. Record unmeasured clauses and failures explicitly.
- Use generated, source-derived Lean identifiers for function instances. Do not select proof objects
  through numeric catalog positions or string names.

## Compiler evidence

- Prefer LLVM outputs as the common source for symbols, call structure, inlining, and interfaces.
  Use disassembly and generated control-flow regions to check the final machine code.
- DWARF augments LLVM evidence with source identity and locations; it does not override instructions in
  the shipped binary.

## Documentation language

- Comments, docstrings, READMEs, plans, and status notes must use concrete project terms. Do not use
  generic jargon when the specific declaration, artifact, proof relationship, or machine-code region
  can be named.
- Introduce specialized terms with enough local context to identify what they mean here. For example,
  say “the theorem converting `Level1ContractAssumptions` into `ExportedContractAssumptions`” before
  calling it a “refinement edge,” and name the exact theorem meant by “root” or “parent.”
- Avoid context-free labels such as “foundation,” “admission,” “spine,” “layer,” “closure,” or
  “machinery.” If one is useful, accompany it with the concrete files, declarations, checks, or
  dependency relation it summarizes.
- Documentation should let a reader follow the proof and build artifacts without first learning an
  agent's private vocabulary.

## Loops

- Prove loops with an invariant or recursive theorem plus a decreasing measure or justified bound.
  Do not unroll a loop merely because observed test inputs make it short; runtime-dependent lengths are
  compatible with an inductive proof.

## Verification

- Use focused Lean targets and evidence tests while iterating. Run the full `lake build` at coherent
  checkpoints, before committing proof changes, and before claiming a completed chunk.
- Regenerate compiler-derived artifacts from the current branch. Shared worktree build artifacts may
  accelerate compilation, but stale generated inputs or `.olean` files are not evidence.
- Keep the generated flamegraph proof status current. Selected but unproved functions are red,
  selected functions under active proof are yellow, proved functions are green, and unselected
  functions are blue.

## Pull request descriptions

- Name every theorem or other statement proved by the PR and state what each proof establishes.
- Name every theorem, contract, assumption, or proof obligation weakened by the PR and describe the
  weakening precisely. This includes adding assumptions, narrowing inputs, weakening conclusions,
  replacing a proof with an axiom or placeholder, and reducing machine-code or specification coverage.
- If the PR proves no new statements or weakens none, say so explicitly. Do not make reviewers infer
  either fact from the diff.
