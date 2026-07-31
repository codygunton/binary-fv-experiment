import BinaryFv.Zesu.Elflings.GeneratedProgramInstructions
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.RiscV.Proof.ImageFetch
import GeneratedProgram

/-!
# The exit instruction, decoded

`CodeIntact` pins the *bytes* of the loaded code, and `GeneratedProgramInstructions` decodes every
word of every generated region and checks it legal. Neither says what the instruction *at an exit*
is, and the sentinel bridge needs exactly that: `tryStepRetRetires` wants four fetched bytes at the
exit pc together with a `Runs (ext_decode …) … (.JALR (0#12, rs1, zreg))`, i.e. `jalr x0, 0(rs1)`.
Nothing in the tree produced that decode for any exit address. This module does.

## An exit pc is usually *not* a `ret`

The natural-sounding fact — "for every generated function instance, the word at each of its exit pcs
decodes to `ret`" — is **false on this artifact**, and it is worth stating why rather than weakening
it silently. `tools/generate_elfling_program.py` defines an exit as a pc whose control leaves the
function instance's regions: a return/terminal, or a *continuation* outside the regions. So the exit
inventory also contains tail calls, branches whose taken edge leaves the regions, and the last
instruction of a fragment that simply falls through into the next one — arithmetic, loads and stores
among them. Of the 469 exit rows across the 141 function instances, **16** are returns. 128 of the
141 function instances have no return exit at all, so for them the sentinel bridge is not applicable
in the first place.

### What changed since this module was written, and why

This module was first written against an exit rule that counted a resolved call's **callee** edge as
a way of leaving the caller, so *every* call site was an exit: 642 rows, 180 of them calls. That rule
contradicted `FunctionInstance.exitPcs`' own docstring — "returns and **tail-calls** that leave this
function instance" — and it made the conditional root theorem **vacuous**. `FunctionTrace.step`
carries `hnotExit : ¬ exit pc`, so a trace must halt at the first exit it reaches; `zesu_decode_raw`'s
trace therefore halted at its call to `decodeRaw` (`0x1031c`), where `status` and `storedResult` are
still unwritten and `postZesuDecodeRaw` is false. Any contract using that extent was consequently
unsatisfiable. `CallTransfer.callNotExit` also failed at all 180 call rows, leaving
`ScopedTrace.callStep` dead code against this artifact.

The generator now tests a resolved call's **fall-through** instead: control comes back from a call, so
a call site leaves its caller only in tail position. 642 exit rows became **469** — the 173 non-tail
call rows dropped, the 7 tail-position ones kept. The 16 returns are untouched: the rule never
concerned returns, which is why every count in this module about *returns* is unchanged and only the
totals moved. `zesu_decode_raw` went from six exits to **one, its `ret` at `0x10378`**, recorded below
as `entry_function_instance_exit_is_its_return` — so "the entry run ends at its return" is now a
definite description read off the data, with no contract clause supplying it.

The narrowing is checked from both sides. `GeneratedProgramCfg.leavesFunctionInstance` mirrors the new
rule and `exitsValid` re-decides both inclusions against the Sail-decoded CFG; and, because trading
vacuity for unprovability would be no better,
`GeneratedProgramCfg.generated_every_function_instance_reaches_an_exit` checks that all 141 instances
can still reach a declared exit, with the naive "drop every call exit" rule run as a mutant that
strands the `readArray` instance at `0x10fbc`.

What *is* true, and is what the bridge needs, is the conditional form: **an exit the decoded CFG
classifies as a return is a `ret` through `ra`**, encoded exactly `0x00008067`. The classification is
not this module's choice — `DecodedWord.controlTransfer` derives it from the Sail decode of the
pinned image — so this is a constraint on the artifact, not a definition dressed as one.

## The three checks, and what each can detect

* `returnExitsAreRetB` — every listed exit has a decoded node at exactly that address, and every one
  the CFG calls a return carries the word `ret`. Its falsifiable content is the *register*: a
  `.return_` through anything but `ra` fails it. That is not hypothetical — the pinned image contains
  six `jr t1` return sites in the runtime, and `adding_non_ra_return_exit_breaks_check` puts one into
  an exit list and watches the check reject it. It is `.all` over the exit rows, so it is monotone
  under removal and cannot notice a *missing* exit.
* `returnSitesListedAsExitsB` — the reverse inclusion, which is where removal is caught: every
  decoded return site lying inside a function instance's regions is listed among its exits. Deleting
  a return exit falsifies it, for every one of the 16;
  `dropping_any_return_exit_breaks_reverse_inclusion` decides all 16 deletions.
* `generatedReturnExitPcs.size = 16` — a set-level count over a `filter` of the decoded CFG, so it
  moves if the artifact's return inventory does.

Set-completeness of the *node array* is, as everywhere in this layer, inherited from image pinning
rather than asserted: `controlFlow?` is `decodedWords?.map controlFlowNodes`, derived by decoding the
pinned image, so "a node went missing" is not a failure the artifact can exhibit. What is a genuine
per-artifact table, and is therefore mutation-tested here, is `exitPcs`.
-/

namespace BinaryFv.Zesu.Elflings.Validation

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.Zesu.ControlFlow
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.Zesu.Elflings.Generated (generatedProgram)

/-! ## `ret`, as a word and as a decode -/

/-- The RV64 encoding of `ret`, i.e. `jalr x0, 0(ra)`. -/
def retEncoding : BitVec 32 := 0x00008067#32

/-- **`ret` decodes to the instruction the step lemma wants.** Run through the authoritative
generated Sail decoder, `0x00008067` is `.JALR (0#12, ra, zreg)` — literally the shape
`tryStepRetRetires` takes as its `decode` premise, with `rs1 := ra`.

The two register premises are the ones `ext_decode` genuinely reads (the privilege and `mseccfg`
gates behind `currentlyEnabled`); dropping either leaves the decode stuck, so they are not
decoration. -/
theorem ret_decode_run (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode retEncoding) state state (.JALR (0#12, .Regidx 1#5, zreg)) := by
  unfold retEncoding
  decode_run

/-! ## The decoded return sites -/

/-- The addresses the decoded CFG classifies as returns. A `filter`, so it tracks the artifact rather
than a maintained list. -/
def returnSitePcs (nodes : Array ControlFlowNode) : Array Nat :=
  (nodes.filter (fun n => n.returnSite)).map (fun n => n.word.encoded.address)

/-- The exit pcs of one function instance at which the decoded CFG says control returns. -/
def returnExitPcs (nodes : Array ControlFlowNode) (functionInstance : FunctionInstance) :
    Array Nat :=
  functionInstance.exitPcs.filter fun pc =>
    match ControlFlowNodeAt? nodes pc with
    | some node => node.returnSite
    | none => false

/-! ## Check 1: a listed exit that returns is `ret` through `ra` -/

/-- Every listed exit pc decodes to a node at exactly that address and fits a machine word; and every
one the CFG calls a return carries `retEncoding`, both as the CFG saw it and as the *file-backed*
image reads it back. The file-backed read is deliberate: it is the currency `CodeIntact`
(`fileBytesMatchMemory`) preserves, so this composes with a running machine without a second
image-agreement argument. -/
def returnExitsAreRetB (nodes : Array ControlFlowNode) (image : ProgramImage) (program : Program) :
    Bool :=
  program.functionInstances.all fun functionInstance =>
    functionInstance.exitPcs.all fun pc =>
      decide (pc < 2 ^ 64) &&
        (match ControlFlowNodeAt? nodes pc with
         | some node =>
             !node.returnSite ||
               (node.word.encoded.bits == retEncoding &&
                 image.readFileU32LE? pc == some retEncoding.toNat)
         | none => false)

/-- The per-exit fact extracted from the aggregate `Bool`. Generic in `image`, so instantiating at
`Artifacts.programImage` leaves the read symbolic. -/
theorem returnExitsAreRetB_elim {nodes : Array ControlFlowNode} {image : ProgramImage}
    {program : Program} (h : returnExitsAreRetB nodes image program = true)
    {functionInstance : FunctionInstance}
    (hFunctionInstance : functionInstance ∈ program.functionInstances)
    {pc : Nat} (hpc : pc ∈ functionInstance.exitPcs)
    {node : ControlFlowNode} (hnode : ControlFlowNodeAt? nodes pc = some node)
    (hret : node.returnSite = true) :
    pc < 2 ^ 64 ∧ node.word.encoded.bits = retEncoding ∧
      image.ownsFileEncodedWord { address := pc, bits := retEncoding } := by
  have hrow := forall_mem_of_all (forall_mem_of_all h functionInstance hFunctionInstance) pc hpc
  rw [Bool.and_eq_true] at hrow
  obtain ⟨hfits, hbody⟩ := hrow
  rw [hnode] at hbody
  simp only [hret, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hbody
  exact ⟨of_decide_eq_true hfits, hbody.1, hbody.2⟩

theorem returnExitsAreRet_check :
    ∀ nodes, controlFlow? = some nodes →
      returnExitsAreRetB nodes Artifacts.programImage generatedProgram = true := by
  intro nodes hn
  have : (controlFlow?.map
      (fun ns => returnExitsAreRetB ns Artifacts.programImage generatedProgram)).getD false = true := by
    native_decide
  rw [hn] at this; simpa using this

/-! ## Check 2: no return is omitted from the exit inventory -/

/-- Every decoded return site inside a function instance's regions is listed among its exits. This is
the reverse inclusion, and it is the removal-sensitive half: deleting a return exit falsifies it. -/
def returnSitesListedAsExitsB (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.functionInstances.all fun functionInstance =>
    (returnSitePcs nodes).all fun pc =>
      !Program.inRanges functionInstance.regions pc || functionInstance.exitPcs.contains pc

theorem returnSitesListedAsExits_check :
    ∀ nodes, controlFlow? = some nodes → returnSitesListedAsExitsB nodes generatedProgram = true := by
  intro nodes hn
  have : (controlFlow?.map (fun ns => returnSitesListedAsExitsB ns generatedProgram)).getD false
      = true := by native_decide
  rw [hn] at this; simpa using this

/-- **No return instruction inside a function instance's code escapes its exit inventory.** The
statement the check earns: a `ret` the function instance owns is an exit it declares, so a trace
cannot run past a return the inventory forgot to mention. -/
theorem generated_returns_are_declared_exits :
    ∀ nodes, controlFlow? = some nodes →
      ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ pc ∈ returnSitePcs nodes,
        Program.inRanges functionInstance.regions pc = true →
          functionInstance.exitPcs.contains pc = true := by
  intro nodes hn functionInstance hFunctionInstance pc hpc hin
  have hrow := forall_mem_of_all
    (forall_mem_of_all (returnSitesListedAsExits_check nodes hn) functionInstance hFunctionInstance)
    pc hpc
  simpa [hin] using hrow

/-! ## The inventory as data -/

/-- The decoded return sites that lie inside some function instance's code: the pcs at which a
generated function instance can actually return. Computed from the CFG and the generated regions,
never listed. -/
def generatedReturnExitPcs : Array Nat :=
  (controlFlow?.map fun nodes =>
    (returnSitePcs nodes).filter fun pc =>
      generatedProgram.functionInstances.any fun functionInstance =>
        Program.inRanges functionInstance.regions pc).getD #[]

/-- **Sixteen.** A set-level count over a `filter`, so it moves if the artifact's return inventory
does — unlike the per-row checks above, which are blind to removal. -/
theorem generatedReturnExitPcs_size : generatedReturnExitPcs.size = 16 := by native_decide

/-- Total declared exit rows across the 141 function instances. Recorded so that the docstring's
claim — most exits are not returns — is a checked number rather than an assertion: 469 rows, 16 of
them returns. It was 642 before the generator's exit rule stopped counting a resolved call's callee
edge as a way of leaving the caller. -/
def totalExitRows (program : Program) : Nat :=
  program.functionInstances.foldl (fun n functionInstance => n + functionInstance.exitPcs.size) 0

theorem totalExitRows_generated : totalExitRows generatedProgram = 469 := by native_decide

/-- Only 13 of the 141 function instances declare a return exit at all; for the other 128 the
sentinel bridge has nothing to attach to, because the machine never leaves them by a `ret`. -/
theorem function_instances_with_return_exits :
    ∀ nodes, controlFlow? = some nodes →
      (generatedProgram.functionInstances.filter
        fun functionInstance => !(returnExitPcs nodes functionInstance).isEmpty).size = 13 := by
  intro nodes hn
  have : (controlFlow?.map fun ns => (generatedProgram.functionInstances.filter
      fun functionInstance => !(returnExitPcs ns functionInstance).isEmpty).size).getD 0 = 13 := by
    native_decide
  rw [hn] at this; simpa using this

/-- The entry function instance is present, so the theorem below is not a statement about nothing. -/
theorem entry_function_instance_found :
    (Program.find? generatedProgram generatedProgram.entry).isSome = true := by native_decide

/-- The entry function instance returns from exactly one place. This is the exit the top-level
sentinel trace ends at, so "the run returned" is a definite description rather than a choice among
exits. -/
theorem entry_function_instance_has_one_return_exit :
    ∀ nodes, controlFlow? = some nodes →
      ∀ entry, Program.find? generatedProgram generatedProgram.entry = some entry →
        (returnExitPcs nodes entry).size = 1 := by
  intro nodes hn entry he
  have : (controlFlow?.map fun ns =>
      ((Program.find? generatedProgram generatedProgram.entry).map
        (fun e => (returnExitPcs ns e).size)).getD 0).getD 0 = 1 := by native_decide
  rw [hn, he] at this; simpa using this

/-- **`zesu_decode_raw` has exactly one exit, and it is its `ret`.** Strictly stronger than the
theorem above, which left open whether the entry had *other*, non-return exits — it had five, and a
`FunctionTrace` had to stop at whichever came first, which for the entry was the call at `0x1031c`.
Now the entry's whole exit inventory is the singleton `#[0x10378]` and every element of it is a
decoded return site, so "the entry trace ends at the entry's return" is forced by the artifact:
`FunctionTrace` halts at an exit, there is only one, and `returnExit_fetch_and_decode` reads a
`jalr x0, 0(ra)` there. The literal is load-bearing on purpose — a moved exit fails here rather than
silently re-describing which instruction the top-level run ends on. -/
theorem entry_function_instance_exit_is_its_return :
    ∀ nodes, controlFlow? = some nodes →
      ∀ entry, Program.find? generatedProgram generatedProgram.entry = some entry →
        entry.exitPcs = #[0x10378] ∧ returnExitPcs nodes entry = entry.exitPcs := by
  intro nodes hn entry he
  have h : (controlFlow?.map fun ns =>
      ((Program.find? generatedProgram generatedProgram.entry).map
        (fun e => (e.exitPcs == #[0x10378]) && (returnExitPcs ns e == e.exitPcs))).getD
        false).getD false = true := by native_decide
  rw [hn, he] at h
  simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-! ## What the assembly consumes

The two premises `tryStepRetRetires` needs about the *code* at the exit, produced together from one
`CodeIntact`-style memory agreement. Everything else it wants — the platform, the interrupt state,
the link read, the counters — is about registers, not about which instruction is there, and is not
this module's business. -/

/-- **The exit instruction is fetched and decoded.** At a generated exit the CFG classifies as a
return, a machine whose memory agrees with the pinned image's *file bytes* fetches four bytes that
decode, through the generated Sail decoder, to `jalr x0, 0(ra)`.

`fileBytesMatchMemory` rather than `matchesMemory` on purpose: that is exactly
`DecoderEnvironment.CodeIntact`, the clause every contract in this target already carries, so a
caller spends a fact it has instead of proving a new one. -/
theorem returnExit_fetch_and_decode {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes)
    {functionInstance : FunctionInstance}
    (hFunctionInstance : functionInstance ∈ generatedProgram.functionInstances)
    {pc : Nat} (hpc : pc ∈ functionInstance.exitPcs)
    {node : ControlFlowNode} (hnode : ControlFlowNodeAt? nodes pc = some node)
    (hret : node.returnSite = true)
    (state : State) (intact : Artifacts.programImage.fileBytesMatchMemory state.mem)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    ∃ byte0 byte1 byte2 byte3 : UInt8,
      FetchBytesAt state (BitVec.ofNat 64 pc)
        (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ∧
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
          (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
        state state (.JALR (0#12, .Regidx 1#5, zreg)) := by
  obtain ⟨hfits, _, howns⟩ :=
    returnExitsAreRetB_elim (returnExitsAreRet_check nodes hn) hFunctionInstance hpc hnode hret
  obtain ⟨byte0, byte1, byte2, byte3, hfetch, hword⟩ :=
    ProgramImage.fetchBytesAt_of_ownedFileEncodedWord Artifacts.programImage state
      { address := pc, bits := retEncoding } hfits intact howns
  refine ⟨byte0, byte1, byte2, byte3, hfetch, ?_⟩
  rw [hword]
  exact ret_decode_run state privilege mseccfgBits mseccfg

/-! ## Mutation tests

`native_decide`d `= true` facts about the real data say nothing about a predicate's power, so both
checks are mutated here and the mutants are required to fail. The mutation targets are chosen from
the data, never written down: an unfalsifiable literal proves as easily over-large as correct. -/

/-- The generated program with the exit `a` deleted from every function instance's inventory. -/
def programWithoutExit (a : Nat) : Program :=
  { generatedProgram with
    functionInstances := generatedProgram.functionInstances.map fun functionInstance =>
      { functionInstance with exitPcs := functionInstance.exitPcs.filter fun pc => pc != a } }

/-- **The deletions are real.** Every one of the 16 removes at least one row — stated so that a
future change producing the original program would fail here rather than turn the theorem below into
a check of nothing. -/
theorem programWithoutExit_shrinks :
    generatedReturnExitPcs.all
      (fun a => decide (totalExitRows (programWithoutExit a) < totalExitRows generatedProgram))
      = true := by native_decide

/-- **Dropping any return exit breaks the reverse inclusion.** All 16 deletions, decided. This is the
mutation the per-row checks structurally cannot catch, and the reason
`returnSitesListedAsExitsB` exists. -/
theorem dropping_any_return_exit_breaks_reverse_inclusion :
    generatedReturnExitPcs.all
      (fun a => (controlFlow?.map fun nodes =>
        returnSitesListedAsExitsB nodes (programWithoutExit a)).getD true == false) = true := by
  native_decide

/-- Decoded return sites whose word is **not** `ret` through `ra`. The pinned image has some: `jr t1`
tails in the runtime, outside every function instance's regions. They are what gives
`returnExitsAreRetB` something to reject. -/
def nonRaReturnSitePcs : Array Nat :=
  (controlFlow?.map fun nodes =>
    (nodes.filter fun n => n.returnSite && n.word.encoded.bits != retEncoding).map
      fun n => n.word.encoded.address).getD #[]

/-- **The rejection target exists, and is not one of the declared exits.** Six `jr t1` return sites,
none of them inside any function instance's code — which is why the real inventory passes. -/
theorem nonRaReturnSitePcs_size : nonRaReturnSitePcs.size = 6 := by native_decide

theorem nonRaReturnSitePcs_undeclared :
    nonRaReturnSitePcs.all
      (fun a => generatedProgram.functionInstances.all
        fun functionInstance => !functionInstance.exitPcs.contains a) = true := by native_decide

/-- The generated program with `a` appended to every function instance's exit inventory. -/
def programWithExtraExit (a : Nat) : Program :=
  { generatedProgram with
    functionInstances := generatedProgram.functionInstances.map fun functionInstance =>
      { functionInstance with exitPcs := functionInstance.exitPcs.push a } }

/-- **Declaring a return that is not a `ret` through `ra` breaks the check.** All six, decided. So
`returnExitsAreRetB`'s content is the register, not merely "an exit exists here". -/
theorem adding_non_ra_return_exit_breaks_check :
    nonRaReturnSitePcs.all
      (fun a => (controlFlow?.map fun nodes =>
        returnExitsAreRetB nodes Artifacts.programImage (programWithExtraExit a)).getD true == false)
      = true := by native_decide

/-! ### The scope of the check, stated rather than implied

A check that rejects everything is as uninformative as one that rejects nothing, so the complement is
recorded too: adding a decoded **non**-return pc to every exit inventory leaves `returnExitsAreRetB`
satisfied. It constrains returns; it does not claim the exit inventory contains only returns — which
it must not, since 453 of the 469 exit rows are tail calls, branches and fall-throughs. -/

/-- A decoded pc that is not a return site, taken from the CFG rather than written down. -/
def someNonReturnPc : Nat :=
  (controlFlow?.bind fun nodes =>
    ((nodes.filter fun n => !n.returnSite).map fun n => n.word.encoded.address)[0]?).getD 0

theorem someNonReturnPc_is_decoded_non_return :
    (controlFlow?.map fun nodes =>
      match ControlFlowNodeAt? nodes someNonReturnPc with
      | some node => !node.returnSite
      | none => false).getD false = true := by native_decide

/-- Adding a non-return exit does **not** break the check: its content is conditional on the CFG
calling the pc a return. -/
theorem adding_non_return_exit_does_not_break_check :
    (controlFlow?.map fun nodes =>
      returnExitsAreRetB nodes Artifacts.programImage (programWithExtraExit someNonReturnPc)).getD
      false = true := by native_decide

end BinaryFv.Zesu.Elflings.Validation
