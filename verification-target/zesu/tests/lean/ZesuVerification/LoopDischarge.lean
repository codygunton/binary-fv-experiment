import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry

/-!
# Angle 3: can a machine loop be discharged in this framework?

Test-only. Nothing here is imported by the root theorem; this module records what the trace
types can and cannot express about a loop, and what the generated exit inventory does to a loop.

Four things are established.

1. **`FunctionTrace`/`ScopedTrace` halt at an exit pc** (`functionTrace_stuck_at_exit`,
   `scopedTrace_stuck_at_exit`): if the machine is *at* an exit pc, the only trace from there is the
   empty one. `step`/`ownStep`/`inlineStep`/`callStep` each carry `¬ exit pc`, so this is not a
   convention but a property of the types. Consequence: an exit pc that the machine can *continue
   from inside the same instance* truncates every trace at that pc.

2. **The generated exit inventory truncates 97 of its 469 exit rows** (`truncating_rows_generated`),
   spread over 40 of the 141 instances — and **not one of them is an emitted instance**
   (`emitted_exits_are_all_sinks`). The consequence for loops is stated as a certificate per
   instance: for each of the nine looping *inlined* instances there is a closed set of ≤ 13
   addresses containing the entry from which no trace can escape, and the loop header is not in it
   (`looping_inlined_instances_cannot_reach_their_loop`). Those nine local obligations therefore have
   no trace that completes the loop at all.

3. **The trace types can nonetheless express a loop of input-dependent trip count, with no new
   constructor** (`ScopedTrace.loopDescend`, `FunctionTrace.loopDescend`). The iteration must be
   stated as a *continuation transformer* (`ConfinedPrefix`), not as a trace: a trace that stopped at
   the loop header would need the header to be an exit, and `EnteredFunctionTrace` then has no
   inhabitant (`no_loop_iteration_as_entered_trace`). Neither `FunctionTrace.append` nor
   `append_within` can stitch an iteration on, because both demand the enclosing exits be contained
   in the iteration's stopping set.

4. **A unit that is its own callee is inadmissible** (`functionGraphRanked_forbids_self_edge`): a
   self-edge makes `FunctionGraphRanked` false for *every* rank, not merely for the generated one. So a
   loop cannot be given to the composition engine as a self-recursive unit.
-/

namespace ZesuVerification.LoopDischarge

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.Zesu.Elflings.Generated (generatedProgram)

/-! ## 1. Both trace types halt at an exit pc -/

private theorem pc_eq {s : State} {a b : BitVec 64}
    (h1 : s.regs.get? PC = some a) (h2 : s.regs.get? PC = some b) : a = b :=
  Option.some.inj (h1.symm.trans h2)

/-- **A trace standing on an exit is the empty trace.** No step may be retired at an exit pc, so a
run that reaches one is finished whether or not the code continues there. -/
theorem functionTrace_stuck_at_exit {region exit : BitVec 64 → Prop} {fromStep count : Nat}
    {s s' : State} {pc : BitVec 64}
    (hpc : s.regs.get? PC = some pc) (hexit : exit pc)
    (h : FunctionTrace region exit fromStep count s s') : count = 0 ∧ s' = s := by
  cases h with
  | exitAt _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | step _ n p _ _ _ hp _ hnot _ _ =>
      exact absurd (by rw [pc_eq hp hpc]; exact hexit) hnot

/-- The same for the edge-aware trace: all three transition constructors carry `¬ exit pc`. -/
theorem scopedTrace_stuck_at_exit {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {fromStep count : Nat} {s s' : State} {pc : BitVec 64}
    (hpc : s.regs.get? PC = some pc) (hexit : exit pc)
    (h : ScopedTrace region exit childSummary fromStep count s s') : count = 0 ∧ s' = s := by
  cases h with
  | exitAt _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | ownStep _ n p _ _ _ hp _ hnot _ _ =>
      exact absurd (by rw [pc_eq hp hpc]; exact hexit) hnot
  | inlineStep _ used n _ _ _ _ _ _ _ htr _ =>
      exact absurd (by rw [pc_eq htr.atEntry hpc]; exact hexit) htr.entryNotExit
  | inlineCallStep _ childUsed calleeUsed n _ _ _ _ _ _ _ _ htr _ =>
      exact absurd (by rw [pc_eq htr.atEntry hpc]; exact hexit) htr.entryNotExit
  | callStep _ used n _ _ _ _ _ _ _ htr _ =>
      exact absurd (by rw [pc_eq htr.atCall hpc]; exact hexit) htr.callNotExit

/-! ## 2. What the generated exit inventory does to the loops

The union of all 141 edge arrays is the region CFG: the extractor files each edge on the *innermost*
frame owning its source, so no single instance's `edges` is its own CFG. -/

/-- All 3374 generated edges, as one array. -/
def allEdges : Array DirectEdge :=
  generatedProgram.functionInstances.foldl (fun acc i => acc ++ i.edges) #[]

theorem allEdges_size : allEdges.size = 3374 := by native_decide

/-- The successors of `pc` that lie inside `ranges`. -/
def regionSuccessors (ranges : Array BinaryFv.Binary.AddressRange) (pc : Nat) : Array Nat :=
  (allEdges.filter fun e => e.source == pc && Program.inRanges ranges e.target).map
    (fun e => e.target)

/-- An exit row is **truncating** when the machine can continue from it inside the very instance that
declares it. By `functionTrace_stuck_at_exit` every trace stops there, so everything downstream of
such a row is unreachable by any trace of that instance. -/
def truncatingExitRows (i : FunctionInstance) : Array Nat :=
  i.exitPcs.filter fun pc => !(regionSuccessors i.regions pc).isEmpty

def truncatingRowCount (program : Program) : Nat :=
  program.functionInstances.foldl (fun n i => n + (truncatingExitRows i).size) 0

def truncatingInstanceCount (program : Program) : Nat :=
  (program.functionInstances.filter fun i => !(truncatingExitRows i).isEmpty).size

/-- **97 of the 469 declared exit rows are truncating**, over **40** of the 141 instances. -/
theorem truncating_rows_generated : truncatingRowCount generatedProgram = 97 := by native_decide

theorem truncating_instances_generated : truncatingInstanceCount generatedProgram = 40 := by
  native_decide

/-- The emitted instances: those whose identity carries no inline stack. -/
def emittedInstances : Array FunctionInstance :=
  generatedProgram.functionInstances.filter fun i => i.id.inlineStack.isEmpty

theorem emittedInstances_size : emittedInstances.size = 14 := by native_decide

/-- **The check has both directions.** It rejects 97 rows on the real program, and accepts every row
of every *emitted* instance: no emitted instance's trace is truncated anywhere. This is the sense in
which collapsing to the 14 emitted functions repairs the defect rather than relocating it. -/
theorem emitted_exits_are_all_sinks :
    emittedInstances.all (fun i => (truncatingExitRows i).isEmpty) = true := by native_decide

/-- The same check against the address set the *local* obligation actually confines steps to
(`functionInstanceOwnPcs` = `Program.ownedRanges` = own regions plus absorbed excluded routines) and
against the *closed* obligation's execution extent. Both are supersets of `regions`, so this is the
direction that could have gone wrong: an emitted exit whose continuation is in the absorbed code or in
a callee would still truncate. Neither does. -/
def truncatingExitRowsIn (ranges : Array BinaryFv.Binary.AddressRange) (i : FunctionInstance) :
    Array Nat :=
  i.exitPcs.filter fun pc => !(regionSuccessors ranges pc).isEmpty

theorem emitted_exits_are_sinks_in_owned :
    emittedInstances.all
      (fun i => (truncatingExitRowsIn (Program.ownedRanges generatedProgram i) i).isEmpty)
      = true := by native_decide

theorem emitted_exits_are_sinks_in_extent :
    emittedInstances.all
      (fun i => (truncatingExitRowsIn (functionInstanceExecutionRanges generatedProgram i) i).isEmpty)
      = true := by native_decide

/-- And the truncating-row count only grows on the larger sets, so the 97 is a floor, not a ceiling. -/
theorem truncating_rows_owned :
    generatedProgram.functionInstances.foldl
      (fun n i => n + (truncatingExitRowsIn (Program.ownedRanges generatedProgram i) i).size) 0
      = 97 := by native_decide

/-! ### The nine looping inlined instances, certified unable to enter their loop

`liveClosed i live` says: `live` contains `i.entryPc`, and from every member of `live` that is not an
exit, every in-region successor is again in `live`. Any trace of `i` retires only addresses in such a
set, so an address outside it is unreachable by every trace. The sets below were computed as the
exact reachable-avoiding-exits sets; the check re-derives closure, so a wrong set fails here. -/
def liveClosed (i : FunctionInstance) (live : Array Nat) : Bool :=
  live.contains i.entryPc &&
    live.all fun pc =>
      i.exitPcs.contains pc ||
        (regionSuccessors i.regions pc).all fun t => live.contains t

/-- The loop headers of the six collection loops, as addresses. Measured on the region CFG: each of
the six loops is a single-entry SCC occupying exactly the contiguous address interval from its header
to its latch. -/
def collectionLoopHeaders : Array Nat := #[72120, 73620, 74292, 74888, 75336, 77672]

/-- For each of the nine inlined instances whose own region contains a loop: a closed live set, and
the loop headers it does **not** contain. Row shape: (instance index, live set, headers). -/
def loopUnreachableCertificates : Array (Nat × Array Nat × Array Nat) := #[
  (16, #[67084, 67088], #[72120, 73620, 74292, 74888, 75336]),
  (23, #[67352, 67356], #[72120]),
  (45, #[71012, 71016, 71020], #[72120]),
  (58, #[73444, 73448, 73452, 73456], #[73620]),
  (63, #[73716, 73720, 73724, 73728], #[74292, 74888, 75336]),
  (70, #[74072, 74076, 74080, 74084, 74088, 74092, 74096, 74100, 74104, 74108, 74112, 74116, 74120],
       #[74292]),
  (81, #[74656, 74660, 74664, 74668, 74672, 74676, 74680, 74684, 74688, 74692], #[74888]),
  (88, #[75072, 75076, 75080], #[75336]),
  (120, #[77500], #[77672])]

def certificateHolds (row : Nat × Array Nat × Array Nat) : Bool :=
  match generatedProgram.functionInstances[row.1]? with
  | none => false
  | some i =>
      liveClosed i row.2.1 &&
        row.2.2.all fun h => Program.inRanges i.regions h && !row.2.1.contains h

/-- **Nine local obligations admit no trace that reaches their loop.** For each, the entry sits in a
closed set of at most 13 addresses; every loop header inside that instance's own regions lies outside
it. So no `FunctionTrace`/`ScopedTrace` of that instance retires a single loop instruction. -/
theorem looping_inlined_instances_cannot_reach_their_loop :
    loopUnreachableCertificates.all certificateHolds = true := by native_decide

/-- Negative control for the certificate check: appending a loop header to a live set makes the
certificate fail, so `certificateHolds` is not vacuously true. -/
def certificateWithHeaderAdded (row : Nat × Array Nat × Array Nat) : Nat × Array Nat × Array Nat :=
  match row.2.2[0]? with
  | none => row
  | some h => (row.1, row.2.1.push h, row.2.2)

theorem certificate_check_can_fail :
    loopUnreachableCertificates.all
      (fun row => certificateHolds (certificateWithHeaderAdded row) == false) = true := by
  native_decide

/-- Second negative control: dropping the entry from a live set also fails. -/
theorem certificate_check_needs_the_entry :
    loopUnreachableCertificates.all
      (fun row => match generatedProgram.functionInstances[row.1]? with
        | none => false
        | some i => liveClosed i (row.2.1.filter fun pc => pc != i.entryPc) == false) = true := by
  native_decide

/-! ## 3. A loop *can* be discharged, with no change to the trace types

The obligation is existential in the step count (`LocallyImplements` asks for `∃ count s'`), and
`ScopedTrace` is an inductive least fixpoint whose transition constructors recurse. So a trace of
input-dependent length is built by ordinary Lean induction on the trip count. What cannot be done is
to state one iteration as a `FunctionTrace`: it would have to stop at the loop header, and an entered
trace whose stopping set contains its own entry has no inhabitant. -/

/-- **The naive per-iteration formulation is uninhabited.** Making the loop header the stopping set
contradicts `EnteredFunctionTrace.entryNotExit`. This is why the iteration is packaged as a
continuation transformer below and not as a trace. -/
theorem no_loop_iteration_as_entered_trace {region : BitVec 64 → Prop} {header : BitVec 64}
    {fromStep count : Nat} {s s' : State} :
    ¬ EnteredFunctionTrace region (fun pc => pc = header) header fromStep count s s' :=
  fun h => h.entryNotExit rfl

/-- A **confined prefix**: `len` retired steps that stay inside `own` and off every `exit`, expressed
by what they do to any continuation. This is the shape a loop iteration has to take. -/
def ConfinedPrefix (own exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (fromStep len : Nat) (s s' : State) : Prop :=
  ∀ (m : Nat) (t : State),
    ScopedTrace own exit childSummary (fromStep + len) m s' t →
      ScopedTrace own exit childSummary fromStep (len + m) s t

namespace ConfinedPrefix

variable {own exit : BitVec 64 → Prop}
  {cs : FunctionInstanceId → Nat → Nat → State → State → Prop}

theorem nil {a : Nat} {s : State} : ConfinedPrefix own exit cs a 0 s s := by
  intro m t h; simpa using h

/-- One retired owned, non-exit instruction is a length-1 prefix. -/
theorem one {a : Nat} {s s1 : State} (pc : BitVec 64)
    (hpc : s.regs.get? PC = some pc) (hregion : own pc) (hnotExit : ¬ exit pc)
    (hstep : Runs (try_step a false) s s1 false) :
    ConfinedPrefix own exit cs a 1 s s1 := by
  intro m t h
  have harith : 1 + m = m + 1 := Nat.add_comm 1 m
  rw [harith]
  exact ScopedTrace.ownStep a m pc s s1 t hpc hregion hnotExit hstep h

/-- A resolved call is a prefix of length `1 + used + 1`, so an iteration containing a call is still
a prefix — which matters here because every one of the six collection loops calls `memmove`. -/
theorem ofCall {a used : Nat} {s sResume : State} (site : CallSite)
    (program : Program) (caller callee : FunctionInstance)
    (htransfer : CallTransfer own exit cs site program caller callee a used s sResume) :
    ConfinedPrefix own exit cs a (1 + used + 1) s sResume := by
  intro m t h
  have hshift : a + (1 + used + 1) = a + 1 + used + 1 := by omega
  rw [hshift] at h
  exact ScopedTrace.callStep a used m site program caller callee s sResume t htransfer h

theorem trans {a n m : Nat} {s s1 s2 : State}
    (h1 : ConfinedPrefix own exit cs a n s s1)
    (h2 : ConfinedPrefix own exit cs (a + n) m s1 s2) :
    ConfinedPrefix own exit cs a (n + m) s s2 := by
  intro k t h
  have hshift : a + (n + m) = a + n + m := by omega
  have h' : ScopedTrace own exit cs (a + n + m) k s2 t := by rwa [hshift] at h
  have hcount : n + m + k = n + (m + k) := by omega
  rw [hcount]
  exact h1 (m + k) t (h2 k t h')

end ConfinedPrefix

/-- **Loop discharge by descending trip count.** If a loop invariant `Inv` advances by one
length-`L` confined prefix for every positive residual count, and the post-loop tail is a trace of at
most `E` steps ending in `Post`, then the whole loop is a `ScopedTrace` of at most `N * L + E` steps
ending in `Post` — for `N` given by the arguments, hence by the input size.

No constructor is added and no existing proof changes: this is derivable from `ownStep`/`callStep`
alone. The `count ≤ stepBound args` side of `LocallyImplements` becomes the arithmetic
`N * L + E ≤ stepBound args`. -/
theorem ScopedTrace.loopDescend {own exit : BitVec 64 → Prop}
    {cs : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {L E : Nat} {Inv : Nat → State → Prop} {Post : State → Prop}
    (adv : ∀ (k a : Nat) (s : State), Inv (k + 1) s →
      ∃ s', ConfinedPrefix own exit cs a L s s' ∧ Inv k s')
    (fin : ∀ (a : Nat) (s : State), Inv 0 s →
      ∃ (m : Nat) (t : State), m ≤ E ∧ ScopedTrace own exit cs a m s t ∧ Post t) :
    ∀ (N a : Nat) (s : State), Inv N s →
      ∃ (m : Nat) (t : State), m ≤ N * L + E ∧ ScopedTrace own exit cs a m s t ∧ Post t := by
  intro N
  induction N with
  | zero =>
      intro a s hInv
      obtain ⟨m, t, hb, ht, hp⟩ := fin a s hInv
      exact ⟨m, t, by omega, ht, hp⟩
  | succ k ih =>
      intro a s hInv
      obtain ⟨s', hpre, hk⟩ := adv k a s hInv
      obtain ⟨m, t, hb, ht, hp⟩ := ih (a + L) s' hk
      have hmul : (k + 1) * L = k * L + L := by
        simpa [Nat.succ_mul] using rfl
      exact ⟨L + m, t, by omega, hpre m t ht, hp⟩

/-- The same combinator for the flat trace, so a leaf like `memcpy` (9 instructions, 7 of them on its
byte loop) is covered without any splicing. -/
theorem FunctionTrace.loopDescend {region exit : BitVec 64 → Prop}
    {L E : Nat} {Inv : Nat → State → Prop} {Post : State → Prop}
    (adv : ∀ (k a : Nat) (s : State), Inv (k + 1) s →
      ∃ s', (∀ (m : Nat) (t : State), FunctionTrace region exit (a + L) m s' t →
        FunctionTrace region exit a (L + m) s t) ∧ Inv k s')
    (fin : ∀ (a : Nat) (s : State), Inv 0 s →
      ∃ (m : Nat) (t : State), m ≤ E ∧ FunctionTrace region exit a m s t ∧ Post t) :
    ∀ (N a : Nat) (s : State), Inv N s →
      ∃ (m : Nat) (t : State), m ≤ N * L + E ∧ FunctionTrace region exit a m s t ∧ Post t := by
  intro N
  induction N with
  | zero =>
      intro a s hInv
      obtain ⟨m, t, hb, ht, hp⟩ := fin a s hInv
      exact ⟨m, t, by omega, ht, hp⟩
  | succ k ih =>
      intro a s hInv
      obtain ⟨s', hpre, hk⟩ := adv k a s hInv
      obtain ⟨m, t, hb, ht, hp⟩ := ih (a + L) s' hk
      have hmul : (k + 1) * L = k * L + L := by simpa [Nat.succ_mul] using rfl
      exact ⟨L + m, t, by omega, hpre m t ht, hp⟩

/-! ## 4. A loop cannot be its own unit

`calleeFunctionInstances` is a filter of the program's instances by membership in
`children ++ externalCalls`, so an instance that names itself is its own callee and
`FunctionGraphRanked` asks for `rank i < rank i`. -/

/-- **A self-edge is inadmissible for every rank**, not merely absent from this program. So the
composition engine can never perform the loop induction itself: a synthetic "loop unit" that calls
itself back for the next iteration is rejected by `FunctionGraphRanked` whatever rank is supplied. -/
theorem functionGraphRanked_forbids_self_edge {program : Program} {rank : FunctionInstance → Nat}
    {i : FunctionInstance} (hmem : i ∈ program.functionInstances)
    (hself : i.id ∈ i.children ++ i.externalCalls) :
    ¬ FunctionGraphRanked program rank := by
  intro hranked
  have hcallee : i ∈ calleeFunctionInstances program i := by
    refine Array.mem_filter.mpr ⟨hmem, ?_⟩
    obtain ⟨j, hj, hget⟩ := Array.mem_iff_getElem.mp hself
    exact Array.any_eq_true.mpr ⟨j, hj, by rw [hget]; exact decide_eq_true rfl⟩
  exact absurd (hranked i hmem i hcallee) (Nat.lt_irrefl _)

/-- The generated program has no self-edge, so the rank it does carry is not evidence that self-edges
are tolerated — they are simply absent. -/
theorem generated_has_no_self_edge :
    generatedProgram.functionInstances.all
      (fun i => !(i.children ++ i.externalCalls).contains i.id) = true := by native_decide

/-! ## 5. Bounded unrolling: no loop in this program has an input-independent trip count

Recorded as data because it is a measurement, not a derivation: the eleven distinct machine loops,
with the stride in input bytes that one iteration consumes. Every stride is positive and every trip
count is `bytes / stride`, so no loop admits unrolling by a constant. -/

/-- (owner, header, latch, instructions on the cycle, bytes of input consumed per iteration). Counted
from the pinned image's disassembly. -/
def machineLoops : Array (String × Nat × Nat × Nat × Nat) := #[
  ("decodeWithdrawals",           72120, 72488, 93, 44),
  ("decodeVersionedHashes",       73620, 73660, 11, 32),
  ("decodeDepositRequests",       74292, 74612, 81, 192),
  ("decodeWithdrawalRequests",    74888, 75064, 45, 76),
  ("decodeConsolidationRequests", 75336, 75436, 26, 116),
  ("decodePublicKeys",            77672, 77708, 10, 65),
  ("decodeByteListList",          78868, 79028, 41, 4),
  ("requireCanonicalOffsets",     79672, 79696,  7, 8),
  ("memcpy",                      81596, 81624,  7, 1),
  ("memmove_forward",             81660, 81656,  6, 1),
  ("memmove_backward",            81696, 81692,  6, 1)]

theorem machineLoops_count : machineLoops.size = 11 := by native_decide

/-- Every loop's trip count scales with the input: no stride is zero. -/
theorem no_constant_trip_count :
    machineLoops.all (fun row => decide (0 < row.2.2.2.2)) = true := by native_decide

/-! ## 6. The step budget

`ScopedTrace.callStep` accounts `1 + used + 1`, so a callee's retired steps count against the
*caller's* `stepBound`. Every one of the six collection loops calls `memmove` in its body, and
`memmove` is byte-at-a-time. The arithmetic below is checked; its inputs are counted from the pinned
disassembly. -/

structure LoopBudget where
  name : String
  /-- The contract's `stepBound` slope, per collection element. -/
  boundPerElement : Nat
  /-- Retired pcs on one iteration path inside the owning instance (the `jalr` included, the callee's
  `ret` not). -/
  ownSteps : Nat
  /-- `memmove` call sites in the iteration body. -/
  calls : Nat
  /-- Bytes those calls copy, summed. -/
  copiedBytes : Nat
  /-- Input bytes one iteration consumes (the element stride). -/
  stride : Nat
deriving Repr

/-- Counted: element stride and `li a2,·` immediates read off the loop bodies. -/
def loopBudgets : Array LoopBudget := #[
  { name := "versionedHashes",        boundPerElement :=  64, ownSteps := 11, calls := 1,
    copiedBytes :=  32, stride :=  32 },
  { name := "withdrawals",           boundPerElement := 256, ownSteps := 93, calls := 1,
    copiedBytes :=  20, stride :=  44 },
  { name := "depositRequests",       boundPerElement := 512, ownSteps := 81, calls := 3,
    copiedBytes := 176, stride := 192 },
  { name := "withdrawalRequests",    boundPerElement := 256, ownSteps := 45, calls := 2,
    copiedBytes :=  68, stride :=  76 },
  { name := "consolidationRequests", boundPerElement := 256, ownSteps := 26, calls := 3,
    copiedBytes := 116, stride := 116 },
  { name := "publicKeys",            boundPerElement := 128, ownSteps := 10, calls := 1,
    copiedBytes :=  65, stride :=  65 }]

/-- What the machine actually retires per element: `memmove` costs at least `6 * n + 3` steps to copy
`n` bytes with distinct source and destination, plus one parent step to retire its `ret`. -/
def actualCostPerElement (b : LoopBudget) : Nat :=
  b.ownSteps + 4 * b.calls + 6 * b.copiedBytes

/-- What the caller can *prove* per element: the only quantitative fact a child summary carries is
`used ≤ stepBound args`, and `contractMemmove.stepBound = 64 + 16 * length`. -/
def provableCostPerElement (b : LoopBudget) : Nat :=
  b.ownSteps + 65 * b.calls + 16 * b.copiedBytes

/-- **Five of the six collection budgets are below the machine's actual per-element cost.** -/
theorem actual_cost_exceeds_budget :
    (loopBudgets.filter fun b => decide (b.boundPerElement < actualCostPerElement b)).size = 5 := by
  native_decide

/-- The one that fits, named so the check is not "everything fails". -/
theorem withdrawals_budget_fits :
    (loopBudgets.filter fun b =>
      decide (actualCostPerElement b ≤ b.boundPerElement)).map (fun b => b.name)
      = #["withdrawals"] := by native_decide

/-- **All six budgets are below what the framework's own child-summary interface permits proving.**
This half needs no assumption about `memmove`'s path: it is the bound the summary hands over. -/
theorem provable_cost_exceeds_every_budget :
    loopBudgets.all (fun b => decide (b.boundPerElement < provableCostPerElement b)) = true := by
  native_decide

/-- The collapsed unit's budget survives both routes. `contractDecodeRaw.stepBound` is
`16384 + 512 * bytes.size`, i.e. 512 steps per input byte; the worst loop costs 1115 provable steps
per 65 input bytes. Stated as the per-byte comparison. -/
theorem decodeRaw_budget_covers_every_loop :
    loopBudgets.all (fun b => decide (provableCostPerElement b ≤ 512 * b.stride)) = true := by
  native_decide

end ZesuVerification.LoopDischarge
