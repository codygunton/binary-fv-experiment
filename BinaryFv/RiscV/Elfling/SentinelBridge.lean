import BinaryFv.RiscV.Elfling.FunctionTrace
import BinaryFv.RiscV.Step.ControlFlow

/-!
# From a run confined to a function instance, to a run that ends at a sentinel

`FunctionTrace` and `TraceToSentinel` are the two ends of the machine-level proof and they do not
meet:

* a `FunctionTrace` stops **at** an exit pc — an address *inside* the binary, the one the generated
  exit inventory names;
* a `TraceToSentinel` stops **at** the sentinel — an address that is deliberately in no mapped range,
  so it can never be an exit pc of anything.

Nothing turns one into the other, and no amount of composing `FunctionTrace`s ever will: the
difference is not length, it is that one more instruction has to retire. The last instruction of the
function is a `ret`, and it is the *retirement of that `ret`* that moves the pc from the exit address
to whatever the link register holds. A caller that put the sentinel in `ra` therefore lands on the
sentinel, and only then does a `TraceToSentinel` exist.

This module is that bridge, and it is generic: no address, no register convention and no program is
named here. The three things the bridge cannot know are hypotheses.

## The three hypotheses, and why each one is genuinely needed

1. **The sentinel is not an address the run retires from.** `TraceToSentinel.step` carries
   `hne : v ≠ sentinel` at every retired pc, whereas `FunctionTrace.step` carries only
   `hregion : region pc`. So the run's addresses have to be known to miss the sentinel. Every
   retired pc of a `FunctionTrace` is in `region`, so `regionAvoidsSentinel` covers them —
   *except* the last one, which `FunctionTrace.exitAt` only knows to satisfy `exit`. Hence the
   second, separate hypothesis `exitAvoidsSentinel`. Both are discharged concretely by the target:
   the sentinel is chosen outside every mapped range, and every region and exit address is inside
   one. Neither can be discharged here.

2. **The final `ret` really retires, and really lands on the sentinel.** This is `ret` +
   `landed` below. `traceToSentinel_of_functionTrace` takes the landing as a hypothesis;
   `traceToSentinel_of_functionTrace_retiringTo` **derives** it from the `ret`'s own jump target, so
   the caller supplies the machine step and nothing else. That is the form to use with
   `tryStepRetRetires`, whose conclusion is exactly the shape it expects: the target there is
   `Sail.BitVec.update rs1Val 0 0#1`, the value read out of the link register with bit 0 cleared, so
   "`ra` holds the sentinel" becomes a visible equation rather than an assumption about the pc.

3. **The count goes up by exactly one.** The conclusion is a trace of length `count + 1`, never
   `count`. It is in the statement rather than hidden behind a `∃ n` because the runner's fuel
   premise is a strict inequality on that number: a caller that has `count ≤ bound` from a function
   instance contract owes `count + 1 ≤ bound`, and that obligation should be forced into view here
   rather than discovered when the fuel argument fails.

## What is deliberately *not* assumed

The bridge never takes "the machine reaches the sentinel" as a hypothesis in any form — that is the
conclusion. What it takes is one `Runs (try_step …)` fact about a single instruction, which is the
same currency every other step lemma in this layer trades in. `SentinelBridgeWitness` exhibits a
closed instance of the whole hypothesis set to show it is satisfiable at all.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/-- After the `try_step` postlude has ticked the pc and bumped `minstret`, the pc is the jump
target. This is what lets the bridge *derive* its landing condition from a control-flow retirement
instead of assuming it. -/
theorem tryStepControlFlowAfterRetired_pc (afterExec : State) (targetPC retired : BitVec 64) :
    (tryStepControlFlowAfterRetired afterExec targetPC retired).regs.get? PC = some targetPC := by
  have hne : (PC : Register) ≠ minstret := by decide
  have hframe :
      (tryStepControlFlowAfterRetired afterExec targetPC retired).regs.get? PC =
        (tryStepControlFlowAfterTick afterExec targetPC).regs.get? PC :=
    writeReg_read_unchanged (tryStepControlFlowAfterTick afterExec targetPC) minstret PC
      (Sail.BitVec.addInt retired 1) hne
  rw [hframe]
  change (afterExec.regs.insert PC targetPC).get? PC = some targetPC
  rw [Std.ExtDHashMap.get?_insert]
  simp

/--
**The bridge.** A run confined to `region` that stops on an exit, followed by one more retiring step
that leaves the pc at `sentinel`, is a `TraceToSentinel` of length `count + 1`.

The two avoidance hypotheses are what make the resulting trace's per-step invariant true; the extra
`Runs` is the `ret`; the `+ 1` is that `ret`'s own retirement.
-/
theorem traceToSentinel_of_functionTrace {region exit : BitVec 64 → Prop} {sentinel : BitVec 64}
    {fromStep count : Nat} {entry atExit final : State}
    (regionAvoidsSentinel : ∀ pc, region pc → pc ≠ sentinel)
    (exitAvoidsSentinel : ∀ pc, exit pc → pc ≠ sentinel)
    (run : FunctionTrace region exit fromStep count entry atExit)
    (ret : Runs (try_step (fromStep + count) false) atExit final false)
    (landed : final.regs.get? PC = some sentinel) :
    TraceToSentinel sentinel fromStep (count + 1) entry final := by
  induction run with
  | exitAt a s pc hpc hexit =>
      refine TraceToSentinel.step a 0 pc s final final hpc (exitAvoidsSentinel pc hexit) ?_ ?_
      · simpa using ret
      · exact TraceToSentinel.done (a + 1) final landed
  | step a n pc u u' u'' hpc hregion _ hstep _ ih =>
      refine TraceToSentinel.step a (n + 1) pc u u' final hpc (regionAvoidsSentinel pc hregion)
        hstep (ih ?_)
      have harith : a + (n + 1) = a + 1 + n := by omega
      rwa [harith] at ret

/--
The same bridge with the landing condition **discharged** rather than assumed: the last step is a
control-flow retirement whose jump target *is* the sentinel, and `tryStepControlFlowAfterRetired_pc`
turns that into the pc reading the bridge needs.

`ret` here is literally the conclusion of `tryStepRetRetires`, so a proved `ret` retirement plugs in
with no reshaping. Instantiating `targetPC := Sail.BitVec.update rs1Val 0 0#1` is what makes "`ra`
held the sentinel" the load-bearing fact.
-/
theorem traceToSentinel_of_functionTrace_retiringTo {region exit : BitVec 64 → Prop}
    {sentinel retired : BitVec 64} {fromStep count : Nat} {entry atExit afterExec : State}
    (regionAvoidsSentinel : ∀ pc, region pc → pc ≠ sentinel)
    (exitAvoidsSentinel : ∀ pc, exit pc → pc ≠ sentinel)
    (run : FunctionTrace region exit fromStep count entry atExit)
    (ret : Runs (try_step (fromStep + count) false) atExit
      (tryStepControlFlowAfterRetired afterExec sentinel retired) false) :
    TraceToSentinel sentinel fromStep (count + 1) entry
      (tryStepControlFlowAfterRetired afterExec sentinel retired) :=
  traceToSentinel_of_functionTrace regionAvoidsSentinel exitAvoidsSentinel run ret
    (tryStepControlFlowAfterRetired_pc afterExec sentinel retired)

/--
The bridge for a **`ret` to the link register**, which is the shape the last instruction of a
compiled function actually has.

`tryStepRetRetires` retires `jalr x0, 0(rs1)` to `Sail.BitVec.update rs1Val 0 0#1` — the value read
out of `rs1` with bit 0 cleared, as the ISA specifies. So `linkIsSentinel` says exactly *the link
register held the sentinel* (for a sentinel with bit 0 clear, which any instruction address has),
and it is the only target-specific fact this form needs beyond the two avoidance conditions.

The caller's obligation is therefore reduced to what it should be: prove the `ret` retires, and
prove `ra` held the sentinel. Neither is something a generic layer can know, and neither is the
conclusion.
-/
theorem traceToSentinel_of_functionTrace_ret {region exit : BitVec 64 → Prop}
    {sentinel rs1Val retired : BitVec 64} {fromStep count : Nat} {entry atExit afterExec : State}
    (regionAvoidsSentinel : ∀ pc, region pc → pc ≠ sentinel)
    (exitAvoidsSentinel : ∀ pc, exit pc → pc ≠ sentinel)
    (run : FunctionTrace region exit fromStep count entry atExit)
    (linkIsSentinel : Sail.BitVec.update rs1Val 0 0#1 = sentinel)
    (ret : Runs (try_step (fromStep + count) false) atExit
      (tryStepControlFlowAfterRetired afterExec (Sail.BitVec.update rs1Val 0 0#1) retired) false) :
    TraceToSentinel sentinel fromStep (count + 1) entry
      (tryStepControlFlowAfterRetired afterExec (Sail.BitVec.update rs1Val 0 0#1) retired) :=
  traceToSentinel_of_functionTrace regionAvoidsSentinel exitAvoidsSentinel run ret
    (linkIsSentinel ▸ tryStepControlFlowAfterRetired_pc afterExec
      (Sail.BitVec.update rs1Val 0 0#1) retired)

/--
The `EnteredFunctionTrace` form, which is the one a contract actually produces.

Stated separately because entering buys something the bare form cannot: the run retired at least one
instruction *inside* the function, so the sentinel trace has length at least two. A degenerate
"already at an exit, do the `ret`" run cannot masquerade as an execution of the function.
-/
theorem traceToSentinel_of_enteredFunctionTrace {region exit : BitVec 64 → Prop}
    {sentinel entryPc : BitVec 64} {fromStep count : Nat} {entry atExit final : State}
    (regionAvoidsSentinel : ∀ pc, region pc → pc ≠ sentinel)
    (exitAvoidsSentinel : ∀ pc, exit pc → pc ≠ sentinel)
    (run : EnteredFunctionTrace region exit entryPc fromStep count entry atExit)
    (ret : Runs (try_step (fromStep + count) false) atExit final false)
    (landed : final.regs.get? PC = some sentinel) :
    TraceToSentinel sentinel fromStep (count + 1) entry final ∧ 2 ≤ count + 1 :=
  ⟨traceToSentinel_of_functionTrace regionAvoidsSentinel exitAvoidsSentinel run.trace ret landed,
    by have := run.count_pos; omega⟩

end BinaryFv.RiscV.Elfling
