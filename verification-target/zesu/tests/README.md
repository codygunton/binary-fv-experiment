# Zesu tests

This directory contains tests tied to the concrete Zesu implementation and binary. The differential
and boundary tests compare the public decoder with the pinned Ethereum execution-specs reference and
the executable Lean SSZ specification. The remaining tests check output observability, deterministic
Elfling generation, relocation stability, and agreement between production objects and their DWARF
sidecars.

These tests try to falsify two concrete claims: that generated function-instance boundaries describe
the production binary, and that selected production executions return the expected values and errors.
Passing those finite tests does not prove either claim universally. The compliance argument itself is
the Lean refinement from `BinaryFv/Specs/SSZ` through Zesu's contracts to machine execution.

`elfling_program_test.py` checks that generated Lean names identify the source function,
specialization, and full inline call path, and that generation fails if two instances would receive
the same name.

`level4_contract_evidence.py` is the admission-evidence runner for the reviewed 18 Level 4 local
boundaries from 15 function families. It consumes the hierarchy stream's JSON inventory, compares
accepted and rejected inputs with execution-specs, executable Lean SSZ, and an independently built
source probe, then observes entry/exit PCs and writes in the unchanged RV64 ELF. Its report names
the argument/result/frame/universal-bound clauses the trace cannot measure; passing it is evidence,
not a proof premise. `level4_contract_evidence_test.py` rejects stale 4+4 inventory data and mutates
every currently measurable observation.

`lean/ZesuVerification/` contains Lean checks tied to the production binary. The occurrence checks
compare extracted instructions, call boundaries, and source bindings with committed execution
observations. The scaled checks attempt those tests for all 141 compiled function instances under
three deterministic inputs. They record which instances actually executed and which individual checks could be evaluated;
an unexecuted instance, exceeded step bound, or unavailable meaning comparison is reported as a gap
and never counted as a pass. Mutation probes alter representative execution-observation fields and
require the corresponding checker to reject them. These modules live in the dedicated
`ZesuVerificationTests` Lake library, outside the production `BinaryFv` theorem library.

## Examples of checked execution observations

- `ScaleOccurrenceCheck.gating_checks_hold` records that every covered function instance reaches its
  declared entry, follows declared control-flow edges and exits, respects the checked write classes,
  and is consistent with its allocation declaration.
- `ScaleOccurrenceCheck.step_bounds_hold_except_documented_gap` records that checked step bounds hold
  for every covered instance except `requireCanonicalOffsets`, whose bound depends on a caller-passed
  length absent from the captured interface.
- `ScaleOccurrenceCheck.uncovered_are_exactly_the_statically_dead` records coverage for 138 of 141
  instances and identifies the other three as statically unreachable in this executable.
- `BinaryOccurrenceCheck.present_meaning_agrees` checks one concrete semantic case: the bytes loaded by
  the production `decodeOptionalBlobSchedule` instance decode under the handwritten meaning to the
  observed fields `22`, `23`, and `24`.

These are checked regression facts about captured executions, not premises of the formal compliance
proof. Mutation theorems in the same modules demonstrate that representative corruptions are rejected.
