# Checks against production executions

These tools run the unchanged production Zesu ELF on deterministic test inputs. They test whether the
generated function-instance description agrees with those executions: whether execution reaches the
claimed entry, follows claimed control-flow edges, leaves at a declared exit, performs only the
classified writes and allocations, and returns the expected result for cases that have a meaning
checker. A failure disproves the proposed boundary or behavior claim. A pass establishes only that the
claim survived these particular executions; it is not a premise of the Lean compliance theorem.

There are two Nix entry points:

- `nix build .#ssz-binary-evidence` checks one focused vertical slice:
  `decodeOptionalBlobSchedule` and its three child instances, under present, absent, and malformed
  inputs. It checks observed values, errors, allocation events, entries, edges, and exits; runs
  negative mutations; and requires the regenerated observation record to match the committed file.
- `nix build .#ssz-scale-evidence` attempts the boundary checks across all 141 compiled
  function instances under the same inputs. It reports dynamic coverage separately from passing
  checks; instances or clauses that cannot be observed are explicit gaps, not successes.

The command names use “evidence” for these captured execution observations. They are evidence that a
proposed proof boundary describes the executions tested—not evidence of SSZ correctness. The required
CI workflow runs both commands. The manual `production-evidence-extended` job adds no third kind of
check: it runs the complete hermetic Lean build and these same two execution-checking builds together.

This directory is different from the machine-region and flame-graph tooling. The trace tools observe
particular executions through QEMU and GDB. `tools/generate_machine_regions.py` instead performs a
static analysis of the ELF, DWARF, and LLVM disassembly to propose the complete instruction graph,
ownership table, loop components, and proof-region data. Lean checks that static proposal against the
Sail-decoded ELF. The flame-graph viewer presents that static database for human review; it does not
capture an execution.

The implementation is split as follows:

- `qemu_trace_plugin.c`, `capture_trace.py`, and `gdb_capture.py` collect execution observations.
- `cfg_audit.py` and `evaluate_occurrence.py` evaluate a focused function instance.
- `scale_occurrences.py` evaluates the complete function-instance inventory, while
  `classify_uncovered.py` explains instances that did not execute.
- `generate_evidence.py` turns captured observations into Lean-readable checks and reports;
  `negative_tests.py` verifies that representative corruptions are rejected.
- `source_function_catalog.json` supplies the generated identity catalog used to match observations to
  compiled function instances.

`SCALE_COVERAGE.md` and `UNCOVERED_CLASSIFICATION.md` are committed summaries because the Nix build
regenerates and byte-compares them. That drift check makes the recorded observations reproducible; it
does not promote them into formal assumptions.
