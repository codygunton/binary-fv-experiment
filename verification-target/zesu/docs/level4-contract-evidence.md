# Level 4 contract evidence

`tests/level4_contract_evidence.py` consumes the reviewed Level 4 inventory JSON rather than
reconstructing hierarchy selection. Its required boundary fields are `id`, `kind`, `qualified`,
`entryPc`, `instructionPcs`, `exits`, and `parent`; `functionInstanceIdentity` is retained whenever
the hierarchy has one. It accepts exactly 18 boundary occurrences from 15 qualified function
families, so the former four `readOffset` plus four specialized-decoder inventory is deliberately
rejected as stale.

For an accepted rich SSZ input and a rejected missing-schema mutation, the runner compares the pinned
execution-specs reference, executable Lean SSZ specification, and independently built host Zesu
formatter. It then traces the unchanged RV64 ELF under the existing QEMU observer and records each
boundary's entry, declared exit, executed owned instructions, and concrete stores. It mutates each
measured observation (entry, exit, instruction count) and requires the checker to reject it.

The report explicitly leaves optimized argument locations, result carriers, complete write/frame
conditions, caller-frame preservation, and universal step bounds unmeasured: the observer records
PCs and memory accesses, not the boundary's full register state or all executions. Those gaps must
be closed by a reviewed extraction/probe before a Lean contract states them. This finite evidence
helps admit contracts; it is not proof and is not imported by `root_compliance`.
