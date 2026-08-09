# Level 4 contract evidence

`tests/level4_contract_evidence.py` consumes the reviewed Level 4 inventory JSON rather than
reconstructing hierarchy selection. Its required boundary fields are `id`, `kind`, `qualified`,
`entryPc`, `instructionPcs`, `exits`, and `parent`; `functionInstanceIdentity` is the hierarchy's
structured source identity (`qualified`, source file, specialization, and inline stack), retained
whenever present. It accepts exactly 18 boundary occurrences from 15 qualified function
families, so the former four `readOffset` plus four specialized-decoder inventory is deliberately
rejected as stale.

The runner retains and adapts PR #77's fourteen focused vectors: accepted rich/empty/optional cases
and rejected offset, width, fork, and public-key mutations. It compares every vector with the pinned
execution-specs reference, executable Lean SSZ specification, and the host `zesu-value` formatter.
That formatter is an independently built source probe: it is compiled separately for the host from
the pinned repaired Zesu source and is not the RV64 ELF whose machine behavior is being observed.
Every production trace is retained in the report; boundary coverage is the union, because the schema
selects different local decoders on different vectors.

The runner records each boundary's entry, declared exit, executed owned instructions, and concrete
stores under the existing QEMU observer. When the reviewed inventory declares a call edge or an exact
store `(pc, address, width, value)`, it checks that observation and mutates it, as it does entry, exit,
and instruction-count observations. A declared edge/store not exercised by any vector is reported as
unmeasured rather than inferred from a trace; this keeps a static possibility from becoming a false
empirical claim.

There is one reviewed exception to call coverage. The `decodePublicKeys` call at `0x12fb4` to
`allocatorFree` is Zig's `errdefer` cleanup after allocating the public-key array. Every root input
that reaches the allocation has already passed `len % 65 == 0` and the maximum-count check; its loop
then reads exactly one 65-byte lane for each index below that count. Consequently the only
post-allocation `try readArray` cannot fail, while allocation failure happens before the cleanup value
exists. The report records this source-precondition argument as statically unreachable, not as an
unmeasured or observed edge. It is a source-review certificate, not empirical evidence or a Lean
proof. Any other declared call must occur in the vector union.

The report explicitly leaves optimized argument locations, result carriers, complete write/frame
conditions, caller-frame preservation, and universal step bounds unmeasured: the observer records
PCs and memory accesses, not the boundary's full register state or all executions. Those gaps must
be closed by a reviewed extraction/probe before a Lean contract states them. This finite evidence
helps admit contracts; it is not proof and is not imported by `root_compliance`.
