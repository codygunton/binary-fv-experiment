# Production-binary evidence

This directory checks the Row A contracts against execution of the exact production Zesu ELF. It
does not rebuild, patch, or instrument the guest binary. Pinned QEMU runs the ELF while a read-only
plugin records executed instructions, transfers, register snapshots, memory accesses, and allocator
cursor writes.

The workflow has two layers:

1. [generate_evidence.py](generate_evidence.py) reduces the focused capture consumed by
   [BinaryOccurrenceCheck.lean](../../../../BinaryFv/SSZ/Zesu/Validation/BinaryOccurrenceCheck.lean).
   It covers one `decodeOptionalBlobSchedule` occurrence and its three child readers.
2. [scale_occurrences.py](scale_occurrences.py) reduces full traces into deterministic evidence for
   all 141 occurrences, consumed by
   [ScaleOccurrenceCheck.lean](../../../../BinaryFv/SSZ/Zesu/Validation/ScaleOccurrenceCheck.lean).

The scaled checker asks whether each occurrence was entered correctly, followed its generated CFG,
respected exits and step bounds, realized its argument/result bindings, preserved protected memory,
and performed the independently expected allocations. A result is pass, fail, or an explicit gap;
missing evidence is never counted as success.

[allocation_shapes.py](allocation_shapes.py) derives expected allocation sequences from the pinned
source-level decode order and compiler-reported element layouts.
[static_reachability.py](static_reachability.py) explains the three occurrences that no fixture
reaches; its generated report is [STATIC_REACHABILITY.md](STATIC_REACHABILITY.md). The focused
[negative tests](negative_tests.py) and [scaled negative tests](scale_negative_tests.py) corrupt
captured evidence to show that the checks can fail. The full per-occurrence results and documented
gaps are in [SCALE_COVERAGE.md](SCALE_COVERAGE.md).

Committed evidence contains no host-specific stack addresses. Fixed ELF addresses remain exact;
stack-relative values are normalized by one common delta so regeneration is stable across machines.
