# Production-binary evidence

This directory checks the Row A contracts against execution of the exact production Zesu ELF. It
does not rebuild, patch, or instrument the guest binary. Pinned QEMU runs the ELF while a read-only
plugin records executed instructions, transfers, register snapshots, memory accesses, and allocator
cursor writes.

The workflow has two layers:

1. `generate_evidence.py` and `BinaryOccurrenceCheck.lean` cover one
   `decodeOptionalBlobSchedule` occurrence and its three child readers as a small end-to-end example.
2. `scale_occurrences.py` and `ScaleOccurrenceCheck.lean` reduce full traces into deterministic
   evidence for all 141 occurrences.

The scaled checker asks whether each occurrence was entered correctly, followed its generated CFG,
respected exits and step bounds, realized its argument/result bindings, preserved protected memory,
and performed the independently expected allocations. A result is pass, fail, or an explicit gap;
missing evidence is never counted as success.

`allocation_shapes.py` derives expected allocation sequences from the pinned source-level decode
order and compiler-reported element layouts. `static_reachability.py` explains the three occurrences
that no fixture reaches. The negative-test scripts corrupt captured evidence to show that each check
is capable of failing.

Committed evidence contains no host-specific stack addresses. Fixed ELF addresses remain exact;
stack-relative values are normalized by one common delta so regeneration is stable across machines.
