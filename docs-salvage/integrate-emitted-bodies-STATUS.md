# STATUS — branch `integrate-emitted-bodies` (from `ssz-conditional-root` @ 1db13ad)

Task: land the five families' emitted-body wiring on the branch of record, honestly.

## What was integrated

Six blocks now live in `BinaryFv/SSZ/Zesu/Validation/ContractGroundTruth.lean`:

| source | branch / worktree | state when found |
| --- | --- | --- |
| task 6a-v base (leafFrame split, `postBytesAt`) | `task6av` @ `.claude/worktrees/wf_fb09f3b9-8ad-1` | uncommitted; shared prerequisite of all five |
| allocator | `task-6a-ii-allocator` @ `be70c6d` | committed |
| results (`rawError`/`rawResult`) | `task-6a-ii-results` @ `6616f76` | committed |
| copy (`memcpy`/`memmove`) | `task-6a-ii-copy` @ `.claude/worktrees/wf_fb09f3b9-8ad-5` | uncommitted |
| decoders | `task6aii-decoders` @ `.claude/worktrees/wf_fb09f3b9-8ad-6` | uncommitted |
| validation | `task6aii-validation` @ `.claude/worktrees/wf_fb09f3b9-8ad-7` | uncommitted |

Nothing was reconstructed from scratch: every worktree was still present.

## The three mandatory conditions

1. **Tautology gates.** `copyPreVerdict`, `allocPreVerdictGated`, `allocPostVerdictGated`,
   `resultsPostVerdict`, `canonicalOffsetsPostGated` downgrade a would-be `ok` to a gap naming the
   unfalsifiable conjuncts. Refutations are untouched (an unfalsifiable conjunct never fails).
2. **Pass licensing.** `memoryBytesB_iff`, `codeIntactB_iff`, `noAllocationB_iff` supply the missing
   `Bool → Prop` direction; `postCopyCheckedB_iff_postCopy`,
   `postScalarReadCheckedB_iff_postScalarRead`, `postBytesAtCheckedB_iff_postBytesAt` lift them to
   equivalences. Only the two copy rows reach `ok`.
3. **No heartbeats raise.** `LocalObligationLedger.lean` is untouched and still carries
   `set_option maxHeartbeats 800000` at line 30.

## Column totals

| column | 6a-v base | integrated |
| --- | --- | --- |
| 1 entered | 135 / 0 | 135 / 0 |
| 2 pre | 2 / 100 | 2 / 102 |
| 3 exited | 103 / 33 | 103 / 33 |
| 4 post | 0 / 10 | 2 / 11 |
| 5 steps | 104 / 1 | 112 / 1 |

Three passes the individual families claimed were withdrawn: `rawAlloc` (0) columns 2 and 4, and
the two copy rows' column 2.
