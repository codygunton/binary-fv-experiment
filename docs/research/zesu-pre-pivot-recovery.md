# Zesu pre-pivot recovery map

The complete repository ref set before the upstream-Zesu/EVM-Sail pivot is stored outside the
repository at:

```text
/home/cody/backups/binary-fv-pre-upstream-zesu-pivot-20260810.bundle
SHA-256 8d2586031b3c08b215ff544641683e0e2b96f2b7f8b122c3b2bcf73278f8dfeb
```

`git bundle verify` accepted the bundle on 2026-08-10. It contains 250 refs: all 140 local branch
heads, remote-tracking refs, eight stashes through `refs/stash`, and the otherwise detached review
commit `a886a75d` under tag `archive-detached-l4-entry-review-a886a75d`.

The maintained snapshot is this branch, `archive/zesu-grafted-decoder-level4`. It contains the
integrated Level 4 proof progress, generated proof-preparation manifests, proof-map UI, read-offset
and deinit reuse studies, corridor retrieval tool, and the n-gram motif study. The original n-gram
history is also retained on pushed branch `ssz-ngram-study`.

Noteworthy historical bundle refs include:

- `l4-specialized-phase`: the final specialized-route working line, including its seven commits
  that were not patch-equivalent to this archive during cleanup.
- `ssz-level4-refinement`: the integration tip immediately before the archive added the n-gram work.
- `l4-header-route`, `meta-deinit-study`, and `l4-reader-trace-finish`: the source studies and reader
  composition lines from which the integrated archive was assembled.
- `ssz-level2-progress`: the former stacked PR #77 line.
- `archive-detached-l4-entry-review-a886a75d`: the detached entry-review worktree that previously
  lived under `/tmp`.

Inspect without restoring anything:

```bash
git bundle list-heads /home/cody/backups/binary-fv-pre-upstream-zesu-pivot-20260810.bundle
```

Restore one historical branch into a clone:

```bash
git fetch /home/cody/backups/binary-fv-pre-upstream-zesu-pivot-20260810.bundle \
  refs/heads/l4-specialized-phase:refs/heads/recovered/l4-specialized-phase
```

Restore every saved ref only into a disposable clone; importing all refs into the working repository
would recreate the clutter this bundle was made to remove.
