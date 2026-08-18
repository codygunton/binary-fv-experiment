# `root_compliance hLevel2` proof rewrite results

This experiment changes only proofs already used below `root_compliance hLevel2`. It proves no new
RISC-V instruction and does not change a contract or theorem statement.

## Retained transformations

- Exact instruction sites bundle pinned bytes, ownership, and fall-through facts.
- `ConfiguredMachinePre.decodeContext` and `.storeDecodeContext` replace repeated configured-machine,
  fetch, PMA, MMIO, and retirement setup.
- `owned_pc` checks literal region membership.
- Shared instruction-class theorems replace ten hand-expanded Level 0 ADDI, AUIPC, and JALR proofs.
- `Seg` replaces eligible writer, allocator, and `zkvm_exit` successor-state chains. Quantified memory
  frames replace their per-state memory equalities.
- The thirteen decode-input save wrappers share one exact store theorem and retain only their symbolic
  register, word, and address facts.

## Remaining repeated patterns

The final L2-normalized n-gram census reports 36.2% coverage at four lines, 23.8% at eight lines, and
9.1% at sixteen lines. The highest-ranked patterns no longer identify an unabstracted proof mechanism:

- 15 JALR patterns are named exact-site theorem statements whose bodies already call
  `configuredJalrCallStep`.
- 13 writer-save patterns are literal access/frame bullets. Both invariant `autoParam` defaults and a
  shared goal-dispatch tactic slowed the writer from 199.8s to 216.6–217.4s, so they were reverted.
- 12 writer and 11 decode-input patterns initialize or extend `Seg`; they are the compact form.
- Repeated tuple rows describe distinct saved-word locations and values, not tactics.
- Repeated stdin/cursor/exit-code fields are the public carrier surface between different handoffs.
  Splitting the largest such handoff structure slowed the writer to 247.3s and was reverted.
- A generic taken/fall-through branch class compiled at all four candidate routes but slowed the writer
  to 235.1s and increased source size when retained only at Level 0, so it was reverted.

`readInputInstanceContract` is the sole explicit multi-state successor chain. Its first seven steps are
ordinary machine steps, but its eighth is `BareMetalReadStep`; existential `Seg` does not expose the
chosen retirement witness needed by that endpoint step. A conversion would add a new trace-lift API,
not reuse an existing proof pattern, so this fixed-slice experiment retains the explicit chain.

## Measurements

| metric | before | after | change |
|---|---:|---:|---:|
| non-comment Lean lines in the root dependency slice | 34,026 | 31,848 | -2,178 (-6.4%) |
| seven proof-module code lines | 22,506 | 20,764 | -1,742 (-7.7%) |
| seven proof-module declarations | 694 | 592 | -102 (-14.7%) |
| writer focused direct check | 218.26s baseline profile | 209.21s | -9.05s (-4.1%) |
| Level 0 profiler | 25.63s | 20.53s | -5.10s (-19.9%) |
| decode-input profiler | 23.40s | 20.19s | -3.21s (-13.7%) |
| runtime-leaves profiler | 40.07s | 37.04s | -3.03s (-7.6%) |

The endpoint denominator remains 6,809 unique instructions. The proof still directly attributes 157
PCs, retains 295 unique refinement-boundary PCs, and conditionally covers 6,668 PCs through the 17
unchanged Level 2 contracts.

The writer's profiler-instrumented wall time was 234.01s and 234.55s in two final runs, while its
uninstrumented source check was 209.21s. The corresponding final CPU times were 213.58s, 211.94s, and
188.16s. The profiler overhead is therefore reported rather than hidden; the retained proof improves
the ordinary focused gate but not the instrumented wall measurement under this machine load.
