# Level 4 deinit proof-reuse case study

This study compares the production-ELF regions attributed to
`ssz_raw.RawExecutionWitness.deinit` and `ssz_raw.RawNewPayloadRequest.deinit` at integration
commit `824676a3`. The comparison is reproducible with:

```console
python3 tools/compare_deinit_regions.py \
  build/machine-regions-lean/machine-regions.json --self-test
```

The script reads only the generated machine-region artifact. It normalizes concrete registers,
immediates, and rendered targets while retaining the mnemonic, operand shape, read/write arity,
memory effect, and presence of a non-fallthrough successor. Its output includes every normalized
instruction, every internal and external CFG edge, matching subsequences, and shared n-grams.

## What is actually proved

These are not two completed Lean machine proofs. `RawExecutionWitness.deinit` has a selected Level 4
contract but no exact machine-execution proof module. `RawNewPayloadRequest.deinit` has 1,323 lines
in `Level4RawNewPayloadRequestDeinitSteps.lean` and another 135 lines in its parent-call adapter.
The step module locally Sail-proves and composes the first 12 of 45 instructions, ending at
`0x1321c`; the parent-call adapter then consumes the outstanding selected contract to obtain the
return at `0x129ec`. Thus the useful comparison is between one prospective proof and one expensive,
partial proof, not between two proof terms already available for refactoring.

The NewPayloadRequest work accumulated in 22 commits from 13:06 through 15:20 on 2026-08-09; the
exact history query is recorded with the profile result in
[`level4-deinit-profile.txt`](data/level4-deinit-profile.txt). A direct profile of the 1,323-line
step module took 13.71 seconds wall on the recorded run. Its reported async
declaration times overlap and must not be summed. The largest visible individual costs included the
two restored-argument steps (5.69 and 5.17 seconds), the second store step (4.64 seconds), the `s1`
save (4.15 seconds), and the first store (4.09 seconds).
This is roughly 110 source lines per locally composed instruction, although shared definitions and
handoff structures make that ratio only an effort indicator.

## Source and compiler identity

The pinned Zig source makes the semantic relationship explicit:

- `RawExecutionWitness.deinit` at `ssz_raw.zig:143` frees three slice fields: `state`, `codes`, and
  `headers`.
- `RawNewPayloadRequest.deinit` at `ssz_raw.zig:130` calls
  `execution_payload.deinit`, frees `versioned_hashes`, and calls
  `execution_requests.deinit`.

The matching decoder object hash recorded in generated `program.json` is
`f3a296a2510a8c7db132cacfb72cbd53266e609199ba844d31a777ca7072530d`. Its DWARF independently
identifies two `DW_TAG_subprogram` DIEs:

| source function | source line | object interval | linked interval |
| --- | ---: | ---: | ---: |
| `RawExecutionWitness.deinit` | 143 | `0x2d88..0x2dfc` | `0x13038..0x130ac` |
| `RawNewPayloadRequest.deinit` | 130 | `0x2f3c..0x2ff0` | `0x131ec..0x132a0` |

Both linked intervals equal the generated excluded-region extents after adding the decoder object's
`0x102b0` link base. The generated source manifest pins `ssz_raw.zig` by SHA-256
`ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131`. The retained artifact has
DWARF and symbols but no LLVM IR, so this study can check source identity and line attribution but
cannot yet compare LLVM basic blocks or optimization remarks. Retaining normalized LLVM IR and
inlining/optimization records should be added as pre-work rather than reconstructed from machine
code.

## Exact machine shapes

The witness region has 29 instructions, 28 internal fallthrough edges, three external call edges,
and one terminal `ret`. The payload region has 45 instructions, 44 internal fallthrough edges, five
external call edges, and one terminal `ret`. Neither contains a conditional branch or loop. Their
mnemonic sequences are:

```text
witness:
addi sd sd mv ld ld ld ld sd sd sd sd addi auipc jalr
ld ld mv auipc jalr ld ld mv auipc jalr ld ld addi ret

payload:
addi sd sd sd mv mv ld ld sd sd mv mv auipc jalr ld ld addi auipc jalr
ld ld ld ld sd sd sd sd addi auipc jalr ld ld addi auipc jalr
ld ld addi auipc jalr ld ld ld addi ret
```

The matcher aligns 21 of 29 witness instructions with payload instructions (sequence ratio
0.6216). It finds 15 shared normalized 3-grams and 11 shared normalized 5-grams. The longest aligned
block has 13 instructions:

```text
ld ld ld ld sd sd sd sd addi auipc jalr ld ld
```

That block is witness indices 4–16 and payload indices 19–31. It is structurally genuine but not a
semantic identity: concrete base registers, record offsets, stack destinations, and the nested call
target differ. A second aligned five-instruction block is `auipc jalr ld ld addi`. Both functions
also use the same prologue/epilogue schema, with the payload function adding one saved register and a
larger frame:

| property | witness | payload |
| --- | ---: | ---: |
| frame size | `0x30` | `0x50` |
| saved callee registers | `ra`, `s0` | `ra`, `s0`, `s1` |
| external calls | 3 | 5 |
| loads / stores | 10 / 6 | 15 / 9 |

At source level the witness body is a three-element schedule of `free(slice)`. The payload body is a
heterogeneous five-call schedule: nested payload cleanup, one direct slice free, then nested request
cleanup whose optimized body expands into three more allocator-free calls. This explains both the
large common machine pattern and why a theorem asserting that the whole functions are identical
would be false.

## Contract and frame differences

Both selected assumptions use `DeinitInlineArgs`, require the record/allocator/stack carriers and an
allocator-pair representation, use a 1,024-step bound, and promise no allocation. The current
witness interface ends in generic `deinitExit`: code remains intact, allocation state is unchanged,
and no caller record/input bytes are written. It does not expose an exact return PC, restored stack,
register write set, or concrete stack-memory frame.

The payload interface is stronger because its parent already consumes it. It fixes entry PC
`0x131ec`, link/return PC `0x129ec`, and frame size `0x50`; its exit restores `sp`, `ra`, `s0`, and
`s1`, gives `WritesOnlyRegs rawNewPayloadRequestDeinitWrites`, confines memory writes to the child
frame, preserves `decoderPreserved`, and retains code, retirement, and no-allocation facts. A shared
machine proof can parameterize these facts, but the witness contract must first be strengthened to
the exact caller-visible return/frame required by its actual parent. Reusing the stronger payload
theorem against the current weaker witness statement would hide, not solve, that interface work.

## Recommended pre-work

1. Generate a typed cleanup schedule from DWARF/source plus decoded instructions. Each entry should
   distinguish `free(slice descriptor)` from `call nested deinit`, bind the record-field offsets and
   live machine carriers, and retain the exact call/return edges. This semantic schedule is the main
   missing link between the three/five source operations and their optimized register/stack packets.
2. Generate a parameterized prologue/epilogue skeleton from frame size, saved-register list, exact
   PCs, and write region. The matcher already recognizes this family; Lean should receive data and
   emit the routine instruction-class/`Seg` obligations instead of 300–500 lines of hand-written
   save/restore transport.
3. Add a reusable `free-call packet` proof combinator or generator for the recurring
   `load descriptor → materialize temporary descriptor → set a0 → auipc/jalr` shape. Keep record
   offsets, target identity, writable stack slots, and returned frame as explicit parameters. This
   is larger and more valuable than abstracting isolated two-instruction sequences.
4. Strengthen selected child contracts from a generated caller-use analysis before proof writing:
   exact return PC, saved registers, permitted register writes, permitted memory region, and semantic
   carrier bindings. The payload proof's repeated contract repairs show that discovering these facts
   instruction-by-instruction is the dominant avoidable cost.
5. Run normalized retrieval over all generated owners before dispatching proof work. Use source
   identity, CFG/call topology, mnemonic/effect n-grams, frame signature, and record-access offsets
   as separate indexed features. Show agents the nearest proved regions and parameter differences in
   their task prompt.
6. Retain LLVM IR, inlining records, and optimization remarks as generated evidence. DWARF proves
   these two source identities, but LLVM data would better explain why nested source calls became
   five machine call packets and which record fields survive in registers.

Probabilistic embeddings or graph clustering are useful only after this deterministic representation
exists. Here, a simple inspectable signature already retrieves a 21-instruction alignment and the
shared call packets. Learned ranking could improve corpus-wide recall, especially under instruction
scheduling and register allocation, but it should rank candidate templates only. Exact generated
PCs, decoded operands, compiler/source bindings, contract review, and Lean kernel checking remain
the admission gate.

## Conclusion

Proof writing is currently correct but too bottom-up: it discovers the frame, live carriers, stack
layout, and repeated call packets while proving individual instructions. This case supports a
schedule-driven generator, not a single hand-written theorem shared wholesale. The realistic target
is to generate 60–80% of each proof—the exact instruction wrappers, `Seg` composition, frame
transport, and recurring free-call packets—while leaving source-specific field meanings, nested
child contracts, and parent-visible postconditions as reviewed obligations.
