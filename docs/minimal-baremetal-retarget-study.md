# Minimal syscall-free SSZ retarget study

The minimal migration is **not** to replace `ssz_decode_root.main`. Keep the pinned Zesu decode
object byte-for-byte and replace only its linked host implementations with a syscall-free memory
context. A comparison linker layout can keep every existing symbol address and every pre-existing
data address unchanged.

## Compared artifacts

The baseline was Nix output `.#zesuSszDecodeRv64Elf` at Zesu `d67f28c`, built
`ReleaseSmall` for freestanding `rv64im_zicclsm`. Two temporary, uncommitted candidates were built:

1. **Preserved main:** the exact baseline Zesu object linked to `read_input`, `write_output`, and
   `zkvm_exit` implementations backed by memory context instead of Linux `ecall`. Text and data were
   pinned at `0x10120` and `0x19000`; the replacement functions retained their old extents.
2. **Direct entry:** a comparison-only `zesu_ssz_decode(input, size, result)` root retaining the
   existing noinline `decodeInput` boundary, linked without input/output/exit functions.

No candidate source was added to the repository. `tools/compare_retarget_artifacts.py` reproduces
the exact-byte and normalized-CFG comparison once candidate ELFs and their generated CFG JSON files
are supplied.

## Preserved-main result

- Zero `ecall` instructions.
- All 52 named functions remain at the same addresses.
- 48/52 named functions are identical at the same PCs. Deduplicating the `main`/source-name alias,
  28,708/28,888 `.text` bytes (99.38%) remain at the same address with the same bytes.
- The only changed functions are `_start`, `read_input`, `write_output`, and `zkvm_exit` (45 old
  instructions total). Their CFGs genuinely change: Linux read/write loops become memory-context
  loads/stores, and Linux exit becomes a bare-metal terminal instruction.
- `main`, `ssz_decode_root.decodeInput`, every decoder/RLP helper, every observation encoder, the
  allocator, `memcpy`, and `memset` are byte-identical at their old PCs. There are no
  relocation-patched bytes among these functions.
- `ZKVM_HEAP_POS`, `ZKVM_HEAP_TOP`, `heap_buffer`, `input_buffer`, and `alt_fl_alloc.state` retain
  their old addresses. A 32-byte input/output context is appended after `alt_fl_alloc.state`, so no
  pre-existing data moves.

An intermediate link put the new context before `alt_fl_alloc.state`. That moved it by 32 bytes and
changed one relocation-patched `addi` in `main` despite an otherwise identical CFG. Moving the new
context to a trailing section eliminated even that difference. This demonstrates that linker layout,
not compiler luck, is sufficient to preserve the current decoder and proof PCs.

The ABI change is confined to the machine entry/termination contract. Before entering `main`, memory
supplies the input pointer/length; `write_output` records the observation pointer/length; `zkvm_exit`
terminates with the code still in `a0`. A tiny register-argument adapter can be placed in a new
post-image section if required, without moving existing code. The reserved input buffer can instead
remain the input window, avoiding an adapter and preserving the complete old memory layout.

## Direct-entry result

- Zero `ecall` instructions; 39 rather than 52 named functions; 6,242 rather than 7,222 decoded
  instructions.
- All 6,212 instructions outside the new 30-instruction entry have matching normalized CFGs,
  mnemonics, registers, and block-relative successors in the old ELF (37 functions, including
  compiler-renumbered allocator helpers). Thus 99.52% of the direct ELF is structurally unchanged.
- Nevertheless every function moves. Only 9 common named functions (1,408 bytes) remain byte-exact;
  most other differences are PC-relative call/data relocation immediates.
- Removed regions are `_start`, Linux host functions, `main`, and the observation encoder. The new
  entry also changes the public ABI from a memory-preconditioned `main()` plus encoded observation to
  `(input pointer, input length, StatelessInput result pointer) -> status`.
- Heap BSS falls by 64 MiB because the fixed input buffer is removed. The raw `StatelessInput` result
  contains allocator-backed pointers and is a worse external compliance observation than the current
  versioned, injective byte encoding.

The normalization deliberately erases numeric immediates while retaining CFG topology, instruction
mnemonics, and registers. It establishes structural reuse, not semantic equality of constants. The
preserved-main result is stronger: its reusable functions were compared as exact bytes at exact PCs.

## Proof impact and migration sequence

With preserved main, regenerate the ELF digest/program-image facts and the four host-region CFG and
boundary artifacts. Existing exact instruction lemmas and compositions for `main`, `decodeInput`,
observation encoding, allocator functions, and `memcpy` should need no address rewrite; their code
bytes and PCs are unchanged. Proof statements mentioning the whole `Artifacts.programImage` still
need regeneration because four code regions and the image digest change.

Rewrite only the contracts/proofs for `read_input`, `write_output`, `zkvm_exit`, and endpoint
termination. Replace `stdin`/`stdout`/Linux-transition fields in `MainEntry` and `MainExit` with the
memory-context representation, while leaving the six-call Level 0 route and decoder contract intact.
Then regenerate evidence and mutation tests for the memory clauses before re-admitting those three
host contracts.

Recommended sequence:

1. Specify the memory context and terminal-state ABI, including output lifetime/capacity.
2. Add the real forked-Zesu/runtime implementation and a linker assertion fixing every legacy text
   and data symbol used by proofs; fail the build if any moves.
3. Regenerate the artifact image plus host CFG/evidence only, and verify the 48-function exact-byte
   invariant automatically.
4. Replace the three host contracts and root entry/exit state model; retain the current `main`,
   decoder, encoder, allocator, and `memcpy` proofs.
5. Use the direct entry only if the shipped interface must exclude the observation encoder; it has a
   mechanically rebasable decoder core but needlessly discards the already-proved Level 0 route and
   creates a less useful raw-pointer result ABI.
