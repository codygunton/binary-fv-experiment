# Grafted-Zesu deletion audit

This audit distinguishes reusable proof infrastructure from statements bound to the locally grafted
decoder. The complete original tree remains recoverable from
`archive/zesu-grafted-decoder-level4`; deletion here means “not part of the authentic-target proof,”
not loss of history.

## Recovered into target-independent namespaces

- `BinaryFv.RiscV.Elfling.Seg`: opaque straight-line trace composition, register lifetimes, register
  and memory frames, stores, jumps, and retirement. Its Zesu imports were replaced by generic frame
  and register-write modules.
- `BinaryFv.RiscV.Instruction.{RegisterRuns,DecodeTactic}`: generated Sail register actions and the
  shared instruction-decode tactic; neither mentions an ELF, source function, or SSZ value.
- `BinaryFv.RiscV.Step.RegisterWrite`: the target-independent register-writing successor state and
  write/memory/retirement frames. The old file's `decodeRaw` geometry and configured-decoder wrappers
  were deliberately not copied.
- `BinaryFv.RiscV.Logic.MemoryWriteFrame`: predicate-valued byte regions and compositional
  `WritesOnlyWithin` algebra extracted from the old decoder environment/ownership modules.
- `BinaryFv.RiscV.Runtime.{BumpAllocator,AllocationCursor}`: pure Zig-style checked bump allocation,
  padding bounds, and cursor-chain composition. Old constants for the grafted decoder's 2 MiB input,
  allocation multiplier, and 64 MiB zkVM arena were not retained.
- `BinaryFv.ProofProgress.MachineProofManifest`: kernel-backed exact-PC/composition manifests, with
  `level4` renamed to target-neutral `selectedLevel`.

The generic `MemFramed`, loop induction, block-step, call/return, register-agreement, and separation
logic used by the old `memcpy` proof were already under `BinaryFv.RiscV` and remain unchanged.

## Deleted categories and why

- `Artifacts` (7 files): byte image, symbols, ABI, allocator call sites, and layout are facts about
  the grafted ELF. Reusing any would assert false machine facts about upstream Zesu.
- `DecodedValue` and `Specs/SSZ` (17 files): representations and observations implement the removed
  Amsterdam/Etheorem schema. EVM-Sail generated Lean replaces the semantic authority.
- `Contracts` (29 files): public contracts quantify over the removed `DecoderEnvironment`, old
  decoded-value representations, grafted allocator layout, or selected `decodeRaw` boundaries. Only
  their target-independent memory-frame algebra was extracted.
- `ControlFlow`, `Elflings`, and generated evidence (16 files): every range, function instance,
  instruction word, exit, and reachability certificate names the removed production ELF.
- `Entrypoints`, `Root`, and `ExecutionTypes` (31 files): runner ABI, conditional refinement levels,
  and `root_compliance` connect the grafted executable to the removed spec. Keeping their theorem
  statements would misrepresent current progress.
- `MachineExecution` target modules (52 files before extraction): concrete steps contain grafted
  addresses, bytes, generated ownership predicates, or target machine contexts. The exact `memcpy`
  theorem, for example, proves the helper at `0x13eb8`; it is not a theorem about arbitrary Zig
  `memcpy`. Its reusable loop/frame APIs remain, while the address-bound instance is archived.
- `Runtime` target residue: allocator-vtable addresses and decoder-specific allocation bounds were
  removed; the pure bump allocator and generic cursor arithmetic were recovered.
- verification fixtures, QEMU evidence, oracle, and UI JSON: they execute or describe the grafted
  binary and would silently contaminate admission of the authentic target.
- old Elfling/machine-region/proof-map generators: their extraction cores were mixed with hundreds of
  lines of `decodeRaw` ownership, route, PC-count, and namespace policy. They remain archived for
  selective recovery after the authentic target schema exists; retaining them live as “generic”
  would be misleading.

## Retained authoring tools

The live tree keeps RV64 analysis, Lean profiling, n-gram motif discovery, proof-corridor retrieval,
the target-neutral binary-regions viewer shell, and the proof manifest type. Historical n-gram and
recovery reports remain explicitly labeled; no old measurement contributes to new proof status.
