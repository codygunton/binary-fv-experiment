# Zesu verification modules

This directory contains the proof that the pinned Zesu Amsterdam V4 decoder binary implements the
pinned Ethereum SSZ decoding specification. SizzLean supplies the executable Lean specification;
the generated Sail model supplies the RISC-V machine semantics; and the Elfling model connects
source-level function identities to instruction regions in the compiled binary. The
implementation-independent specification lives in `BinaryFv/Specs/SSZ`, outside this Zesu target.

The directory names describe the role of each definition or theorem; there is no catch-all `Proof`
namespace.

- `Artifacts`: facts extracted from the pinned Zesu ELF, including its bytes, symbols, memory
  layout, compiler ABI data, and closed instruction inventories.
- `Contracts`: the handwritten, address-free contracts — `meaning`, `pre`, and `post` — selected by
  source function identity and applied to every compiled function instance.
- `ControlFlow`: decoded functions, basic-block/control-flow facts, and reachability.
- `Elflings`: the generated description of where source-level Zesu functions and instructions occur
  in the compiled ELF. It also proves that this description agrees with the ELF and its decoded
  control-flow graph. Proofs select the regions they need from this single whole-program model,
  regenerated with `nix build .#elfling-program`.
- `Entrypoints`: end-to-end ABI-call traces and result interpretation, grouped by exported function.
  `ZesuDecodeRaw` covers `zesu_decode_raw`.
- `MachineExecution`: proofs about concrete Zesu instructions using the executable Sail RISC-V
  semantics, including composed basic-block traces.
- `MemoryRepresentation`: predicates, observers, and primitive-read lemmas connecting Sail memory
  to native Zesu values and the SSZ specification.
- `Runtime`: the Zesu allocator, allocation bounds, and other runtime implementation details.

`Interface.lean` defines the public API for executing a validated Zesu ELF on an input. `Root.lean`
states the final theorem relating that execution to `BinaryFv.Specs.SSZ` for every input in scope.

`MachineExecution/BlobScheduleAndResultStores.lean` is an early standalone proof of selected
blob-schedule decoding and result-store instructions. It predates the current whole-program
refinement and is retained temporarily; no active root proof depends on it.
