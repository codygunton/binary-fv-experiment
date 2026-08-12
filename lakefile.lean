import Lake
open Lake DSL

package sha_fv_experiment where

require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.26.0"

lean_lib LeanRV64DExecutable where
  srcDir := "build/sail-riscv-lean"
  moreLeanArgs := #["--tstack=4000000"]

/-
Generated from the pinned `zesu-ssz-decode.o` by `tools/generate_zesu_program.py`, built and
determinism-checked by Nix (`nix/analysis.nix`). Address-bearing and UNTRUSTED: the sizes and byte
reads a proof relies on are re-derived by `#guard` in `BinaryFv/Zesu/Generated/Check.lean`.
-/
lean_lib ZesuProgramGenerated where
  srcDir := "build/zesu-program-lean"
  roots := #[`Image, `Program]
  moreLeanArgs := #["--tstack=4000000"]

@[default_target]
lean_lib BinaryFv where
  roots := #[`BinaryFv]
  moreLeanArgs := #["--tstack=4000000"]
