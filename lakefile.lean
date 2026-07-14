import Lake
open Lake DSL

package sha_fv_experiment where

require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.26.0"

lean_lib LeanRV64DExecutable where
  srcDir := "build/sail-riscv-lean"
  moreLeanArgs := #["--tstack=400000"]

lean_lib RethKeccakElf where
  srcDir := "build/reth-keccak-elf-lean"
  roots := #[`RethKeccakElf]

lean_lib KeccakSpec where
  srcDir := "build/keccak-spec-lean"
  roots := #[`Spec.Keccak.Keccak256]

@[default_target]
lean_lib BinaryFv where
  roots := #[`BinaryFv]
