import Lake
open Lake DSL

package sha_fv_experiment where

require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.29.0"

lean_lib Sail where
  srcDir := "build/sail-riscv-lean"

lean_lib LeanRV64DExecutable where
  srcDir := "build/sail-riscv-lean"
  moreLeanArgs := #["--tstack=4000000"]

@[default_target]
lean_lib BinaryFv where
  roots := #[`BinaryFv]
  moreLeanArgs := #["--tstack=4000000"]
