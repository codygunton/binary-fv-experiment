import Lake
open Lake DSL

package sha_fv_experiment where

require «cryptography» from "./specs/sha-3"
require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.26.0"

lean_lib LeanRV64DExecutable where
  srcDir := "build/sail-riscv-lean"
  moreLeanArgs := #["--tstack=400000"]

lean_lib Sha3Elf where
  srcDir := "build/sha3-elf-lean"

@[default_target]
lean_lib ShaFv where
