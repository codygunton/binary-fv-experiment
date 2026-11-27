import Lake
open Lake DSL
package zesu_exec
lean_lib Sail where srcDir := "sail-riscv-lean"
lean_lib LeanRV64DExecutable where
  srcDir := "sail-riscv-lean"
  moreLeanArgs := #["--tstack=4000000"]
lean_lib BinaryFv where
  srcDir := "bfv"
  moreLeanArgs := #["--tstack=4000000"]
lean_lib Evm where srcDir := "vendor/evm-sail-lean"
@[default_target] lean_lib ZesuExec
lean_exe «zesu-difftest» where root := `ZesuExec.Test.Difftest
