import Lake
open Lake DSL

package sha_fv_experiment where

require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.26.0"

lean_lib LeanRV64DExecutable where
  srcDir := "build/sail-riscv-lean"
  moreLeanArgs := #["--tstack=4000000"]

/-
The specification closure is copied and content-checked by the Nix derivation rather than added as a
Lake dependency. It is deliberately restricted to SizzLean's pure SSZ decoder modules and the local
Amsterdam V4 bridge, so the proof project neither imports nor links the bridge's SHA/OpenSSL layer.
-/
lean_lib SszSpec where
  srcDir := "build/ssz-spec-lean"
  roots := #[
    `SizzLean.Spec.Type,
    `SizzLean.Spec.Interp,
    `SizzLean.Spec.Constants,
    `SizzLean.Spec.SSZError,
    `SizzLean.Spec.Serialize,
    `SizzLean.Spec.Deserialize,
    `SszBridge.Core,
  ]

lean_lib ZesuSszElf where
  srcDir := "build/zesu-ssz-elf-lean"
  roots := #[`ZesuSszElf]
  moreLeanArgs := #["--tstack=4000000"]

lean_lib ZesuSszAbi where
  srcDir := "build/zesu-abi-lean"
  roots := #[`ZesuSszAbi]

lean_lib ElflingGeneratedProgram where
  srcDir := "build/elfling-program-lean"
  roots := #[`GeneratedProgram, `DecoderGlobals, `GeneratedBindings]

@[default_target]
lean_lib BinaryFv where
  roots := #[`BinaryFv]
  moreLeanArgs := #["--tstack=4000000"]

/-
Row B validation runner: a host executable over the handwritten decode `meaning`. It is NOT part of
the `BinaryFv` theorem library and is never imported by it — validation is falsification evidence,
never a proof premise.
-/
lean_exe ssz_contract_runner where
  root := `BinaryFv.SSZ.Zesu.Validation.ContractRunner
  moreLeanArgs := #["--tstack=4000000"]
