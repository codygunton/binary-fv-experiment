import Lake
open Lake DSL

package sha_fv_experiment where

require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.26.0"

lean_lib LeanRV64DExecutable where
  srcDir := "build/sail-riscv-lean"
  moreLeanArgs := #["--tstack=4000000"]

/-
The SizzLean closure is copied and content-checked by Nix rather than added as a Lake dependency. It
is deliberately restricted to the pure SSZ decoder modules, so the proof project neither imports nor
links SizzLean's SHA/OpenSSL layer. The project-owned Amsterdam V4 specification is ordinary source
under `BinaryFv/Specs/SSZ`.
-/
lean_lib SizzLeanPinned where
  srcDir := "build/sizzlean-lean"
  roots := #[
    `SizzLean.Spec.Type,
    `SizzLean.Spec.Interp,
    `SizzLean.Spec.Constants,
    `SizzLean.Spec.SSZError,
    `SizzLean.Spec.Serialize,
    `SizzLean.Spec.Deserialize,
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
  roots := #[`GeneratedProgram, `DecoderGlobals]

lean_lib MachineRegionsGenerated where
  srcDir := "build/machine-regions-lean"
  roots := #[`GeneratedMachineRegions]

@[default_target]
lean_lib ZesuVerificationTests where
  srcDir := "verification-target/zesu/tests/lean"
  roots := #[
    `ZesuVerification.SequentialSpliceWitness,
    `ZesuVerification.LoopDischarge,
    `ZesuVerification.CallStepRetInRegion,
    `ZesuVerification.SyntheticUnitProbe,
  ]
  moreLeanArgs := #["--tstack=4000000"]

@[default_target]
lean_lib BinaryFv where
  roots := #[`BinaryFv]
  moreLeanArgs := #["--tstack=4000000"]
