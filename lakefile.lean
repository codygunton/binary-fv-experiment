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
    `SizzLean.Spec.BasicSupported,
    `SizzLean.Spec.Supported,
    `SizzLean.Spec.MaxByteLength,
    `SizzLean.Compat,
    `SizzLean.Proofs.SimpAttrs,
    `SizzLean.Proofs.Simp,
    `SizzLean.Proofs.SerializeSize,
    `SizzLean.Proofs.UInt,
    `SizzLean.Proofs.Bool,
    `SizzLean.Proofs.FixedElems,
    `SizzLean.Proofs.VectorFixed,
    `SizzLean.Proofs.ListFixed,
    `SizzLean.Proofs.ContainerFixed,
    `SizzLean.Proofs.BitPack,
    `SizzLean.Proofs.SizeBound,
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
lean_lib BinaryFv where
  roots := #[
    `BinaryFv,
    `BinaryFv.Zesu.Validation.SequentialSpliceWitness,
    `BinaryFv.Zesu.Validation.LoopDischarge,
    `BinaryFv.Zesu.Validation.CallStepRetInRegion,
    `BinaryFv.Zesu.Validation.SyntheticUnitProbe,
  ]
  moreLeanArgs := #["--tstack=4000000"]

/-
Row B validation runner: a host executable over the handwritten decode `meaning`. It is NOT part of
the `BinaryFv` theorem library and is never imported by it — validation is falsification evidence,
never a proof premise.
-/
lean_exe ssz_contract_runner where
  root := `BinaryFv.Zesu.Validation.ContractRunner
  moreLeanArgs := #["--tstack=4000000"]
