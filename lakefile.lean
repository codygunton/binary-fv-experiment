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
  roots := #[`GeneratedProgram, `DecoderGlobals, `GeneratedBindings]

lean_lib MachineRegionsGenerated where
  srcDir := "build/machine-regions-lean"
  roots := #[`GeneratedMachineRegions, `GeneratedLevel4Attribution]

@[default_target]
lean_lib ZesuVerificationTests where
  srcDir := "verification-target/zesu/tests/lean"
  roots := #[
    `ZesuVerification.BinaryOccurrenceTypes,
    `ZesuVerification.GeneratedBinaryEvidence,
    `ZesuVerification.BinaryOccurrenceCheck,
    `ZesuVerification.ScaleOccurrenceTypes,
    `ZesuVerification.GeneratedScaleEvidence,
    `ZesuVerification.ScaleOccurrenceCheck,
    `ZesuVerification.Level4CfgPartition,
  ]
  moreLeanArgs := #["--tstack=4000000"]

@[default_target]
lean_lib BinaryFv where
  roots := #[`BinaryFv]
  moreLeanArgs := #["--tstack=4000000"]

/-
Validation of the *generated* artifact description. Kernel-checked theorems, built by CI, but
deliberately outside `BinaryFv`'s import closure: `root_compliance` does not depend on any of them,
and they are the slowest evidence in the project. Separating them lets the compliance proof build
without waiting on work it does not use. See `BinaryFv/Evidence.lean`.
-/
@[default_target]
lean_lib BinaryFvEvidence where
  roots := #[`BinaryFv.Evidence]
  moreLeanArgs := #["--tstack=4000000"]
