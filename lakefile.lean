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
    `SizzLean.Spec.BasicSupported,
    `SizzLean.Spec.Supported,
    `SizzLean.Spec.MaxByteLength,
    -- Every `Proofs` module is named: Lake resolves an import only against a library whose *root*
    -- is a prefix of it, so listing the three central theorems alone leaves their siblings
    -- unbuilt.
    `SizzLean.Compat,
    `SizzLean.Proofs.SimpAttrs,
    `SizzLean.Proofs.Simp,
    `SizzLean.Proofs.UInt,
    `SizzLean.Proofs.Bool,
    `SizzLean.Proofs.BitPack,
    `SizzLean.Proofs.SerializeSize,
    `SizzLean.Proofs.FixedElems,
    `SizzLean.Proofs.VectorFixed,
    `SizzLean.Proofs.ListFixed,
    `SizzLean.Proofs.ContainerFixed,
    `SizzLean.Proofs.Roundtrip,
    `SizzLean.Proofs.Injective,
    `SizzLean.Proofs.SizeBound,
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
  roots := #[`GeneratedProgram, `DecoderGlobals, `GeneratedBindings, `GeneratedManifest]

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
