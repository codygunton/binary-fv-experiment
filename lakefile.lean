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
  moreLeanArgs := #["--tstack=400000"]

@[default_target]
lean_lib BinaryFv where
  roots := #[`BinaryFv]
