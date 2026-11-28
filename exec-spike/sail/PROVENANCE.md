# Provenance of `exec-spike/sail-riscv-lean`

| Input | Value |
|---|---|
| sail-riscv | `riscv/sail-riscv` commit `65ddde80ee2b131bf46c20e6e748343c336c4071` (release 0.12) |
| lean-sail runtime | `rems-project/lean-sail` rev `79b4d08505af29d88b3918f32d29840fae1fa191` |
| nixpkgs (`flake.lock`) | `NixOS/nixpkgs` rev `f205b5574fd0cb7da5b702a2da51507b7f4fdd1b` |
| Sail compiler | `pkgs.ocamlPackages.sail` 0.20.1 (OCaml 5.4.1) with nixpkgs' own patch and `00-sail-lean-asr.patch` (derivation `zesuSailCompiler`) |
| Build tools | cmake 4.1.2, z3 4.16.0, ninja and pkg-config from the same nixpkgs |
| Sail modules | `main;I_insts;M_insts;Zba;Zbb;Zbs;Zbkb`, target `generated_lean_executable_rv64d` |
| `00-sail-lean-asr.patch` | sha256 `97476ae17ea031760993d709acf8303b987399508ed66b9c664ec4a70cf2eefd` (applied to the Sail compiler source) |
| `01-profile-config.patch` | sha256 `2b7e4c591701442743dfffe2c13d5e16b0d6d7fcf6533ea5824833ef041fe775` |
| `02-specialise.patch` | sha256 `d06cf8aedb93636bf1b4a65ce8243e08826dc731d0ac4a1d415ef143e5d9e7dc` |

Build: `nix build -L .#zesuSailRiscvLean` (derivations `zesuSailCompiler`, `zesuSailRiscvRaw`,
`zesuSailRiscvLean` in `nix/proof.nix`: the stock `sailRiscvRegeneratedRaw` with `patches`, the
patched compiler and the module list set, and the stock runtime swap). Check:
`nix build -L .#zesuSailRiscvLeanRegenerationCheck` compares the build with the committed tree
using `tools/compare_generated_tree.py`. Output of the S12b build:
`/nix/store/ra4gifmv5v62ixjrihr4xk1v2kc4a2qs-zesu-sail-riscv-lean-rv64-regenerated` (about 8 minutes,
7 of them the Lean generation).

The patches `01`, `02` were produced in a scratch worktree of the pinned commit
(`~/.cache/zesu-tmp/exec-spike/sail-riscv`, branch `zesu-spec`) with `git diff`.

## `00-sail-lean-asr.patch` (S12b)

The one `lib/vector.sail` hunk of upstream `rems-project/sail` commit
`895028208155d9a020b2e66d38dda4faddeea1da` ("Correct Lean asr builtin", 2026-02-25, first released
in Sail 0.20.2). Sail 0.20.1's library binds the builtin `sail_arith_shiftright` to
`BitVec.rotateRight` for the Lean backend, so the generated `shift_bits_right_arith` (sail-riscv's
`model/prelude/prelude.sail`, which calls `sail_arith_shiftright` correctly) rotated: `srai`,
`sra`, `sraiw`, `sraw` were rotations in the generated model (`OPEN/forms/Srai.lean` of S12). The
patch binds it to `BitVec.sshiftRight`. The defect is in the Sail compiler's library, not in
sail-riscv and not in `01`/`02`. The other C, OCaml, SMT backends were never affected
(`arith_shiftr`). The root-level `sailRiscvRegenerated` (`generated/sail-riscv-lean`, BinaryFv's
model) is built with the unpatched compiler and still has the rotation; it is outside exec-spike.

## Modules (S12b)

`Zba;Zbb;Zbs` are the `B_insts` submodules without `Zbc` (carry-less multiply, not used by the
target); `Zbkb` adds `pack`, `packh`, `packw`, `zip`, `unzip`, `brev8` (and enables `rev8`, `rol`,
`ror`, `andn`, `orn`, `xnor` through `currentlyEnabled(Ext_Zbkb)`). `01-profile-config.patch` is
unchanged: `extensions.B.supported` is true and `Zba`, `Zbb`, `Zbs` are enabled through `B`
(`currentlyEnabled(Ext_B) = hartSupports(Ext_B) & misa[B] == 0b1`), `Zbkb.supported` is true.
