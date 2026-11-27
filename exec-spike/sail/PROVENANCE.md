# Provenance of `exec-spike/sail-riscv-lean`

| Input | Value |
|---|---|
| sail-riscv | `riscv/sail-riscv` commit `65ddde80ee2b131bf46c20e6e748343c336c4071` (release 0.12) |
| lean-sail runtime | `rems-project/lean-sail` rev `79b4d08505af29d88b3918f32d29840fae1fa191` |
| nixpkgs (`flake.lock`) | `NixOS/nixpkgs` rev `f205b5574fd0cb7da5b702a2da51507b7f4fdd1b` (Sail compiler: `pkgs.ocamlPackages.sail`) |
| Sail modules | `main;I_insts;M_insts`, target `generated_lean_executable_rv64d` |
| `01-profile-config.patch` | sha256 `b0cebad68e9574052d83dbf3a14628337ab4a8c12c03c7c83c1607133900d938` |
| `02-specialise.patch` | sha256 `d06cf8aedb93636bf1b4a65ce8243e08826dc731d0ac4a1d415ef143e5d9e7dc` |

Build: `nix build -L .#zesuSailRiscvLean` (derivations `zesuSailRiscvRaw`, `zesuSailRiscvLean` in
`nix/proof.nix`: the stock `sailRiscvRegeneratedRaw` with `patches` set, and the stock runtime
swap). Check: `nix build -L .#zesuSailRiscvLeanRegenerationCheck` compares the build with the
committed tree using `tools/compare_generated_tree.py`.

The patches were produced in a scratch worktree of the pinned commit
(`~/.cache/zesu-tmp/exec-spike/sail-riscv`, branch `zesu-spec`) with `git diff`.
