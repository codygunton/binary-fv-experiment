# Verification targets

A verification target is one concrete implementation presented to BinaryFv for verification. Each
subdirectory contains the repository-owned integration material for that implementation: its adapter,
ABI extraction program, binary-facing tests, and documentation connecting its native data
representation to the reusable specification.

This directory does not contain dependency source or build output. Pinned external source enters
through `flake.nix`; Nix places build products in the store, and optional local output links belong
under the ignored `build/` directory.

No active adapter is committed during the upstream pivot. The next adapter will link the authentic
`deps/zesu` RV64 object, define its concrete entry ABI, and connect it to the extracted EVM-Sail
stateless-input semantics. Generic verification infrastructure remains in `BinaryFv/`.
