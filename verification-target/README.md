# Verification targets

A verification target is one concrete implementation presented to BinaryFv for verification. Each
subdirectory contains the repository-owned integration material for that implementation: its adapter,
ABI extraction program, binary-facing tests, and documentation connecting its native data
representation to the reusable specification.

This directory does not contain dependency source or build output. Pinned external source enters
through `flake.nix`; Nix places build products in the store, and optional local output links belong
under the ignored `build/` directory.

`zesu/` presents the pinned Zesu Amsterdam V4 decoder as a verification target. Reusable specifications belong in
`BinaryFv/Specs/`; shared freestanding support belongs in `runtime/`; and generic verification
infrastructure belongs in `BinaryFv/`.
