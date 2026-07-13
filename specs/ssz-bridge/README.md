# SSZ bridge

This Lean 4.29.1 project is an executable normalization bridge for the raw
Zesu SSZ candidate. It checks schema `0x0001`, optional Ere length framing,
top-level and nested canonical offset tables, relevant execution-spec bounds,
and the V3/V4 execution-payload split. Its output is acceptance metadata, not
a decoded value serialization.

Run the focused check from this directory:

```sh
lake build ssz_bridge_test
lake exe ssz_bridge_test
```

For a corpus fixture, `lake exe ssz_bridge path/to/input.ssz` prints either
an `ok` normalization record or an `error` classification. The bridge is
intentionally executable-only: the pinned SizzLean project has runnable
variable-offset decoding, but its `BasicSupported` proofs do not cover nested
mixed variable containers such as `SszStatelessInput`. The candidate's raw ABI
also exposes only acceptance, so this project cannot establish value-level
equivalence without a separate normalized-projection ABI on the Zesu side.

Layout constants are taken from pinned sources: `Consensys/zesu`
`aa6c94339987d278acb8b7fa409c864dbd3d05aa` and `ethereum/execution-specs`
`bd8c673552d957dbe9c9f3f2656b87201f5ae646`. The latter provides the V4
Amsterdam reference; V3 needs an additional historical oracle pin.
