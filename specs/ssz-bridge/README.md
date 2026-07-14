# SSZ bridge

This Lean 4.29.1 project is a SizzLean-backed executable bridge for the
Amsterdam V4 `SszStatelessInput` schema. It checks schema `0x0001`, tries raw
SSZ before exact Ere length framing, and applies a canonical reserialization
check around SizzLean's executable decoder. Its output is the complete,
deterministic `ssz-value-v1` raw-value protocol.

Run the focused check from this directory:

```sh
lake build ssz_bridge_test
lake exe ssz_bridge_test
```

For a corpus fixture, `lake exe ssz_bridge path/to/input.ssz` prints either a
full `ssz-value-v1` record stream or an `error` classification. The bridge is
intentionally executable-only: the pinned SizzLean project has runnable
variable-offset decoding, but its `BasicSupported` proofs do not cover nested
mixed variable containers such as `SszStatelessInput`.

Layout constants are taken from pinned `ethereum/execution-specs`
`bd8c673552d957dbe9c9f3f2656b87201f5ae646`. V3 is structurally recognized
only and returns `v3_quarantined`: it has no independently pinned historical
oracle and is excluded from strict value-level conformance.

