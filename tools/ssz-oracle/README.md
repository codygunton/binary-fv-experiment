# SSZ oracle tool

This Lean 4.29.1 tool compiles the project-owned `BinaryFv/Specs/SSZ` source against the full pinned
SizzLean package. It provides a command-line oracle and runs the target-independent specification
tests in `tests/Specs/SSZ`.

Run the focused check from this directory:

```sh
lake build ssz_oracle ssz_oracle_test
lake exe ssz_oracle_test
```

For a corpus fixture, `lake exe ssz_oracle path/to/input.ssz` prints either a
full `ssz-value-v1` record stream or an `error` classification. The oracle is
intentionally executable-only: the pinned SizzLean project has runnable
variable-offset decoding, but its `BasicSupported` proofs do not cover nested
mixed variable containers such as `SszStatelessInput`.

Layout constants are taken from pinned `ethereum/execution-specs`
`bd8c673552d957dbe9c9f3f2656b87201f5ae646`. V3 is structurally recognized
only and returns `v3_quarantined`: it has no independently pinned historical
oracle and is excluded from strict value-level conformance.
