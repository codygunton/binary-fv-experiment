# EVM-Sail as the stateless-input SSZ specification

## Verdict

Use EVM-Sail `d0e4aabd` with authentic Zesu `d8071c4`. Both revisions target
zkevm v0.6.2. The generated Lean is executable and contains enough of the SSZ
decoder to state a direct refinement theorem; the remaining mismatches are
finite, explicit candidates for `hKnownBugs`, not a different core schema.

The older EVM-Sail `cd48390` is a worse proof target. Its three-request schema
is closer to zkevm v0.5.0, but its Lean extraction leaves input reads as host
axioms. The selected current extraction instead supplies a concrete `HostState`
and executable region-access definitions.

## Reproducible extraction

`nix/evm-sail.nix` pins all three moving parts:

- EVM-Sail `d0e4aabdde52f9158d191dbc8add444abffd9a6a`;
- its required custom Sail compiler
  `25cc260d9940d65d2e5da427fe4b5d402809a50c`;
- lean-sail `79b4d08505af29d88b3918f32d29840fae1fa191`
  and Lean 4.29.0.

`nix build .#evmSailLeanExtraction` builds all 76 reviewed generated Lean modules and runs
`tests/evm-sail/DecodeSmoke.lean`. The smoke test executes the extracted
decoder on a minimal 666-byte Amsterdam envelope and on a schema-byte mutation;
the first succeeds and the mutation fails.

The regenerated source differs from EVM-Sail's checked-in extraction only in
one compiler-generated existential-name sequence in
`Evm/Lib/Ssz/StatelessInput.lean`; declarations and executable behavior are
unchanged. `nix build .#evmSailLeanRegenerationCheck` regenerates the model from
`sail/evm.sail_project` and requires exact agreement with the reviewed snapshot.

## Lean specification surface

The authoritative generated definitions are:

- `Evm.Functions.decode_stateless_input_ref`: validates the two-byte schema,
  every container offset, the 540-byte Amsterdam payload, five execution-request
  fields, bounded witness lists, and public-key packing; malformed input throws
  `InvalidConfig` in `Evm.SailM`.
- `Evm.Functions.decode_stateless_input`: decodes the block header and chain
  configuration, checks that the configured fork activation has been reached,
  and returns the semantic `StatelessInput` while installing the decoded header
  and chain id in model state.

`Evm.SailM` is `StateT HostState` over the generated Sail machine monad.
`HostState.inputBytes` and the stateless-input region operations are concrete
Lean definitions. The only native opaque accelerator in `HostAxioms.lean` is
outside the SSZ decode path.

This supports a relation such as `SailDecode bytes result`, defined by running
the two generated functions from `initialHostState` with `inputBytes = bytes`.
It does not require restating SSZ in this repository.

## Revision match with Zesu

Authentic Zesu `d8071c4` identifies itself as glamsterdam-devnet v7.2.0 /
zkevm v0.6.2. Its decoder and the selected Sail model agree on the central
layout:

- schema byte plus revision byte `0x01`;
- four top-level variable fields after the two-byte schema;
- 44-byte `SszNewPayloadRequest` fixed region;
- 540-byte Amsterdam `SszExecutionPayload` fixed region;
- five execution-request offset fields, including builder deposits and exits;
- 12-byte execution-witness offset table;
- packed 65-byte public keys;
- fork identity selected by the first schema byte.

## Exact divergence candidates

These must be represented by named fields of `KnownBugs`, or eliminated by
narrowing the theorem's input relation. `hKnownBugs` must not be an arbitrary
result-equivalence oracle.

1. **Ere framing.** Zesu optionally strips a four-byte little-endian length
   prefix before decoding. EVM-Sail consumes the raw SSZ bytes. Prefer proving a
   wrapper lemma that relates the framed Zesu input to the unframed Sail input;
   this is an interface difference, not an SSZ semantic bug.
2. **Zero chain id.** Zesu returns chain id `1` when the encoded value is `0`;
   EVM-Sail preserves the encoded `0`. This is a genuine semantic divergence
   and the first concrete `hKnownBugs` clause.
3. **Legacy request count.** Zesu accepts request tables with three or more
   fields; EVM-Sail v0.6.2 requires exactly the five-field, 20-byte table. This
   does not affect refinement on Sail-accepted inputs, but it is a divergence
   for an all-input accept/reject theorem.
4. **Legacy payload.** Zesu also accepts the older 528-byte V3 payload;
   EVM-Sail requires the 540-byte Amsterdam payload. This has the same theorem
   consequence as legacy request counts.
5. **Fork activation validation.** EVM-Sail requires a well-formed nonempty
   activation and rejects a payload before its activation point. Zesu parses
   activation fields leniently and does not perform that full check in its SSZ
   decoder. Sail-valid inputs still give both decoders the same activation
   values; invalid-input behavior differs.
6. **Protocol bounds.** EVM-Sail checks the declared maximum sizes of lists and
   byte lists. Zesu performs the structural checks needed by its allocations
   but does not mirror every model bound at decode time. These are additional
   invalid-input acceptance cases to enumerate before stating total behavior.

## Theorem shape

Keep `root_compliance` as the unique public theorem, but replace the Etheorem
parameterization with a generated EVM-Sail decode relation. Its sole temporary
premise should be a concrete structure such as:

```lean
structure KnownBugs where
  chainIdZeroNormalization : ChainIdZeroDivergence targetDecode sailDecode
  legacyInputAcceptance : LegacyAcceptanceDivergence targetDecode sailDecode
```

The framing lemma should normally sit outside `KnownBugs`. Each remaining field
must name one reviewed divergence and be removable when Zesu is fixed or the
theorem domain is made precise. The theorem should not assume that arbitrary
Zesu and Sail results agree.

## Go/no-go gate

This is a **go** for replacing Etheorem and the grafted decoder, subject to one
next-PR requirement: define the executable `SailDecode` wrapper and
machine-check the matched-schema and divergence fixtures against both Zesu
`d8071c4` and the extracted Lean before rebuilding the binary proof hierarchy.
