# Amsterdam V4 SSZ specification

This directory contains the project-owned executable specification used to judge binary decoders.
It is independent of Zesu: another decoder can be proved against the same definitions.

- `AmsterdamV4.lean` defines the schema, limits, raw logical values, canonical decoding, and outer
  framing for Ethereum's Amsterdam V4 stateless input.
- `Decode.lean` exposes the observable accepted-value-or-rejected result used by root compliance
  theorems.

The generic SSZ interpreter is the pinned external SizzLean dependency. Nix stages only the pure
SizzLean modules required by the proof; it does not copy project-owned specification source.
