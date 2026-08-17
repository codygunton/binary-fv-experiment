# Decoded values

`Representation.lean` relates the native Zig heap graph at a successful decoder return to the
semantic Zesu decoded result. `Encoder.lean` defines the versioned `ZSSZ` observation encoding for
compositional encoder contracts, and `CodecRoundtrip.lean` proves the represented encodings parse
back to the same semantic values used by the Level 1 success-writer proof.
