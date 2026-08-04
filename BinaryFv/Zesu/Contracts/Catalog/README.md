# Contract catalog

The catalog assigns one source-level contract to each stable Zesu source-function identity. It does
not contain compiled addresses; the generated Elfling program may bind the same catalog entry to
several emitted or inlined function instances.

- `Entries.lean` declares the source identities, contract tags, source hashes, exclusions, and required
  generic specializations.
- `Dispatch.lean` turns a tag and a concrete function instance into the corresponding typed machine
  obligation.
- `Validation.lean` states bidirectional coverage, unique dispatch, exclusion, specialization, and
  semantic obligations.

`../Catalog.lean` is the umbrella import. `../CatalogAudit.lean` proves concrete structural checks on
the catalog; semantic proofs live in `../SemanticObligations.lean`.
