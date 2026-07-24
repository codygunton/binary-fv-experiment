# Zesu validation tests and evidence generators

This directory contains the Python drivers and deterministic fixtures used by the Zesu validation
lanes. The main Row B files are:

- `ssz_contract_corpus.py`: builds whole-input accept/reject examples.
- `ssz_routine_vectors.py`: builds typed examples for all 43 routine identities, including expected
  values, errors, and allocation ledgers.
- `ssz_contract_agreement.py`: compares the Lean oracle runner and Zig source probe.
- `ssz_contract_mutation.py`: corrupts one expectation at a time to show that the checks can fail.
- `ssz_contract_report.py`: renders routine- and occurrence-level coverage as JSON and Markdown.

Expected allocation sequences are derived from fixture structure and compiler-reported element
layouts, independently of the decoder's observed allocator calls. Generated files must be
byte-identical across repeated runs; do not add timestamps, host addresses, or unordered output.

Other files in this directory cover differential tests, binary evidence, and later proof rows. Their
generated artifacts are validation evidence and are never imported as premises by the root theorem.
