# Zesu validation tests and evidence generators

This directory contains the Python drivers and deterministic fixtures used to test Zesu and its
handwritten contracts. The contract-validation files are:

- [ssz_contract_agreement.py](ssz_contract_agreement.py) compares the Lean oracle runner and Zig
  source probe.
- [ssz_contract_corpus.py](ssz_contract_corpus.py) builds whole-input accept/reject examples.
- [ssz_contract_mutation.py](ssz_contract_mutation.py) corrupts expectations and coverage inputs to
  show that the checks can fail.
- [ssz_contract_report.py](ssz_contract_report.py) renders source function- and occurrence-level coverage as
  JSON and Markdown.
- [ssz_source_function_vectors.py](ssz_source_function_vectors.py) builds typed examples for all 43
  source-function identities, including expected values, errors, and allocation ledgers.

Expected allocation sequences are derived from fixture structure and compiler-reported element
layouts, independently of the decoder's observed allocator calls. Generated files must be
byte-identical across repeated runs; do not add timestamps, host addresses, or unordered output.

The remaining scripts cover differential behavior, output observability, generation, relocation,
and function-boundary checks. Validation results are test evidence; the proof import guard
prevents `BinaryFv.Zesu.Validation` modules from becoming premises of production proofs.
