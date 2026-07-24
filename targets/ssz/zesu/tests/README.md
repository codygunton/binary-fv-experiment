# Zesu validation tests and evidence generators

This directory contains the Python drivers and deterministic fixtures used by the Zesu validation
lanes. Start with these Row B files:

- [ssz_contract_corpus.py](ssz_contract_corpus.py) builds whole-input accept/reject examples.
- [ssz_routine_vectors.py](ssz_routine_vectors.py) builds typed examples for all 43 routine
  identities, including expected values, errors, and allocation ledgers.
- [ssz_contract_agreement.py](ssz_contract_agreement.py) compares the Lean oracle runner and Zig
  source probe.
- [ssz_contract_mutation.py](ssz_contract_mutation.py) corrupts expectations and coverage inputs to
  show that the checks can fail.
- [ssz_contract_report.py](ssz_contract_report.py) renders routine- and function-instance-level coverage as
  JSON and Markdown.

Expected allocation sequences are derived from fixture structure and compiler-reported element
layouts, independently of the decoder's observed allocator calls. Generated files must be
byte-identical across repeated runs; do not add timestamps, host addresses, or unordered output.

The remaining scripts cover differential, observability, generator, relocation, and boundary
checks inherited from earlier work. Validation results are test evidence; the proof import guard
prevents `BinaryFv.SSZ.Zesu.Validation` modules from becoming premises of production proofs.
