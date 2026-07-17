# GitHub automation

`workflows/required-lightweight.yml` validates retained RV64 targets, SSZ conformance, and the root
Lean library after changes land on `main`. It intentionally does not run on pull requests: builders
and reviewers run those gates locally to avoid monopolizing organization runners.

`workflows/manual-zesu-heavyweight.yml` runs both full Zesu fixture suites and the extended boundary
corpus when manually dispatched for a release checkpoint.
