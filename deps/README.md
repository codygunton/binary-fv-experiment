# Dependency sources

`zesu/` is authentic Consensys Zesu at zkevm v0.6.2. `evm-sail/` is the version-matched executable
EVM/SSZ model whose Sail Lean extraction is the candidate specification. Initialize both with
`git submodule update --init`; Nix independently fetches the same revisions and owns all builds.
