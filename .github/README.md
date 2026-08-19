# Automation

The required workflow compiles the reviewed Sail snapshots and runs all proof, evidence, binary, and
UI checks. It permits two Nix builds at one time. Both Sail generators remain outside this workflow.

The regeneration workflow runs each Sunday, on request, and when generator inputs or snapshots change.
Its two jobs regenerate EVM-Sail and Sail RISC-V on separate runners and compare complete source trees.

`act` needs a regular clone with initialized submodules. Nix sandboxing also requires a privileged
container. These commands reproduce both workflows locally:

```sh
act pull_request -W .github/workflows/required-lightweight.yml \
  --container-architecture linux/amd64 --container-options '--privileged'
act workflow_dispatch -W .github/workflows/generated-sail-regeneration.yml \
  --container-architecture linux/amd64 --container-options '--privileged'
```
