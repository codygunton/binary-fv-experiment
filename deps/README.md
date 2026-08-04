# Dependency source

This directory provides browsable working copies of external source that reviewers need beside the
verification code. Initialize them with:

```sh
git submodule update --init
```

`zesu/` is the repaired source used to build the decoder under verification. `zesu-upstream/` is the
unchanged production baseline. Their gitlinks match the revisions pinned independently in `flake.nix`
and `nix/targets.nix`.

The submodules are not build-output directories and are not an alternative build system. Nix fetches
the pinned revisions and owns all compilation and generated artifacts.
