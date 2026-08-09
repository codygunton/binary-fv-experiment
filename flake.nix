{
  description = "Reproducible RV64 binary compliance proofs for SSZ";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    # Target and audit sources are pinned independently of the proof stack.
    # Preserve the unmodified upstream source for the production baseline.
    zesu = {
      url = "github:Consensys/zesu/aa6c94339987d278acb8b7fa409c864dbd3d05aa";
      flake = false;
    };

    # The selected lossless Amsterdam V4 decoder lives in the user's repaired fork.
    zesuRepaired = {
      url = "github:codygunton/zesu/96f1621468ba54755d653f19cbc9704e789be001";
      flake = false;
    };

    sailRiscv = {
      url = "github:riscv/sail-riscv/65ddde80ee2b131bf46c20e6e748343c336c4071";
      flake = false;
    };

    etheorem = {
      url = "github:etheorem/etheorem/032ab6c6d67186ba60b734e0f2c44ba1bb8b6fb0";
      flake = false;
    };

    executionSpecs = {
      url = "github:ethereum/execution-specs/bd8c673552d957dbe9c9f3f2656b87201f5ae646";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    zesu,
    zesuRepaired,
    sailRiscv,
    etheorem,
    executionSpecs,
  }:
    let
      repo = ./.;
      systems = [ "x86_64-linux" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system:
          let
            pkgs = import nixpkgs { inherit system; };
          in
          f system pkgs);

      packagesFor = system: pkgs:
        let
          rv64 = import ./nix/riscv.nix {
            inherit pkgs;
          };
          targets = import ./nix/targets.nix {
            inherit pkgs repo rv64 zesu zesuRepaired;
            source = self;
          };
          analysis = import ./nix/analysis.nix {
            inherit pkgs repo rv64 targets;
          };
          proof = import ./nix/proof.nix {
            inherit etheorem executionSpecs pkgs repo rv64 sailRiscv targets;
          };
        in
        targets.public // analysis.public // proof.public;

      outputsFor = system: pkgs:
        import ./nix/checks.nix {
          packages = self.packages.${system};
        };
    in
    {
      packages = forAllSystems packagesFor;

      checks = forAllSystems (system: pkgs:
        (outputsFor system pkgs).checks);

      apps = forAllSystems (system: pkgs:
        (outputsFor system pkgs).apps);

      devShells = forAllSystems (system: pkgs:
        let
          rv64 = import ./nix/riscv.nix {
            inherit pkgs;
          };
          targets = import ./nix/targets.nix {
            inherit pkgs repo rv64 zesu zesuRepaired;
            source = self;
          };
          proof = import ./nix/proof.nix {
            inherit etheorem executionSpecs pkgs repo rv64 sailRiscv targets;
          };
        in
        {
          default = proof.devShell;
        });
    };
}
