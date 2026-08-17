{
  description = "Reproducible RV64 binary compliance proofs for SSZ";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    # Target and audit sources are pinned independently of the proof stack.
    # Preserve the unmodified upstream source for the production baseline.
    zesu = {
      url = "github:codygunton/zesu/d67f28c";
      flake = false;
    };

    sailRiscv = {
      url = "github:riscv/sail-riscv/65ddde80ee2b131bf46c20e6e748343c336c4071";
      flake = false;
    };

    evmSail = {
      url = "github:frisitano/evm-sail/d0e4aabdde52f9158d191dbc8add444abffd9a6a";
      flake = false;
    };

    evmSailCompiler = {
      url = "github:frisitano/sail/25cc260d9940d65d2e5da427fe4b5d402809a50c";
      flake = false;
    };

    leanSail = {
      url = "github:rems-project/lean-sail/79b4d08505af29d88b3918f32d29840fae1fa191";
      flake = false;
    };

  };

  outputs = {
    self,
    nixpkgs,
    zesu,
    sailRiscv,
    evmSail,
    evmSailCompiler,
    leanSail,
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
            inherit pkgs repo rv64 zesu;
          };
          analysis = import ./nix/analysis.nix {
            inherit pkgs rv64 targets;
          };
          proof = import ./nix/proof.nix {
            inherit leanSail pkgs repo rv64 sailRiscv;
            inherit (targets.public) zesuSszDecodeRv64Elf;
          };
          evmSailSpec = import ./nix/evm-sail.nix {
            inherit evmSail evmSailCompiler leanSail pkgs repo;
            inherit (proof.public) binaryFvLean;
            inherit (targets.public) zesuSszDecodeSmoke;
            inherit (analysis.public) zesuSszDecodeCfg zesuSszDecodeLevel1Manifest
              zesuSszDecodeLevel2Manifest;
          };
        in
        targets.public // analysis.public // proof.public // evmSailSpec.public;

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
            inherit pkgs repo rv64 zesu;
          };
          proof = import ./nix/proof.nix {
            inherit leanSail pkgs repo rv64 sailRiscv;
            inherit (targets.public) zesuSszDecodeRv64Elf;
          };
        in
        {
          default = proof.devShell;
        });
    };
}
