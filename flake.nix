{
  description = "Reproducible binary size probes for SHA-3 and miniz DEFLATE inflate";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    tiny-sha3 = {
      url = "github:mjosaarinen/tiny_sha3/dcbb3192047c2a721f5f851db591871d428036a9";
      flake = false;
    };

    miniz = {
      url = "github:richgel999/miniz/77d0dce8627735138c51770d1799a1ef48f2117d";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, tiny-sha3, miniz }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system:
          let
            pkgs = import nixpkgs { inherit system; };
          in
          f system pkgs);
    in
    {
      packages = forAllSystems (system: pkgs:
        let
          stats = pkgs.stdenvNoCC.mkDerivation {
            pname = "sha-fv-binary-stats";
            version = "0.1.0";
            src = self;

            nativeBuildInputs = [
              pkgs.gcc16
              pkgs.binutils
              pkgs.coreutils
              pkgs.gawk
              pkgs.gnugrep
              pkgs.gnused
              pkgs.zig
            ];

            hardeningDisable = [ "all" ];
            dontConfigure = true;
            dontBuild = true;

            installPhase = ''
              runHook preInstall

              mkdir -p "$out"
              export NIX_HARDENING_ENABLE=""
              export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
              export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
              SHA3_SRC=${tiny-sha3} \
              MINIZ_SRC=${miniz} \
              OUT_DIR="$out" \
              CC=gcc \
              ZIG=zig \
              SIZE=size \
              NM=nm \
              OBJDUMP=objdump \
              SOURCE_DATE_EPOCH=1 \
                ${pkgs.bash}/bin/bash ./scripts/measure.sh

              mkdir -p "$out/bin"
              cat > "$out/bin/show-stats" <<EOF
              #!${pkgs.runtimeShell}
              cat "$out/stats.md"
              EOF
              chmod +x "$out/bin/show-stats"

              runHook postInstall
            '';
          };
        in
        {
          inherit stats;
          default = stats;
        });

      checks = forAllSystems (system: pkgs: {
        stats = self.packages.${system}.stats;
        default = self.packages.${system}.stats;
      });

      apps = forAllSystems (system: pkgs: {
        stats = {
          type = "app";
          program = "${self.packages.${system}.stats}/bin/show-stats";
          meta.description = "Print the reproducible SHA-3/miniz binary size stats";
        };
        default = self.apps.${system}.stats;
      });

      devShells = forAllSystems (system: pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.gcc16
            pkgs.binutils
            pkgs.coreutils
            pkgs.gawk
            pkgs.gnugrep
            pkgs.gnused
            pkgs.zig
          ];

          shellHook = ''
            echo "Run: nix build .#stats && cat result/stats.md"
          '';
        };
      });
    };
}
