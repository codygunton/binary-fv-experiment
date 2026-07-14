{ pkgs, source, repo }:
let
  lib = pkgs.lib;
  riscvPkgs = pkgs.pkgsCross.riscv64;
  riscvBinutils = riscvPkgs.buildPackages.binutils;
  riscvTargetPrefix = riscvPkgs.stdenv.cc.targetPrefix;
  riscvCc = "${riscvPkgs.stdenv.cc}/bin/${riscvTargetPrefix}gcc";
  riscvObjdump = "${riscvBinutils}/bin/${riscvTargetPrefix}objdump";
  riscvNm = "${riscvBinutils}/bin/${riscvTargetPrefix}nm";
  riscvReadelf = "${riscvBinutils}/bin/${riscvTargetPrefix}readelf";
  riscvSize = "${riscvBinutils}/bin/${riscvTargetPrefix}size";
  riscvAr = "${riscvBinutils}/bin/${riscvTargetPrefix}ar";
  qemuRiscv64 = "${pkgs.qemu-user}/bin/qemu-riscv64";
  riscvTarget = "RV64IM_Zicclsm";
  riscvArch = "rv64im_zicclsm";
  riscvAbi = "lp64";
  commonCFlags = [
    "-Os"
    "-g0"
    "-DNDEBUG"
    "-march=${riscvArch}"
    "-mabi=${riscvAbi}"
    "-ffreestanding"
    "-fno-builtin"
    "-ffunction-sections"
    "-fdata-sections"
    "-fno-asynchronous-unwind-tables"
    "-fno-unwind-tables"
    "-fno-stack-protector"
    "-fomit-frame-pointer"
    "-fno-pic"
    "-fno-pie"
  ];
  cflags = lib.concatStringsSep " " commonCFlags;

  mkBinary =
    { name
    , srcRoot
    , sourceFile
    , entrypoint
    , includes ? [ ]
    , extraCFlags ? [ ]
    , selectedSymbols
    }:
    pkgs.stdenvNoCC.mkDerivation {
      pname = "sha-fv-${name}-rv64im-zicclsm";
      version = "0.1.0";
      src = source;

      nativeBuildInputs = [
        riscvPkgs.stdenv.cc
        riscvBinutils
      ];

      hardeningDisable = [ "all" ];
      dontConfigure = true;
      dontBuild = true;
      dontFixup = true;

      installPhase =
        let
          includeFlags = lib.concatMapStringsSep " " (include: "-I${include}") includes;
          targetCFlags = lib.concatStringsSep " " (commonCFlags ++ extraCFlags);
        in
        ''
          runHook preInstall

          mkdir -p "$out/bin" "$out/obj" "$out/meta"
          export NIX_HARDENING_ENABLE=""

          ${riscvCc} ${targetCFlags} ${includeFlags} \
            -I${srcRoot} \
            -c ${srcRoot}/${sourceFile} \
            -o "$out/obj/${name}.o"

          ${riscvCc} ${targetCFlags} ${includeFlags} \
            -I${srcRoot} \
            -c ${entrypoint} \
            -o "$out/obj/${name}-main.o"

          ${riscvCc} ${cflags} \
            -c ${repo}/harness/riscv64_runtime.c \
            -o "$out/obj/riscv64_runtime.o"

          ${riscvCc} ${cflags} \
            -c ${repo}/harness/riscv64_start.S \
            -o "$out/obj/riscv64_start.o"

          ${riscvCc} ${cflags} -nostdlib -static -no-pie \
            "$out/obj/riscv64_start.o" \
            "$out/obj/${name}-main.o" \
            "$out/obj/${name}.o" \
            "$out/obj/riscv64_runtime.o" \
            -lgcc \
            -Wl,--gc-sections \
            -Wl,-e,_start \
            -o "$out/bin/${name}"

          printf '%s\n' ${lib.escapeShellArgs selectedSymbols} > "$out/meta/selected-symbols"
          ${riscvReadelf} -h "$out/bin/${name}" > "$out/meta/elf-header.txt"
          ${riscvReadelf} -A "$out/bin/${name}" > "$out/meta/elf-attributes.txt"

          runHook postInstall
        '';
    };
in
{
  inherit
    cflags
    commonCFlags
    lib
    mkBinary
    qemuRiscv64
    riscvAbi
    riscvAr
    riscvArch
    riscvBinutils
    riscvCc
    riscvNm
    riscvObjdump
    riscvPkgs
    riscvReadelf
    riscvSize
    riscvTarget
    riscvTargetPrefix;

  devShell = pkgs.mkShell {
    packages = [
      pkgs.coreutils
      pkgs.gawk
      pkgs.gnused
      pkgs.qemu-user
      riscvPkgs.stdenv.cc
      riscvBinutils
    ];
    shellHook = ''
      echo "Run: nix build .#sha3 --out-link build/sha3, nix run .#sha3, or nix run .#dump -- TARGET"
    '';
  };
}
