{ pkgs }:
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

in
{
  inherit
    cflags
    commonCFlags
    lib
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
      echo "Run: nix run .#zesu-ssz, or nix run .#dump -- TARGET"
    '';
  };
}
