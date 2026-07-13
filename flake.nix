{
  description = "Reproducible binary size comparison for SHA-3 and miniz DEFLATE inflate";

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

    sail-riscv = {
      url = "github:riscv/sail-riscv/65ddde80ee2b131bf46c20e6e748343c336c4071";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, tiny-sha3, miniz, sail-riscv }:
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
          lib = pkgs.lib;
          riscvPkgs = pkgs.pkgsCross.riscv64;
          riscvBinutils = riscvPkgs.buildPackages.binutils;
          riscvTargetPrefix = riscvPkgs.stdenv.cc.targetPrefix;
          riscvCc = "${riscvPkgs.stdenv.cc}/bin/${riscvTargetPrefix}gcc";
          riscvObjdump = "${riscvBinutils}/bin/${riscvTargetPrefix}objdump";
          riscvNm = "${riscvBinutils}/bin/${riscvTargetPrefix}nm";
          riscvReadelf = "${riscvBinutils}/bin/${riscvTargetPrefix}readelf";
          riscvSize = "${riscvBinutils}/bin/${riscvTargetPrefix}size";
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
          sha3SampleMessage = "sha3-sample-message";
          sha3SampleDigest = "f8b2abe65645474af551ae4523f3c5948d9897c9f46c08a390ef88d6777507ba";

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
              src = self;

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
                    -c ${./harness/riscv64_runtime.c} \
                    -o "$out/obj/riscv64_runtime.o"

                  ${riscvCc} ${cflags} \
                    -c ${./harness/riscv64_start.S} \
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
                  sha256sum "$out/bin/${name}" | cut -d ' ' -f 1 > "$out/meta/elf-sha256.txt"
                  ${riscvReadelf} -h "$out/bin/${name}" > "$out/meta/elf-header.txt"
                  ${riscvReadelf} -h "$out/bin/${name}" |
                    awk '/Entry point address:/ { print $4 }' > "$out/meta/entrypoint.txt"
                  ${riscvReadelf} -A "$out/bin/${name}" > "$out/meta/elf-attributes.txt"
                  ${riscvReadelf} -lW "$out/bin/${name}" > "$out/meta/program-headers.txt"
                  ${riscvNm} -n --defined-only "$out/bin/${name}" > "$out/meta/symbols.txt"

                  runHook postInstall
                '';
            };

          sha3 = mkBinary {
            name = "sha3";
            srcRoot = tiny-sha3;
            sourceFile = "sha3.c";
            entrypoint = ./harness/sha3.c;
            selectedSymbols = [
              "sha3_keccakf"
              "sha3_init"
              "sha3_update"
              "sha3_final"
              "sha3"
              "main"
            ];
          };

          sha3ElfLean = pkgs.runCommand "sha-fv-sha3-elf-lean" {
            nativeBuildInputs = [
              pkgs.coreutils
              pkgs.gawk
            ];
          } ''
            mkdir -p "$out"
            {
              printf '%s\n' 'namespace ShaFv.SHA3.Artifact'
              printf '\n'
              printf '%s\n' '/-- Generated from the canonical Nix-built RV64 SHA-3 ELF. -/'
              printf '%s\n' 'def bytes : ByteArray := ByteArray.mk #['
              ${pkgs.coreutils}/bin/od -An -v -tu1 ${sha3}/bin/sha3 |
                ${pkgs.gawk}/bin/awk '
                  {
                    for (i = 1; i <= NF; i++) {
                      if (count % 12 == 0) {
                        printf "  "
                      }
                      printf "0x%02x, ", $i
                      count++
                      if (count % 12 == 0) {
                        printf "\n"
                      }
                    }
                  }
                  END {
                    if (count % 12 != 0) {
                      printf "\n"
                    }
                  }
                '
              printf '%s\n' ']'
              printf '\n'
              printf '%s\n' 'end ShaFv.SHA3.Artifact'
            } > "$out/Sha3Elf.lean"
          '';

          tinfl = mkBinary {
            name = "tinfl";
            srcRoot = miniz;
            sourceFile = "miniz_tinfl.c";
            entrypoint = ./harness/tinfl.c;
            includes = [ ./include ];
            extraCFlags = [
              "-DMINIZ_NO_TIME"
              "-DMINIZ_NO_STDIO"
              "-DMINIZ_NO_MALLOC"
              "-DMINIZ_NO_ARCHIVE_APIS"
              "-DMINIZ_NO_DEFLATE_APIS"
              "-DMINIZ_NO_ZLIB_COMPATIBLE_NAMES"
            ];
            selectedSymbols = [
              "tinfl_decompress"
              "tinfl_decompress_mem_to_mem"
              "main"
            ];
          };

          stats = pkgs.stdenvNoCC.mkDerivation {
            pname = "sha-fv-binary-stats-rv64im-zicclsm";
            version = "0.1.0";

            nativeBuildInputs = [
              pkgs.coreutils
              pkgs.gawk
              pkgs.gnused
              pkgs.qemu-user
              riscvBinutils
            ];

            dontUnpack = true;
            dontConfigure = true;
            dontBuild = true;
            dontFixup = true;

            installPhase = ''
              runHook preInstall

              mkdir -p "$out/bin" "$out/rv64/bin" "$out/rv64/obj" "$out/rv64/meta" "$out/objdump"

              cp ${sha3}/bin/sha3 "$out/rv64/bin/sha3"
              cp ${sha3}/obj/sha3.o "$out/rv64/obj/sha3.o"
              cp ${sha3}/obj/sha3-main.o "$out/rv64/obj/sha3-main.o"
              cp ${sha3}/meta/elf-attributes.txt "$out/rv64/meta/sha3-elf-attributes.txt"

              cp ${tinfl}/bin/tinfl "$out/rv64/bin/tinfl"
              cp ${tinfl}/obj/tinfl.o "$out/rv64/obj/tinfl.o"
              cp ${tinfl}/obj/tinfl-main.o "$out/rv64/obj/tinfl-main.o"
              cp ${tinfl}/meta/elf-attributes.txt "$out/rv64/meta/tinfl-elf-attributes.txt"

              count_symbol_instructions() {
                local file="$1"
                local symbol="$2"
                ${riscvObjdump} -d --disassemble="$symbol" "$file" |
                  awk '/^[[:space:]]+[0-9a-f]+:/ { n++ } END { print n + 0 }'
              }

              selected_instruction_total() {
                local file="$1"
                local symbols_file="$2"
                local total=0
                local count
                local symbol
                while IFS= read -r symbol; do
                  count="$(count_symbol_instructions "$file" "$symbol")"
                  total=$((total + count))
                done < "$symbols_file"
                printf '%s\n' "$total"
              }

              branchish_total() {
                local file="$1"
                local symbols_file="$2"
                local tmp
                tmp="$(mktemp)"
                local symbol
                while IFS= read -r symbol; do
                  ${riscvObjdump} -d --disassemble="$symbol" "$file" >> "$tmp"
                done < "$symbols_file"
                awk '
                  /^[[:space:]]+[0-9a-f]+:/ {
                    nfields = split($0, tabbed, "\t")
                    instr = tabbed[nfields]
                    sub(/^[[:space:]]+/, "", instr)
                    split(instr, a, /[[:space:]]+/)
                    m = a[1]
                    if (m ~ /^b/) branch++
                    else if (m == "j" || m == "jr" || m == "jal" || m == "jalr") branch++
                    else if (m == "call" || m == "tail") call++
                    else if (m == "ret") ret++
                  }
                  END { print branch + call + ret + 0 }
                ' "$tmp"
                rm -f "$tmp"
              }

              text_size() {
                ${riscvSize} "$1" | awk 'NR == 2 { print $1 }'
              }

              file_size() {
                stat -c '%s' "$1"
              }

              objdump_line_count() {
                ${riscvObjdump} -d "$1" | wc -l | awk '{ print $1 }'
              }

              objdump_instruction_line_count() {
                ${riscvObjdump} -d "$1" |
                  awk '/^[[:space:]]+[0-9a-f]+:/ { n++ } END { print n + 0 }'
              }

              ${riscvObjdump} -d "$out/rv64/bin/sha3" > "$out/objdump/sha3.txt"
              ${riscvObjdump} -d "$out/rv64/bin/tinfl" > "$out/objdump/tinfl.txt"

              sha3_object_text="$(text_size "$out/rv64/obj/sha3.o")"
              tinfl_object_text="$(text_size "$out/rv64/obj/tinfl.o")"
              sha3_linked_text="$(text_size "$out/rv64/bin/sha3")"
              tinfl_linked_text="$(text_size "$out/rv64/bin/tinfl")"

              sha3_selected_instrs="$(
                selected_instruction_total "$out/rv64/bin/sha3" ${sha3}/meta/selected-symbols
              )"
              tinfl_selected_instrs="$(
                selected_instruction_total "$out/rv64/bin/tinfl" ${tinfl}/meta/selected-symbols
              )"
              sha3_branchish="$(branchish_total "$out/rv64/bin/sha3" ${sha3}/meta/selected-symbols)"
              tinfl_branchish="$(branchish_total "$out/rv64/bin/tinfl" ${tinfl}/meta/selected-symbols)"
              sha3_objdump_lines="$(objdump_line_count "$out/rv64/bin/sha3")"
              tinfl_objdump_lines="$(objdump_line_count "$out/rv64/bin/tinfl")"
              sha3_objdump_instr_lines="$(objdump_instruction_line_count "$out/rv64/bin/sha3")"
              tinfl_objdump_instr_lines="$(objdump_instruction_line_count "$out/rv64/bin/tinfl")"

              sha3_output="$(${qemuRiscv64} "$out/rv64/bin/sha3" ${lib.escapeShellArg sha3SampleMessage})"
              if [ "$sha3_output" != "${sha3SampleDigest}" ]; then
                echo "unexpected SHA-3 digest for ${sha3SampleMessage}: $sha3_output" >&2
                exit 1
              fi
              ${qemuRiscv64} "$out/rv64/bin/tinfl"

              ${riscvSize} \
                "$out/rv64/obj/sha3.o" \
                "$out/rv64/obj/tinfl.o" \
                "$out/rv64/bin/sha3" \
                "$out/rv64/bin/tinfl" > "$out/size.txt"

              ${riscvNm} -S --size-sort --radix=d \
                "$out/rv64/obj/sha3.o" \
                "$out/rv64/obj/tinfl.o" \
                "$out/rv64/bin/sha3" \
                "$out/rv64/bin/tinfl" > "$out/symbols.txt"

              {
                echo "tool,value"
                printf 'target,%s\n' '${riscvTarget}'
                printf 'march,%s\n' '${riscvArch}'
                printf 'mabi,%s\n' '${riscvAbi}'
                printf 'cc,%s\n' "$(${riscvCc} --version | head -n 1)"
                printf 'size,%s\n' "$(${riscvSize} --version | head -n 1)"
                printf 'nm,%s\n' "$(${riscvNm} --version | head -n 1)"
                printf 'objdump,%s\n' "$(${riscvObjdump} --version | head -n 1)"
                printf 'qemu,%s\n' "$(${qemuRiscv64} --version | head -n 1)"
              } > "$out/toolchain.csv"

              cat > "$out/stats.tsv" <<EOF
              target	arch	object_text	linked_text	selected_symbol_instructions	branchish	linked_objdump_lines	linked_objdump_instruction_lines	file_size_object	file_size_linked
              sha3	${riscvTarget}	$sha3_object_text	$sha3_linked_text	$sha3_selected_instrs	$sha3_branchish	$sha3_objdump_lines	$sha3_objdump_instr_lines	$(file_size "$out/rv64/obj/sha3.o")	$(file_size "$out/rv64/bin/sha3")
              tinfl	${riscvTarget}	$tinfl_object_text	$tinfl_linked_text	$tinfl_selected_instrs	$tinfl_branchish	$tinfl_objdump_lines	$tinfl_objdump_instr_lines	$(file_size "$out/rv64/obj/tinfl.o")	$(file_size "$out/rv64/bin/tinfl")
              EOF

              cat > "$out/stats.md" <<EOF
              # Binary Size Stats

              ## Inputs

              - SHA-3: \`mjosaarinen/tiny_sha3\` at \`dcbb3192047c2a721f5f851db591871d428036a9\`
              - DEFLATE: \`richgel999/miniz\` at \`77d0dce8627735138c51770d1799a1ef48f2117d\`

              ## Toolchain

              \`\`\`text
              target ${riscvTarget}
              march ${riscvArch}
              mabi ${riscvAbi}
              $(${riscvCc} --version | head -n 1)
              $(${riscvSize} --version | head -n 1)
              $(${qemuRiscv64} --version | head -n 1)
              \`\`\`

              ## ${riscvTarget}

              | Target | Object \`.text\` | Linked \`.text\` | Selected symbol instrs | Branch/call/ret-ish | Full \`objdump -d\` lines | Full instr lines |
              |---|---:|---:|---:|---:|---:|---:|
              | \`tiny_sha3/sha3.c\` | $sha3_object_text B | $sha3_linked_text B | $sha3_selected_instrs | $sha3_branchish | $sha3_objdump_lines | $sha3_objdump_instr_lines |
              | \`miniz/miniz_tinfl.c\` | $tinfl_object_text B | $tinfl_linked_text B | $tinfl_selected_instrs | $tinfl_branchish | $tinfl_objdump_lines | $tinfl_objdump_instr_lines |

              “Selected symbol instrs” counts disassembled instruction lines only in these linked-ELF symbols:
              \`sha3_keccakf\`, \`sha3_init\`, \`sha3_update\`, \`sha3_final\`, \`sha3\`, and \`main\` for SHA-3;
              \`tinfl_decompress\`, \`tinfl_decompress_mem_to_mem\`, and \`main\` for DEFLATE. The full
              \`objdump -d\` columns count each entire RV64IM_Zicclsm linked ELF, including the local
              freestanding startup/runtime sections.

              ## Sanity

              SHA-3 was run under \`qemu-riscv64\` with message \`${sha3SampleMessage}\` and produced
              \`${sha3SampleDigest}\`. The \`tinfl\` binary also ran successfully under \`qemu-riscv64\`.

              Raw \`size\` output is in \`size.txt\`, symbol sizes are in \`symbols.txt\`, RV64 linked
              \`objdump -d\` output is in \`objdump/sha3.txt\` and \`objdump/tinfl.txt\`, ELF attributes
              are in \`rv64/meta/\`, and machine-readable summary data is in \`stats.tsv\`.
              EOF

              cat > "$out/bin/show-stats" <<EOF
              #!${pkgs.runtimeShell}
              cat "$out/stats.md"
              EOF
              chmod +x "$out/bin/show-stats"

              runHook postInstall
            '';
          };

          sha3Run = pkgs.writeShellApplication {
            name = "sha3";
            runtimeInputs = [ pkgs.qemu-user ];
            text = ''
              exec qemu-riscv64 ${sha3}/bin/sha3 "$@"
            '';
          };

          tinflRun = pkgs.writeShellApplication {
            name = "tinfl";
            runtimeInputs = [ pkgs.qemu-user ];
            text = ''
              exec qemu-riscv64 ${tinfl}/bin/tinfl "$@"
            '';
          };

          dump = pkgs.writeShellApplication {
            name = "dump";
            text = ''
              exec ${riscvObjdump} -d ${sha3}/bin/sha3
            '';
          };

          sailRiscvLean = pkgs.stdenv.mkDerivation {
            pname = "sail-riscv-lean-rv64";
            version = "0.12";
            src = sail-riscv;

            nativeBuildInputs = [
              pkgs.cmake
              pkgs.ninja
              pkgs.ocamlPackages.sail
              pkgs.pkg-config
              pkgs.z3
            ];
            buildInputs = [ pkgs.gmp ];

            postPatch = ''
              substituteInPlace handwritten_support/RiscvExtrasExecutable.lean \
                --replace-fail 'import Sail.Sail' \
                'import LeanRV64DExecutable.Sail.Sail'

              find model -name '*.sail' -type f -exec sed -i \
                -e 's/\<Vector\>/VectorPayload/g' \
                -e 's/"VectorPayload"/"Vector"/g' {} +

              substituteInPlace model/postlude/insts_end.sail \
                --replace-fail '// End definitions' \
                $'// Omitted optional modules are disabled in the RV64IM model.\nfunction clause currentlyEnabled(_) = false\n\n// End definitions'
            '';

            cmakeFlags = [
              "-DDOWNLOAD_CLI11=OFF"
              "-DDOWNLOAD_JSONCONS=OFF"
              "-DSAIL_MODULES=main;I_insts;M_insts"
            ];

            buildPhase = ''
              runHook preBuild
              cmake --build . --target generated_lean_executable_rv64d
              runHook postBuild
            '';

            installPhase = ''
              runHook preInstall
              cp -r model/Lean_RV64D_executable "$out"
              runHook postInstall
            '';
          };
        in
        {
          inherit sha3 tinfl stats dump sha3Run tinflRun;
          "sha3-elf-lean" = sha3ElfLean;
          "sail-riscv-lean" = sailRiscvLean;
          default = stats;
        });

      checks = forAllSystems (system: pkgs: {
        inherit (self.packages.${system}) sha3 tinfl stats dump;
        "sha3-elf-lean" = self.packages.${system}."sha3-elf-lean";
        "sail-riscv-lean" = self.packages.${system}."sail-riscv-lean";
        default = self.packages.${system}.stats;
      });

      apps = forAllSystems (system: pkgs: {
        sha3 = {
          type = "app";
          program = "${self.packages.${system}.sha3Run}/bin/sha3";
          meta.description = "Run the RV64IM_Zicclsm SHA-3 binary under qemu-riscv64";
        };
        tinfl = {
          type = "app";
          program = "${self.packages.${system}.tinflRun}/bin/tinfl";
          meta.description = "Run the RV64IM_Zicclsm miniz tinfl binary under qemu-riscv64";
        };
        stats = {
          type = "app";
          program = "${self.packages.${system}.stats}/bin/show-stats";
          meta.description = "Print the reproducible SHA-3/miniz RV64IM_Zicclsm binary size stats";
        };
        dump = {
          type = "app";
          program = "${self.packages.${system}.dump}/bin/dump";
          meta.description = "Print RISC-V objdump -d for the SHA-3 binary";
        };
        default = self.apps.${system}.stats;
      });

      devShells = forAllSystems (system: pkgs:
        let
          riscvPkgs = pkgs.pkgsCross.riscv64;
          riscvBinutils = riscvPkgs.buildPackages.binutils;
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.coreutils
              pkgs.elan
              pkgs.gawk
              pkgs.git
              pkgs.gmp
              pkgs.gnused
              pkgs.pkg-config
              pkgs.qemu-user
              pkgs.ocamlPackages.sail
              pkgs.cmake
              pkgs.ninja
              pkgs.z3
              riscvPkgs.stdenv.cc
              riscvBinutils
            ];
            shellHook = ''
              echo "Run: nix build .#sha3 --out-link build/sha3, nix run .#sha3, or lake build ShaFv"
            '';
          };
        });
    };
}
