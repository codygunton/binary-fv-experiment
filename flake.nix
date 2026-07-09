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
          lib = pkgs.lib;
          commonCFlags = [
            "-Os"
            "-g0"
            "-DNDEBUG"
            "-ffunction-sections"
            "-fdata-sections"
            "-fno-asynchronous-unwind-tables"
            "-fno-unwind-tables"
            "-fno-stack-protector"
            "-fomit-frame-pointer"
            "-fno-pie"
          ];
          cflags = lib.concatStringsSep " " commonCFlags;
          sha3SampleMessage = "sha3-sample-message";

          mkBinary =
            { name
            , srcRoot
            , sourceFile
            , entrypoint
            , includes ? [ ]
            , runArgs ? [ ]
            , selectedSymbols
            }:
            pkgs.stdenvNoCC.mkDerivation {
              pname = "sha-fv-${name}";
              version = "0.1.0";
              src = self;

              nativeBuildInputs = [
                pkgs.gcc16
                pkgs.zig
              ];

              hardeningDisable = [ "all" ];
              dontConfigure = true;
              dontBuild = true;
              dontFixup = true;

              installPhase =
                let
                  includeFlags = lib.concatMapStringsSep " " (include: "-I${include}") includes;
                in
                ''
                  runHook preInstall

                  mkdir -p "$out/bin" "$out/obj" "$out/meta"
                  export NIX_HARDENING_ENABLE=""
                  export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
                  export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"

                  gcc ${cflags} ${includeFlags} \
                    -I${srcRoot} \
                    -c ${srcRoot}/${sourceFile} \
                    -o "$out/obj/${name}.o"

                  gcc ${cflags} -no-pie ${includeFlags} \
                    -I${srcRoot} \
                    ${entrypoint} \
                    "$out/obj/${name}.o" \
                    -Wl,--gc-sections \
                    -o "$out/bin/${name}"

                  zig cc -target aarch64-linux-gnu ${cflags} ${includeFlags} \
                    -I${srcRoot} \
                    -c ${srcRoot}/${sourceFile} \
                    -o "$out/obj/${name}.aarch64.o"

                  zig cc -target aarch64-linux-gnu ${cflags} -no-pie ${includeFlags} \
                    -I${srcRoot} \
                    ${entrypoint} \
                    "$out/obj/${name}.aarch64.o" \
                    -Wl,--gc-sections \
                    -o "$out/bin/${name}.aarch64"

                  "$out/bin/${name}" ${lib.escapeShellArgs runArgs}
                  printf '%s\n' ${lib.escapeShellArgs selectedSymbols} > "$out/meta/selected-symbols"

                  runHook postInstall
                '';
            };

          sha3 = mkBinary {
            name = "sha3";
            srcRoot = tiny-sha3;
            sourceFile = "sha3.c";
            entrypoint = ./harness/sha3.c;
            runArgs = [ sha3SampleMessage ];
            selectedSymbols = [
              "sha3_keccakf"
              "sha3_init"
              "sha3_update"
              "sha3_final"
              "sha3"
              "main"
            ];
          };

          tinfl = mkBinary {
            name = "tinfl";
            srcRoot = miniz;
            sourceFile = "miniz_tinfl.c";
            entrypoint = ./harness/tinfl.c;
            includes = [ ./include ];
            selectedSymbols = [
              "tinfl_decompress"
              "tinfl_decompress_mem_to_mem"
              "main"
            ];
          };

          stats = pkgs.stdenvNoCC.mkDerivation {
            pname = "sha-fv-binary-stats";
            version = "0.1.0";

            nativeBuildInputs = [
              pkgs.binutils
              pkgs.coreutils
              pkgs.gawk
              pkgs.gcc16
              pkgs.gnused
              pkgs.zig
            ];

            dontUnpack = true;
            dontConfigure = true;
            dontBuild = true;
            dontFixup = true;

            installPhase = ''
              runHook preInstall

              mkdir -p "$out/bin" "$out/native/bin" "$out/native/obj" "$out/aarch64/bin" \
                "$out/aarch64/obj" "$out/objdump"

              cp ${sha3}/bin/sha3 "$out/native/bin/sha3"
              cp ${sha3}/obj/sha3.o "$out/native/obj/sha3.o"
              cp ${sha3}/bin/sha3.aarch64 "$out/aarch64/bin/sha3"
              cp ${sha3}/obj/sha3.aarch64.o "$out/aarch64/obj/sha3.o"

              cp ${tinfl}/bin/tinfl "$out/native/bin/tinfl"
              cp ${tinfl}/obj/tinfl.o "$out/native/obj/tinfl.o"
              cp ${tinfl}/bin/tinfl.aarch64 "$out/aarch64/bin/tinfl"
              cp ${tinfl}/obj/tinfl.aarch64.o "$out/aarch64/obj/tinfl.o"

              count_symbol_instructions() {
                local file="$1"
                local symbol="$2"
                objdump -d --disassemble="$symbol" "$file" |
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
                  objdump -d --disassemble="$symbol" "$file" >> "$tmp"
                done < "$symbols_file"
                awk '
                  /^[[:space:]]+[0-9a-f]+:/ {
                    nfields = split($0, tabbed, "\t")
                    instr = tabbed[nfields]
                    sub(/^[[:space:]]+/, "", instr)
                    split(instr, a, /[[:space:]]+/)
                    m = a[1]
                    if (m ~ /^j/ && m != "jmp") cond++
                    else if (m == "jmp") uncond++
                    else if (m ~ /^call/) call++
                    else if (m ~ /^ret/) ret++
                  }
                  END { print cond + uncond + call + ret + 0 }
                ' "$tmp"
                rm -f "$tmp"
              }

              text_size() {
                size "$1" | awk 'NR == 2 { print $1 }'
              }

              file_size() {
                stat -c '%s' "$1"
              }

              objdump_line_count() {
                objdump -d "$1" | wc -l | awk '{ print $1 }'
              }

              objdump_instruction_line_count() {
                objdump -d "$1" |
                  awk '/^[[:space:]]+[0-9a-f]+:/ { n++ } END { print n + 0 }'
              }

              objdump -d "$out/native/bin/sha3" > "$out/objdump/sha3.txt"
              objdump -d "$out/native/bin/tinfl" > "$out/objdump/tinfl.txt"

              sha3_native_object_text="$(text_size "$out/native/obj/sha3.o")"
              tinfl_native_object_text="$(text_size "$out/native/obj/tinfl.o")"
              sha3_native_linked_text="$(text_size "$out/native/bin/sha3")"
              tinfl_native_linked_text="$(text_size "$out/native/bin/tinfl")"
              sha3_aarch64_object_text="$(text_size "$out/aarch64/obj/sha3.o")"
              tinfl_aarch64_object_text="$(text_size "$out/aarch64/obj/tinfl.o")"
              sha3_aarch64_linked_text="$(text_size "$out/aarch64/bin/sha3")"
              tinfl_aarch64_linked_text="$(text_size "$out/aarch64/bin/tinfl")"

              sha3_selected_instrs="$(
                selected_instruction_total "$out/native/bin/sha3" ${sha3}/meta/selected-symbols
              )"
              tinfl_selected_instrs="$(
                selected_instruction_total "$out/native/bin/tinfl" ${tinfl}/meta/selected-symbols
              )"
              sha3_branchish="$(branchish_total "$out/native/bin/sha3" ${sha3}/meta/selected-symbols)"
              tinfl_branchish="$(branchish_total "$out/native/bin/tinfl" ${tinfl}/meta/selected-symbols)"
              sha3_objdump_lines="$(objdump_line_count "$out/native/bin/sha3")"
              tinfl_objdump_lines="$(objdump_line_count "$out/native/bin/tinfl")"
              sha3_objdump_instr_lines="$(objdump_instruction_line_count "$out/native/bin/sha3")"
              tinfl_objdump_instr_lines="$(objdump_instruction_line_count "$out/native/bin/tinfl")"

              "$out/native/bin/sha3" ${lib.escapeShellArg sha3SampleMessage}
              "$out/native/bin/tinfl"

              size \
                "$out/native/obj/sha3.o" \
                "$out/native/obj/tinfl.o" \
                "$out/native/bin/sha3" \
                "$out/native/bin/tinfl" \
                "$out/aarch64/obj/sha3.o" \
                "$out/aarch64/obj/tinfl.o" \
                "$out/aarch64/bin/sha3" \
                "$out/aarch64/bin/tinfl" > "$out/size.txt"

              nm -S --size-sort --radix=d \
                "$out/native/obj/sha3.o" \
                "$out/native/obj/tinfl.o" \
                "$out/native/bin/sha3" \
                "$out/native/bin/tinfl" \
                "$out/aarch64/obj/sha3.o" \
                "$out/aarch64/obj/tinfl.o" > "$out/symbols.txt"

              {
                echo "tool,value"
                printf 'cc,%s\n' "$(gcc --version | head -n 1)"
                printf 'zig,%s\n' "$(zig version)"
                printf 'size,%s\n' "$(size --version | head -n 1)"
                printf 'nm,%s\n' "$(nm --version | head -n 1)"
                printf 'objdump,%s\n' "$(objdump --version | head -n 1)"
              } > "$out/toolchain.csv"

              cat > "$out/stats.tsv" <<EOF
              target	arch	object_text	linked_text	selected_symbol_instructions	branchish	linked_objdump_lines	linked_objdump_instruction_lines	file_size_object	file_size_linked
              sha3	x86_64	$sha3_native_object_text	$sha3_native_linked_text	$sha3_selected_instrs	$sha3_branchish	$sha3_objdump_lines	$sha3_objdump_instr_lines	$(file_size "$out/native/obj/sha3.o")	$(file_size "$out/native/bin/sha3")
              tinfl	x86_64	$tinfl_native_object_text	$tinfl_native_linked_text	$tinfl_selected_instrs	$tinfl_branchish	$tinfl_objdump_lines	$tinfl_objdump_instr_lines	$(file_size "$out/native/obj/tinfl.o")	$(file_size "$out/native/bin/tinfl")
              sha3	aarch64	$sha3_aarch64_object_text	$sha3_aarch64_linked_text						$(file_size "$out/aarch64/obj/sha3.o")	$(file_size "$out/aarch64/bin/sha3")
              tinfl	aarch64	$tinfl_aarch64_object_text	$tinfl_aarch64_linked_text						$(file_size "$out/aarch64/obj/tinfl.o")	$(file_size "$out/aarch64/bin/tinfl")
              EOF

              cat > "$out/stats.md" <<EOF
              # Binary Size Stats

              ## Inputs

              - SHA-3: \`mjosaarinen/tiny_sha3\` at \`dcbb3192047c2a721f5f851db591871d428036a9\`
              - DEFLATE: \`richgel999/miniz\` at \`77d0dce8627735138c51770d1799a1ef48f2117d\`

              ## Toolchain

              \`\`\`text
              $(gcc --version | head -n 1)
              zig $(zig version)
              $(size --version | head -n 1)
              \`\`\`

              ## Native x86-64

              | Target | Object \`.text\` | Linked \`.text\` | Selected symbol instrs | Branch/call/ret-ish | Full \`objdump -d\` lines | Full instr lines |
              |---|---:|---:|---:|---:|---:|---:|
              | \`tiny_sha3/sha3.c\` | ''${sha3_native_object_text} B | ''${sha3_native_linked_text} B | ''${sha3_selected_instrs} | ''${sha3_branchish} | ''${sha3_objdump_lines} | ''${sha3_objdump_instr_lines} |
              | \`miniz/miniz_tinfl.c\` | ''${tinfl_native_object_text} B | ''${tinfl_native_linked_text} B | ''${tinfl_selected_instrs} | ''${tinfl_branchish} | ''${tinfl_objdump_lines} | ''${tinfl_objdump_instr_lines} |

              “Selected symbol instrs” counts disassembled instruction lines only in these native symbols:
              \`sha3_keccakf\`, \`sha3_init\`, \`sha3_update\`, \`sha3_final\`, \`sha3\`, and \`main\` for SHA-3;
              \`tinfl_decompress\`, \`tinfl_decompress_mem_to_mem\`, and \`main\` for DEFLATE. The full
              \`objdump -d\` columns count the entire native linked ELF, including startup/runtime sections.

              ## AArch64

              | Target | Object \`.text\` | Linked \`.text\` |
              |---|---:|---:|
              | \`tiny_sha3/sha3.c\` | ''${sha3_aarch64_object_text} B | ''${sha3_aarch64_linked_text} B |
              | \`miniz/miniz_tinfl.c\` | ''${tinfl_aarch64_object_text} B | ''${tinfl_aarch64_linked_text} B |

              ## Sanity

              The native SHA-3 and \`tinfl\` binaries both ran successfully. The AArch64 binaries were
              cross-compiled but not run.

              Raw \`size\` output is in \`size.txt\`, symbol sizes are in \`symbols.txt\`, native linked
              \`objdump -d\` output is in \`objdump/sha3.txt\` and \`objdump/tinfl.txt\`, and
              machine-readable summary data is in \`stats.tsv\`.
              EOF

              cat > "$out/bin/show-stats" <<EOF
              #!${pkgs.runtimeShell}
              cat "$out/stats.md"
              EOF
              chmod +x "$out/bin/show-stats"

              runHook postInstall
            '';
          };

          dump = pkgs.writeShellApplication {
            name = "dump";
            runtimeInputs = [ pkgs.binutils ];
            text = ''
              exec objdump -d ${sha3}/bin/sha3
            '';
          };
        in
        {
          inherit sha3 tinfl stats dump;
          default = stats;
        });

      checks = forAllSystems (system: pkgs: {
        inherit (self.packages.${system}) sha3 tinfl stats dump;
        default = self.packages.${system}.stats;
      });

      apps = forAllSystems (system: pkgs: {
        sha3 = {
          type = "app";
          program = "${self.packages.${system}.sha3}/bin/sha3";
          meta.description = "Run the native SHA-3 binary";
        };
        tinfl = {
          type = "app";
          program = "${self.packages.${system}.tinfl}/bin/tinfl";
          meta.description = "Run the native miniz tinfl binary";
        };
        stats = {
          type = "app";
          program = "${self.packages.${system}.stats}/bin/show-stats";
          meta.description = "Print the reproducible SHA-3/miniz binary size stats";
        };
        dump = {
          type = "app";
          program = "${self.packages.${system}.dump}/bin/dump";
          meta.description = "Print objdump -d for the native SHA-3 binary";
        };
        default = self.apps.${system}.stats;
      });

      devShells = forAllSystems (system: pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.binutils
            pkgs.coreutils
            pkgs.gawk
            pkgs.gcc16
            pkgs.gnused
            pkgs.zig
          ];

          shellHook = ''
            echo "Run: nix build .#sha3 or nix run .#sha3"
          '';
        };
      });
    };
}
