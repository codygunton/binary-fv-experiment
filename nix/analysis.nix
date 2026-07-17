{ pkgs, repo, rv64, targets }:
let
  inherit (rv64)
    lib
    qemuRiscv64
    riscvAbi
    riscvAr
    riscvArch
    riscvBinutils
    riscvCc
    riscvNm
    riscvObjdump
    riscvReadelf
    riscvSize
    riscvTarget;
  inherit (targets.internal) rethKeccakRust;
  inherit (targets.public) rethKeccak zesuRawObject zesuSsz;

  stats = pkgs.stdenvNoCC.mkDerivation {
    pname = "sha-fv-binary-stats-rv64im-zicclsm";
    version = "0.1.0";

    nativeBuildInputs = [
      pkgs.coreutils
      pkgs.gawk
      pkgs.gnused
      pkgs.python3
      pkgs.qemu-user
      riscvBinutils
    ];

    dontUnpack = true;
    dontConfigure = true;
    dontBuild = true;
    dontFixup = true;

    installPhase = ''
      runHook preInstall

      mkdir -p \
        "$out/analysis" \
        "$out/bin" \
        "$out/objdump" \
        "$out/rv64/bin" \
        "$out/rv64/meta" \
        "$out/rv64/obj"

      cp ${rethKeccak}/bin/reth-keccak "$out/rv64/bin/reth-keccak"
      cp ${rethKeccakRust}/lib/libreth_keccak_wrapper.a \
        "$out/rv64/obj/reth-keccak-rustcrypto.a"
      cp ${rethKeccak}/obj/reth-keccak-main.o "$out/rv64/obj/reth-keccak-main.o"
      cp ${rethKeccak}/meta/elf-attributes.txt \
        "$out/rv64/meta/reth-keccak-elf-attributes.txt"
      cp ${rethKeccak}/meta/selected-symbols \
        "$out/rv64/meta/reth-keccak-selected-symbols.txt"
      cp ${rethKeccak}/meta/reth-keccak.map "$out/rv64/meta/reth-keccak.map"
      cp ${rethKeccak}/meta/symbols.txt "$out/rv64/meta/reth-keccak-symbols.txt"
      cp ${rethKeccak}/meta/provenance.txt "$out/rv64/meta/reth-keccak-provenance.txt"

      cp ${zesuSsz}/bin/zesu-ssz "$out/rv64/bin/zesu-ssz"
      cp ${zesuSsz}/obj/zesu-raw-ssz-allocator.o \
        "$out/rv64/obj/zesu-raw-ssz-allocator.o"
      cp ${zesuSsz}/obj/zesu-raw-ssz-decoder.o \
        "$out/rv64/obj/zesu-raw-ssz-decoder.o"
      cp ${zesuSsz}/obj/zesu-raw-ssz-sink.o \
        "$out/rv64/obj/zesu-raw-ssz-sink.o"
      cp ${zesuSsz}/obj/zesu-ssz-main.o "$out/rv64/obj/zesu-ssz-main.o"
      cp ${zesuSsz}/meta/elf-attributes.txt \
        "$out/rv64/meta/zesu-ssz-elf-attributes.txt"
      cp ${zesuSsz}/meta/selected-symbols \
        "$out/rv64/meta/zesu-ssz-selected-symbols.txt"
      cp ${zesuSsz}/meta/zesu-ssz.map "$out/rv64/meta/zesu-ssz.map"
      cp ${zesuSsz}/meta/symbols.txt "$out/rv64/meta/zesu-ssz-symbols.txt"
      cp ${zesuRawObject}/meta/provenance.txt \
        "$out/rv64/meta/zesu-raw-ssz-provenance.txt"
      for raw_object in allocator decoder sink; do
        cp "${zesuRawObject}/meta/$raw_object-elf-header.txt" \
          "$out/rv64/meta/zesu-raw-ssz-$raw_object-elf-header.txt"
        cp "${zesuRawObject}/meta/$raw_object-elf-attributes.txt" \
          "$out/rv64/meta/zesu-raw-ssz-$raw_object-elf-attributes.txt"
        cp "${zesuRawObject}/meta/$raw_object-undefined-symbols.txt" \
          "$out/rv64/meta/zesu-raw-ssz-$raw_object-undefined-symbols.txt"
      done
      printf '%s\n' reth_keccak256 \
        > "$out/rv64/meta/reth-keccak-protocol-selected-symbols.txt"
      printf '%s\n' zesu_decode_raw > "$out/rv64/meta/zesu-ssz-parser-selected-symbols.txt"

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
            nfields = split($0, tabbed, "\\t")
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

      archive_text_size() {
        local archive="$1"
        local unpack
        unpack="$(mktemp -d)"
        (
          cd "$unpack"
          ${riscvAr} x "$archive"
          for member in *; do
            test -f "$member" || continue
            ${riscvSize} "$member" | awk 'NR == 2 { print $1 }'
          done
        ) | awk '{ total += $1 } END { print total + 0 }'
        rm -rf "$unpack"
      }

      object_text_size() {
        case "$1" in
          *.a) archive_text_size "$1" ;;
          *) text_size "$1" ;;
        esac
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

      {
        printf 'role\tartifact\ttext_bytes\tfile_bytes\n'
        for raw_object in allocator decoder sink; do
          object="$out/rv64/obj/zesu-raw-ssz-$raw_object.o"
          printf '%s\t%s\t%s\t%s\n' \
            "$raw_object" "$(basename "$object")" \
            "$(text_size "$object")" "$(file_size "$object")"
        done
      } > "$out/rv64/meta/zesu-ssz-raw-objects.tsv"

      analyze_target() {
        local target="$1"
        local binary="$2"
        local entry="$3"
        shift 3
        ${pkgs.python3}/bin/python ${repo}/tools/analyze_rv64.py "$binary" \
          --objdump ${riscvObjdump} \
          --entry "$entry" \
          --target "$target ${riscvTarget}" \
          --json "$out/analysis/$target.json" \
          --markdown "$out/analysis/$target.md" \
          "$@"
      }

      json_value() {
        ${pkgs.python3}/bin/python -c 'import json, sys; value = json.load(open(sys.argv[1]))[sys.argv[2]]; print("" if value is None else value)' "$1" "$2"
      }

      json_compact() {
        ${pkgs.python3}/bin/python -c 'import json, sys; print(json.dumps(json.load(open(sys.argv[1]))[sys.argv[2]], sort_keys=True, separators=(",",":")))' "$1" "$2"
      }

      json_length() {
        ${pkgs.python3}/bin/python -c 'import json, sys; print(len(json.load(open(sys.argv[1]))[sys.argv[2]]))' "$1" "$2"
      }

      json_owner_instructions() {
        ${pkgs.python3}/bin/python -c 'import json, sys; report = json.load(open(sys.argv[1])); print(report["ownership"].get(sys.argv[2], {}).get("instructions", 0))' "$1" "$2"
      }

      json_owner_function_count() {
        ${pkgs.python3}/bin/python -c 'import json, sys; report = json.load(open(sys.argv[1])); print(report["ownership"].get(sys.argv[2], {}).get("function_count", 0))' "$1" "$2"
      }

      json_call_depth() {
        ${pkgs.python3}/bin/python -c 'import json, sys; report = json.load(open(sys.argv[1])); print("recursive" if report["recursive_direct_calls"] else report["maximum_direct_call_depth"])' "$1"
      }

      append_target() {
        local target="$1"
        local source="$2"
        local object_label="$3"
        local object="$4"
        local binary="$5"
        local selected_symbols="$6"
        local entry_symbol="$7"
        local analysis_scope="$8"
        local analysis="$out/analysis/$target.json"
        local object_text
        local linked_text
        local selected_instrs
        local branchish
        local full_instrs
        local reachable_instrs
        local protocol_owned_instrs
        local protocol_owned_functions
        local reachable_functions
        local basic_blocks
        local cfg_edges
        local conditional_branches
        local direct_calls
        local loop_sccs
        local maximum_call_depth
        local opcode_classes
        local forbidden_count
        local objdump_lines
        local objdump_instr_lines

        object_text="$(object_text_size "$object")"
        linked_text="$(text_size "$binary")"
        selected_instrs="$(selected_instruction_total "$binary" "$selected_symbols")"
        branchish="$(branchish_total "$binary" "$selected_symbols")"
        full_instrs="$(json_value "$analysis" full_instruction_count)"
        reachable_instrs="$(json_value "$analysis" reachable_instruction_count)"
        protocol_owned_instrs="$(json_owner_instructions "$analysis" protocol)"
        protocol_owned_functions="$(json_owner_function_count "$analysis" protocol)"
        reachable_functions="$(json_value "$analysis" reachable_function_count)"
        basic_blocks="$(json_value "$analysis" basic_blocks)"
        cfg_edges="$(json_value "$analysis" cfg_edges)"
        conditional_branches="$(json_value "$analysis" conditional_branches)"
        direct_calls="$(json_value "$analysis" direct_calls)"
        loop_sccs="$(json_value "$analysis" loop_sccs)"
        maximum_call_depth="$(json_call_depth "$analysis")"
        opcode_classes="$(json_compact "$analysis" opcode_classes)"
        forbidden_count="$(json_length "$analysis" forbidden_reachable_instructions)"
        objdump_lines="$(objdump_line_count "$binary")"
        objdump_instr_lines="$(objdump_instruction_line_count "$binary")"

        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
          "$target" "$analysis_scope" "$entry_symbol" "$source" "${riscvTarget}" \
          "$object_label" "$object_text" "$linked_text" "$selected_instrs" "$branchish" \
          "$full_instrs" "$reachable_instrs" "$protocol_owned_instrs" "$protocol_owned_functions" \
          "$reachable_functions" \
          "$basic_blocks" "$cfg_edges" "$conditional_branches" "$direct_calls" "$loop_sccs" \
          "$maximum_call_depth" "$opcode_classes" "$forbidden_count" "$objdump_lines" \
          "$objdump_instr_lines" "$(file_size "$object")" "$(file_size "$binary")" \
          "analysis/$target.json" >> "$out/stats.tsv"

        printf '| `%s` | `%s` | `%s` | %s | %s B | %s B | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n' \
          "$target" "$analysis_scope" "$entry_symbol" "$object_label" "$object_text" "$linked_text" \
          "$full_instrs" "$reachable_instrs" "$protocol_owned_instrs" "$reachable_functions" \
          "$protocol_owned_functions" \
          "$basic_blocks" "$cfg_edges" "$conditional_branches" "$direct_calls" "$loop_sccs" \
          >> "$out/stats.md"
      }

      ${riscvObjdump} -d "$out/rv64/bin/reth-keccak" > "$out/objdump/reth-keccak.txt"
      ${riscvObjdump} -d "$out/rv64/bin/zesu-ssz" > "$out/objdump/zesu-ssz.txt"
      ${riscvObjdump} -d --disassemble=reth_keccak256 "$out/rv64/bin/reth-keccak" \
        > "$out/objdump/reth-keccak-protocol.txt"
      ${riscvObjdump} -d --disassemble=zesu_decode_raw "$out/rv64/bin/zesu-ssz" \
        > "$out/objdump/zesu-ssz-parser.txt"

      # Retain each freestanding adapter composition for context. The
      # protocol-entry analyses below are the uniformly rooted metrics
      # used for target-selection comparisons.
      analyze_target reth-keccak "$out/rv64/bin/reth-keccak" _start \
        --owner 'reth_keccak256=protocol' \
        --owner '*Keccak*=protocol' \
        --owner '*keccak*=protocol' \
        --owner '*sha3*=protocol' \
        --owner 'main=adapter' \
        --owner '_start=runtime' \
        --owner '*mem*=runtime' \
        --owner '_R*=rust-runtime' \
        --owner '*=rust-runtime'
      # Keep the complete adapter/allocator/decoder/sink composition as
      # a distinct `_start`-rooted analysis. The protocol-entry comparison
      # below is decision-facing and does not replace this artifact.
      analyze_target zesu-ssz "$out/rv64/bin/zesu-ssz" _start \
        --owner 'zesu_raw_sink_checksum=adapter' \
        --owner 'zesu_raw_result=adapter' \
        --owner 'zesu_raw_error=adapter' \
        --owner 'zesu_raw_alloc=allocator' \
        --owner 'zesu_decode_raw=protocol' \
        --owner '*ssz*=protocol' \
        --owner '*Ssz*=protocol' \
        --owner '*decode*=protocol' \
        --owner '*Decode*=protocol' \
        --owner '*rlp*=rlp' \
        --owner '*Rlp*=rlp' \
        --owner 'main=adapter' \
        --owner '_start=runtime' \
        --owner '*mem*=runtime' \
        --owner '*alloc*=allocator' \
        --owner '*Alloc*=allocator' \
        --owner '*=zig-runtime'

      # Every decision-facing metric starts at the exported protocol
      # boundary in its linked ELF and shares the corresponding full
      # composition ownership map above.
      analyze_target reth-keccak-protocol "$out/rv64/bin/reth-keccak" reth_keccak256 \
        --owner 'reth_keccak256=protocol' \
        --owner '*Keccak*=protocol' \
        --owner '*keccak*=protocol' \
        --owner '*sha3*=protocol' \
        --owner 'main=adapter' \
        --owner '_start=runtime' \
        --owner '*mem*=runtime' \
        --owner '_R*=rust-runtime' \
        --owner '*=rust-runtime'

      # Zesu's protocol entry publishes its raw result for a separate
      # anti-DCE sink. Allocator vtable calls remain explicit unresolved
      # indirect calls, never protocol instructions.
      analyze_target zesu-ssz-parser "$out/rv64/bin/zesu-ssz" zesu_decode_raw \
        --owner 'zesu_raw_sink_checksum=adapter' \
        --owner 'zesu_raw_result=adapter' \
        --owner 'zesu_raw_error=adapter' \
        --owner 'zesu_raw_alloc=allocator' \
        --owner 'zesu_decode_raw=protocol' \
        --owner '*ssz*=protocol' \
        --owner '*Ssz*=protocol' \
        --owner '*decode*=protocol' \
        --owner '*Decode*=protocol' \
        --owner '*mem*=runtime' \
        --owner '*alloc*=allocator' \
        --owner '*Alloc*=allocator' \
        --owner '*=zig-runtime'

      reth_output="$(${qemuRiscv64} "$out/rv64/bin/reth-keccak" 616263)"
      test "$reth_output" = 4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

      set +e
      zesu_output="$(${qemuRiscv64} "$out/rv64/bin/zesu-ssz" < /dev/null)"
      zesu_status=$?
      set -e
      test "$zesu_status" = 1
      test "$zesu_output" = invalid

      ${riscvSize} \
        "$out/rv64/obj/reth-keccak-rustcrypto.a" \
        "$out/rv64/obj/zesu-raw-ssz-allocator.o" \
        "$out/rv64/obj/zesu-raw-ssz-decoder.o" \
        "$out/rv64/obj/zesu-raw-ssz-sink.o" \
        "$out/rv64/bin/reth-keccak" \
        "$out/rv64/bin/zesu-ssz" > "$out/size.txt"

      ${riscvNm} -S --size-sort --radix=d \
        "$out/rv64/obj/reth-keccak-rustcrypto.a" \
        "$out/rv64/obj/zesu-raw-ssz-allocator.o" \
        "$out/rv64/obj/zesu-raw-ssz-decoder.o" \
        "$out/rv64/obj/zesu-raw-ssz-sink.o" \
        "$out/rv64/bin/reth-keccak" \
        "$out/rv64/bin/zesu-ssz" > "$out/symbols.txt"

      {
        echo "tool,value"
        printf 'target,%s\n' '${riscvTarget}'
        printf 'march,%s\n' '${riscvArch}'
        printf 'mabi,%s\n' '${riscvAbi}'
        printf 'cc,%s\n' "$( ${riscvCc} --version | head -n 1)"
        printf 'size,%s\n' "$( ${riscvSize} --version | head -n 1)"
        printf 'nm,%s\n' "$( ${riscvNm} --version | head -n 1)"
        printf 'objdump,%s\n' "$( ${riscvObjdump} --version | head -n 1)"
        printf 'qemu,%s\n' "$( ${qemuRiscv64} --version | head -n 1)"
      } > "$out/toolchain.csv"

      cat > "$out/stats.tsv" <<EOF
      target\tanalysis_scope\tentry_symbol\tsource\tarch\tobject_artifact\tobject_text\tlinked_text\tselected_symbol_instructions\tbranchish\tfull_instructions\treachable_instructions\tprotocol_owned_reachable_instructions\tprotocol_owned_reachable_functions\treachable_functions\tbasic_blocks\tcfg_edges\tconditional_branches\tdirect_calls\tloop_sccs\tmaximum_direct_call_depth\topcode_classes\tforbidden_reachable_instructions\tlinked_objdump_lines\tlinked_objdump_instruction_lines\tfile_size_object\tfile_size_linked\tanalysis_json
      EOF

      cat > "$out/stats.md" <<EOF
      # RV64 Target Evaluation Stats

      ## Inputs

      - Reth provenance: \`paradigmxyz/reth\` at \`9384bc53d8c0c77e59cac83fdaaf3b372c6d2216\`
      - Zesu preservation baseline: \`Consensys/zesu\` at \`aa6c94339987d278acb8b7fa409c864dbd3d05aa\`
      - Zesu selected raw decoder: \`codygunton/zesu\` at \`96f1621468ba54755d653f19cbc9704e789be001\`

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

      ## Decision-facing protocol-entry comparison

      Selection rows use the exported protocol root in the linked ELF:
      \`reth_keccak256\` or \`zesu_decode_raw\`.
      In \`stats.tsv\`, filter \`analysis_scope=protocol-entry\` for the uniformly rooted
      inputs to the size and structural comparison.

      | Target | Scope | Entry symbol | Measured artifact | Object \`.text\` | Linked \`.text\` | Full instrs | Reachable instrs | Protocol reachable | Reachable funcs | Protocol funcs | Blocks | CFG edges | Conditional branches | Calls | Loop SCCs |
      |---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
      EOF

      append_target reth-keccak-protocol \
        'Reth RustCrypto Keccak-256 wrapper (protocol entry)' \
        'libreth_keccak_wrapper.a' \
        "$out/rv64/obj/reth-keccak-rustcrypto.a" \
        "$out/rv64/bin/reth-keccak" \
        "$out/rv64/meta/reth-keccak-protocol-selected-symbols.txt" \
        reth_keccak256 \
        protocol-entry
      append_target zesu-ssz-parser \
        'Zesu raw parser rooted at zesu_decode_raw' \
        'zesu-raw-ssz-decoder.o' \
        "$out/rv64/obj/zesu-raw-ssz-decoder.o" \
        "$out/rv64/bin/zesu-ssz" \
        "$out/rv64/meta/zesu-ssz-parser-selected-symbols.txt" \
        zesu_decode_raw \
        protocol-entry

      cat >> "$out/stats.md" <<EOF

      ## Full \`_start\` composition context

      These retained context rows include each freestanding adapter composition. They do
      not feed the decision gates; use the protocol-entry rows above instead.

      | Target | Scope | Entry symbol | Measured artifact | Object \`.text\` | Linked \`.text\` | Full instrs | Reachable instrs | Protocol reachable | Reachable funcs | Protocol funcs | Blocks | CFG edges | Conditional branches | Calls | Loop SCCs |
      |---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
      EOF

      append_target reth-keccak \
        'Reth RustCrypto Keccak-256 wrapper' \
        'libreth_keccak_wrapper.a' \
        "$out/rv64/obj/reth-keccak-rustcrypto.a" \
        "$out/rv64/bin/reth-keccak" \
        "$out/rv64/meta/reth-keccak-selected-symbols.txt" \
        _start \
        full-composition
      append_target zesu-ssz \
        'Zesu full adapter + allocator + decoder + sink composition' \
        'zesu-ssz (full linked ELF)' \
        "$out/rv64/bin/zesu-ssz" \
        "$out/rv64/bin/zesu-ssz" \
        "$out/rv64/meta/zesu-ssz-selected-symbols.txt" \
        _start \
        full-composition

      cat >> "$out/stats.md" <<EOF

      The measured-artifact column identifies the protocol object (or Rust static archive)
      for compact targets and the decoder object for Zesu's protocol entry; \`zesu-ssz\`
      deliberately names the complete linked ELF. Direct reachability is conservative:
      the analyzer follows direct-call fallthroughs even when a callee is noreturn, so the
      Reth protocol root can retain explicitly labeled adapter or runtime code. Ownership
      maps are shared with the matching full-composition rows and are never stripped based
      on inferred behavior.

      ## Structural analysis

      Each \`analysis/<target>.json\` records full and reachable instructions, reachable
      functions, basic blocks, CFG edges, conditional branches, direct calls, loop SCCs,
      maximum direct-call depth, opcode classes, ISA violations, unresolved indirect calls,
      and ownership buckets. The matching Markdown files render the core metrics and ISA
      gate. Complete linked \`objdump -d\` output is in \`objdump/\`; entry-symbol
      disassemblies are \`objdump/reth-keccak-protocol.txt\` and
      \`objdump/zesu-ssz-parser.txt\`. Raw size and symbol output is in \`size.txt\` and
      \`symbols.txt\`.

      ## Sanity

      Reth Keccak-256 produced the independent Ethereum Keccak-256 vector for \`abc\`, and
      the raw Zesu adapter rejected empty input with its expected \`invalid\` exit.
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
    text = ''
      if [ "$#" -eq 0 ]; then
        target=reth-keccak
      else
        target="$1"
        shift
      fi
      if [ "$#" -ne 0 ]; then
        echo "usage: dump [reth-keccak|zesu-ssz]" >&2
        exit 64
      fi
      case "$target" in
        reth-keccak) binary=${rethKeccak}/bin/reth-keccak ;;
        zesu-ssz) binary=${zesuSsz}/bin/zesu-ssz ;;
        *)
          echo "unknown target: $target" >&2
          echo "usage: dump [reth-keccak|zesu-ssz]" >&2
          exit 64
          ;;
      esac
      exec ${riscvObjdump} -d "$binary"
    '';
  };
in
{
  public = {
    inherit dump stats;
    default = stats;
  };
}
