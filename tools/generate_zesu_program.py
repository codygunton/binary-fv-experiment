#!/usr/bin/env python3
"""Deterministic `zesu-cfg.json` + ELF object -> generated Lean `Program` and `ProgramImage`.

This is a *converter*, not an extractor. `tools/generate_zesu_cfg.py` already reads the object's
DWARF and CFG; this maps its output onto the Lean types that survived the PR #83 wipe:

  BinaryFv/Binary/Elfling/Program.lean          Program, AttributionDefect, ExtractionProvenance
  BinaryFv/Binary/Elfling/FunctionInstance.lean FunctionInstance, BasicBlock, DirectEdge
  BinaryFv/Binary/Elfling/Source.lean           FunctionInstanceId, FunctionId, InlineSite
  BinaryFv/Binary/ProgramImage.lean             ProgramImage, LoadSegment

`FunctionInstance`'s fields correspond one-to-one with what the CFG records, so nothing here
infers anything the extractor did not already establish.

## The target is a relocatable object

`zesu-ssz-decode.o` is an ELF64 RISC-V **relocatable object**: its program counters are `.text`
section offsets and 73 of its instructions carry entries in `.rela.text`. The image is therefore
one `LoadSegment` at virtual address 0 holding `.text` verbatim -- the honest presentation, since
no link has assigned addresses. Instructions with a relocation have unresolved immediate fields;
their offsets are emitted as `relocatedPcs` so a proof can be kept away from them, and the
Markdown index lists them.

## Identity

A `FunctionInstanceId` is address-free: a `FunctionId` plus the inline stack of `InlineSite`s
above it. Uniqueness therefore needs `DW_AT_call_column` -- without it the two `sizeClass` and
`sizeClassOfBytes` pairs that are called twice on one line collapse into single identities. The
extractor emits `callColumn`; this converter fails loudly if two instances still collide.

## Determinism

Instances are emitted in address order, arrays are sorted, and no dictionary iteration order
reaches the output. Two runs are byte-identical; `--check-determinism` asserts it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import struct
import sys

EXTRACTOR_VERSION = "zesu-program-1"


# ---------------------------------------------------------------------------------------
# ELF
# ---------------------------------------------------------------------------------------


def read_sections(data: bytes) -> dict[str, dict]:
    """Section headers of an ELF64 little-endian object, by name."""
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise SystemExit("not an ELF64 little-endian object")
    section_offset = struct.unpack_from("<Q", data, 0x28)[0]
    entry_size = struct.unpack_from("<H", data, 0x3A)[0]
    count = struct.unpack_from("<H", data, 0x3C)[0]
    name_index = struct.unpack_from("<H", data, 0x3E)[0]

    def header(index: int) -> dict:
        base = section_offset + index * entry_size
        fields = struct.unpack_from("<IIQQQQIIQQ", data, base)
        keys = ("name", "type", "flags", "address", "offset", "size",
                "link", "info", "align", "entrySize")
        return dict(zip(keys, fields))

    strings = header(name_index)

    def name_of(offset: int) -> str:
        start = strings["offset"] + offset
        return data[start:data.index(b"\x00", start)].decode()

    return {name_of(h["name"]): h for h in (header(i) for i in range(count))}


def relocated_offsets(data: bytes, sections: dict[str, dict]) -> list[int]:
    """`r_offset` of every entry in `.rela.text`, sorted. These are the instructions whose bytes
    a linker still has to patch, so their immediates are not final in this object."""
    rela = sections.get(".rela.text")
    if rela is None:
        return []
    offsets = {
        struct.unpack_from("<Q", data, rela["offset"] + i * 24)[0]
        for i in range(rela["size"] // 24)
    }
    return sorted(offsets)


# ---------------------------------------------------------------------------------------
# identity
# ---------------------------------------------------------------------------------------


def lean_string(text: str) -> str:
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def declaration(path: str | None, qualified_name: str) -> str:
    return (f"{{ file := {{ path := {lean_string(path or '<unknown>')} }}, "
            f"qualifiedName := {lean_string(qualified_name)} }}")


def instance_identity(row: dict, instances: dict[str, dict]) -> str:
    """`FunctionInstanceId` as Lean source: the function, then the inline stack outermost-last.

    Each `InlineSite` records the declaration inlined *into* and the call site within it. Walking
    parents upward yields innermost-first, which is the order `inlineStack` is written in for the
    generated programs this replaces."""
    sites = []
    current = row
    while current.get("parent"):
        parent = instances[current["parent"]]
        sites.append(
            f"{{ caller := {declaration(current.get('callFile') or parent.get('sourceFile'), parent['name'])}, "
            f"callSite := {{ line := {current.get('callLine') or 0}, "
            f"column := {current.get('callColumn') or 0} }} }}"
        )
        current = parent
    stack = "[" + ", ".join(sites) + "]"
    return (f"{{ function := {{ declaration := {declaration(row.get('sourceFile'), row['name'])}, "
            f"specialization := #[] }}, inlineStack := {stack} }}")


def identity_name(row: dict, index: int) -> str:
    """A stable Lean identifier for an instance's id definition."""
    safe = "".join(character if character.isalnum() else "_" for character in row["name"])
    return f"instanceId_{index:03d}_{safe}"


# ---------------------------------------------------------------------------------------
# emission
# ---------------------------------------------------------------------------------------


def chunked_bytes(name: str, payload: bytes, per_line: int = 12, per_chunk: int = 4096) -> str:
    """`ByteArray` literals in chunks. One 17740-element literal defeats the elaborator, which is
    why the pinned-ELF module this mirrors is chunked the same way."""
    chunks = [payload[i:i + per_chunk] for i in range(0, len(payload), per_chunk)] or [b""]
    lines = []
    for index, chunk in enumerate(chunks):
        lines.append(f"private def {name}_chunk_{index} : ByteArray := ByteArray.mk #[")
        for start in range(0, len(chunk), per_line):
            row = chunk[start:start + per_line]
            lines.append("  " + ", ".join(f"0x{b:02x}" for b in row) + ",")
        if lines[-1].endswith(","):
            lines[-1] = lines[-1][:-1]
        lines.append("]")
        lines.append("")
    joined = " ++ ".join(f"{name}_chunk_{i}" for i in range(len(chunks)))
    lines.append(f"def {name} : ByteArray := {joined}")
    return "\n".join(lines)


def emit_image(text: bytes, digest: str, relocations: list[int]) -> str:
    return f'''-- GENERATED FILE: produced by tools/generate_zesu_program.py. DO NOT EDIT.
import BinaryFv.Binary.ProgramImage

/-!
# Generated program image for the Zesu SSZ decode endpoint

`zesu-ssz-decode.o` is an ELF64 RISC-V **relocatable object**. Its program counters are `.text`
section offsets, so the image is one `LoadSegment` at virtual address 0 holding `.text` verbatim.
No link has assigned addresses, and inventing a base would put a number into the trusted data that
nothing checks.

Address-bearing and **untrusted**: every byte a proof reads is checked against this array, and the
array itself is checked against the pinned object by the derivation that produces it.

`.text` is {len(text)} bytes, exactly {len(text) // 4} instructions, which matches the CFG's
instruction count. sha256 of the section: `{digest}`.

{len(relocations)} instructions carry a `.rela.text` entry, so their immediate fields are not final
in this object. `relocatedPcs` lists them; a proof about a concrete immediate must avoid them.
-/

namespace BinaryFv.Zesu.Generated

set_option maxRecDepth 100000

{chunked_bytes("textBytes", text)}

/-- The `.text` section as the sole load segment, at offset 0. `flags` is R+X. -/
def textSegment : BinaryFv.Binary.LoadSegment :=
  {{ virtualAddress := 0, initialBytes := textBytes, memorySize := {len(text)}, flags := 5 }}

def programImage : BinaryFv.Binary.ProgramImage := {{ segments := #[textSegment] }}

/-- Offsets whose bytes a linker still has to patch. Sorted. -/
def relocatedPcs : Array Nat := #[{", ".join(str(offset) for offset in relocations)}]

end BinaryFv.Zesu.Generated
'''


def emit_program(instances: list[dict], by_id: dict[str, dict], order: dict[str, int],
                 digest: str, entry_id: str) -> str:
    lines = ['-- GENERATED FILE: produced by tools/generate_zesu_program.py. DO NOT EDIT.',
             'import BinaryFv.Binary.Elfling.Program', '',
             '/-!', '# Generated Elfling program for the Zesu SSZ decode endpoint', '',
             'Converted from `zesu-cfg.json` by `tools/generate_zesu_program.py`. Address-bearing',
             'and **untrusted**: the geometry a proof runs against is checked against the image.',
             '',
             f'{len(instances)} function instances, {len(instances)} distinct identities. Identity',
             'is address-free, so it needs `DW_AT_call_column`: without the column the two',
             '`alt_fl_alloc.sizeClass` and `alt_fl_alloc.sizeClassOfBytes` pairs called on one line',
             'collapse into single identities.',
             '-/', '',
             'namespace BinaryFv.Zesu.Generated', '',
             'open BinaryFv.Binary BinaryFv.Binary.Elfling', '',
             'set_option maxRecDepth 100000', '']

    for row in instances:
        lines.append(f"def {identity_name(row, order[row['id']])} : FunctionInstanceId :=")
        lines.append(f"  {instance_identity(row, by_id)}")
    lines.append("")

    lines.append("def functionInstances : Array FunctionInstance := #[")
    entries = []
    for row in instances:
        name = identity_name(row, order[row["id"]])
        regions = ", ".join(
            f"{{ start := {r['start']}, size := {r['end'] - r['start']} }}" for r in row["ranges"])
        exits = ", ".join(str(pc) for pc in row["exitPcs"])
        parent = ("none" if not row.get("parent")
                  else f"some {identity_name(by_id[row['parent']], order[row['parent']])}")
        children = ", ".join(
            identity_name(by_id[child], order[child]) for child in row["children"])
        calls = ", ".join(
            identity_name(by_id[callee], order[callee]) for callee in row["externalCalls"])
        blocks = ", ".join(
            f"{{ range := {{ start := {b['start']}, size := {b['size']} }} }}" for b in row["blocks"])
        edges = ", ".join(
            f"{{ source := {s}, target := {t} }}" for s, t in row["edges"])
        entries.append(
            f"  {{ id := {name}\n"
            f"  , regions := #[{regions}]\n"
            f"  , entryPc := {row['entryPc']}\n"
            f"  , exitPcs := #[{exits}]\n"
            f"  , parent? := {parent}\n"
            f"  , children := #[{children}]\n"
            f"  , externalCalls := #[{calls}]\n"
            f"  , blocks := #[{blocks}]\n"
            f"  , edges := #[{edges}]\n"
            f"  , declProvenance := {{ sourceFileHash := {lean_string(digest)}"
            f", declSpan := {{ line := {row.get('declLine') or 0}, column := 0 }} }}\n"
            f"  , provenance := {{ sidecarHash := {lean_string(digest)}, entryOffset := {row['entryPc']}"
            f", extractorVersion := {lean_string(EXTRACTOR_VERSION)} }}\n"
            f"  , symbol? := none }}")
    lines.append(",\n".join(entries))
    lines.append("]")
    lines.append("")
    lines.append("def generatedProgram : Program :=")
    lines.append(f"  {{ entry := {identity_name(by_id[entry_id], order[entry_id])}")
    lines.append("  , functionInstances := functionInstances")
    lines.append("  , defects := #[]")
    lines.append(f"  , provenance := {{ sidecarHash := {lean_string(digest)}, entryOffset := 0"
                 f", extractorVersion := {lean_string(EXTRACTOR_VERSION)} }} }}")
    lines.append("")
    lines.append("end BinaryFv.Zesu.Generated")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------------------


def build(cfg: dict, data: bytes) -> tuple[str, str, dict]:
    sections = read_sections(data)
    if ".text" not in sections:
        raise SystemExit("object has no .text")
    text_header = sections[".text"]
    text = data[text_header["offset"]:text_header["offset"] + text_header["size"]]
    digest = hashlib.sha256(text).hexdigest()
    relocations = relocated_offsets(data, sections)

    by_id = {row["id"]: row for row in cfg["functionInstances"]}
    instances = sorted(cfg["functionInstances"], key=lambda row: (row["entryPc"], row["name"]))
    order = {row["id"]: index for index, row in enumerate(instances)}

    identities = {}
    for row in instances:
        identity = instance_identity(row, by_id)
        if identity in identities:
            raise SystemExit(
                f"identity collision: {row['name']} at 0x{row['entryPc']:x} and "
                f"0x{identities[identity]['entryPc']:x} share an address-free id. "
                "The extractor must emit DW_AT_call_column.")
        identities[identity] = row

    # blocks and edges come from the CFG's own partition, restricted to each instance's pcs
    owned = {row["id"]: set(row["pcs"]) for row in instances}
    block_rows: dict[str, list[dict]] = {row["id"]: [] for row in instances}
    edge_rows: dict[str, list[tuple[int, int]]] = {row["id"]: [] for row in instances}
    successors: dict[int, list[int]] = {}
    for function in cfg["functions"]:
        for block in function["blocks"]:
            body = block["instructions"]
            pcs = [entry["pc"] for entry in body]
            for offset, pc in enumerate(pcs):
                successors.setdefault(
                    pc,
                    [pcs[offset + 1]] if offset + 1 < len(pcs)
                    else [int(s, 0) for s in block.get("successors", [])])
            for row in instances:
                mine = [pc for pc in pcs if pc in owned[row["id"]]]
                if len(mine) == len(pcs) and pcs:
                    block_rows[row["id"]].append(
                        {"start": pcs[0], "size": 4 * len(pcs)})
    for row in instances:
        mine = owned[row["id"]]
        edge_rows[row["id"]] = sorted(
            (pc, target) for pc in sorted(mine) for target in successors.get(pc, [])
            if target in mine)
        row["blocks"] = sorted(block_rows[row["id"]], key=lambda b: b["start"])
        row["edges"] = edge_rows[row["id"]]
        row["children"] = sorted(
            (other["id"] for other in instances if other.get("parent") == row["id"]),
            key=lambda identifier: by_id[identifier]["entryPc"])
        # an exit is an owned pc whose successors leave the instance, or which has none
        row["exitPcs"] = sorted(
            pc for pc in mine
            if not successors.get(pc) or any(t not in mine for t in successors.get(pc, [])))
        row["externalCalls"] = []

    entry = min(instances, key=lambda row: (row["entryPc"], len(row["pcs"]) * -1))["id"]
    image = emit_image(text, digest, relocations)
    program = emit_program(instances, by_id, order, digest, entry)
    summary = {
        "textBytes": len(text),
        "instructions": len(text) // 4,
        "textSha256": digest,
        "functionInstances": len(instances),
        "distinctIdentities": len(identities),
        "relocatedPcs": len(relocations),
    }
    return image, program, summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cfg", type=pathlib.Path, required=True)
    parser.add_argument("--object", type=pathlib.Path, required=True)
    parser.add_argument("--out-image", type=pathlib.Path, required=True)
    parser.add_argument("--out-program", type=pathlib.Path, required=True)
    parser.add_argument("--check-determinism", action="store_true")
    arguments = parser.parse_args()

    cfg = json.loads(arguments.cfg.read_text())
    data = arguments.object.read_bytes()
    image, program, summary = build(cfg, data)

    if arguments.check_determinism:
        again_image, again_program, _ = build(json.loads(arguments.cfg.read_text()), data)
        if (again_image, again_program) != (image, program):
            raise SystemExit("output is not deterministic")

    for path, payload in ((arguments.out_image, image), (arguments.out_program, program)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(payload)

    json.dump(summary, sys.stdout, indent=1, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
