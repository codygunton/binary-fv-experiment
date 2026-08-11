#!/usr/bin/env python3
"""Extract the reachable DWARF layout graph for a named optimized Zig type."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from elftools.elf.elffile import ELFFile


def text(attribute) -> str | None:
    if attribute is None:
        return None
    value = attribute.value
    return value.decode(errors="replace") if isinstance(value, bytes) else str(value)


def generate(elf_path: Path, root_name: str) -> dict:
    with elf_path.open("rb") as stream:
        dwarf = ELFFile(stream).get_dwarf_info()
        dies = [die for cu in dwarf.iter_CUs() for die in cu.iter_DIEs()]
        roots = [die for die in dies if text(die.attributes.get("DW_AT_name")) == root_name]
        if len(roots) != 1:
            raise ValueError(f"expected one DWARF type named {root_name}, found {len(roots)}")
        pending = [roots[0]]
        seen = set()
        rows = []
        while pending:
            die = pending.pop()
            if die.offset in seen:
                continue
            seen.add(die.offset)
            type_attr = die.attributes.get("DW_AT_type")
            referenced = die.get_DIE_from_attribute("DW_AT_type") if type_attr else None
            if referenced is not None:
                pending.append(referenced)
            members = []
            for child in die.iter_children():
                if child.tag == "DW_TAG_member":
                    member_type = child.get_DIE_from_attribute("DW_AT_type")
                    pending.append(member_type)
                    members.append({
                        "name": text(child.attributes.get("DW_AT_name")),
                        "offset": child.attributes["DW_AT_data_member_location"].value,
                        "type": f"0x{member_type.offset:x}",
                    })
                elif child.tag == "DW_TAG_subrange_type" and "DW_AT_type" in child.attributes:
                    subrange_type = child.get_DIE_from_attribute("DW_AT_type")
                    pending.append(subrange_type)
            row = {
                "id": f"0x{die.offset:x}",
                "tag": die.tag.removeprefix("DW_TAG_"),
                "name": text(die.attributes.get("DW_AT_name")),
                "byteSize": die.attributes.get("DW_AT_byte_size").value
                    if "DW_AT_byte_size" in die.attributes else None,
                "alignment": die.attributes.get("DW_AT_alignment").value
                    if "DW_AT_alignment" in die.attributes else None,
                "type": f"0x{referenced.offset:x}" if referenced is not None else None,
                "members": sorted(members, key=lambda member: member["offset"]),
            }
            rows.append(row)
        rows.sort(key=lambda row: int(row["id"], 16))
        return {
            "schemaVersion": 1,
            "artifact": {"kind": "ELF", "sha256": hashlib.sha256(elf_path.read_bytes()).hexdigest()},
            "rootType": f"0x{roots[0].offset:x}",
            "rootName": root_name,
            "types": rows,
            "interpretation": "same-ELF DWARF data layout; semantic values still require memory-representation proofs",
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--type", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.write_text(json.dumps(generate(args.elf, args.type), indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
