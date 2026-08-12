#!/usr/bin/env python3
"""Extract same-ELF DWARF locations live at selected function-instance entries."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from elftools.dwarf.descriptions import describe_DWARF_expr
from elftools.dwarf.locationlists import LocationExpr, LocationParser
from elftools.elf.elffile import ELFFile


VARIABLE_TAGS = {"DW_TAG_formal_parameter", "DW_TAG_variable"}


def inherited_attribute(die, name):
    while die is not None:
        attribute = die.attributes.get(name)
        if attribute is not None:
            return attribute
        if "DW_AT_abstract_origin" not in die.attributes:
            return None
        die = die.get_DIE_from_attribute("DW_AT_abstract_origin")
    return None


def active_expression(location, pc: int, default_base: int):
    if isinstance(location, LocationExpr):
        return location.loc_expr
    base = default_base
    for entry in location:
        if hasattr(entry, "base_address"):
            base = entry.base_address
        elif hasattr(entry, "begin_offset"):
            low = entry.begin_offset if entry.is_absolute else base + entry.begin_offset
            high = entry.end_offset if entry.is_absolute else base + entry.end_offset
            if low <= pc < high:
                return entry.loc_expr
    return None


def direct_register(expression: bytes) -> int | None:
    # DW_OP_reg0..DW_OP_reg31 are single-byte opcodes 0x50..0x6f.
    if len(expression) == 1 and 0x50 <= expression[0] <= 0x6f:
        return expression[0] - 0x50
    return None


def generate(manifest: dict, elf_path: Path) -> dict:
    with elf_path.open("rb") as stream:
        elf = ELFFile(stream)
        dwarf = elf.get_dwarf_info()
        locations = LocationParser(dwarf.location_lists())
        dies = {die.offset: die for cu in dwarf.iter_CUs() for die in cu.iter_DIEs()}
        rows = []
        for instance in manifest["instances"]:
            die_offset = int(instance["id"].rsplit(":", 1)[1], 16)
            die = dies.get(die_offset)
            if die is None:
                raise ValueError(f"missing DWARF DIE for {instance['id']}")
            pc = instance["entryPc"]
            bindings = []
            # Parameters belong to the selected DIE. Main's input_ptr/input_size are
            # lexical variables whose loclists remain live at the inlined decode entry.
            candidates = list(die.iter_children())
            if instance["qualified"] == "ssz.decode":
                candidates.extend(candidate for candidate in dies.values()
                                  if candidate.tag == "DW_TAG_variable")
            seen = set()
            for candidate in candidates:
                if candidate.tag not in VARIABLE_TAGS:
                    continue
                name_attr = inherited_attribute(candidate, "DW_AT_name")
                location_attr = candidate.attributes.get("DW_AT_location")
                if name_attr is None or location_attr is None:
                    continue
                name = name_attr.value.decode(errors="replace")
                if instance["qualified"] == "ssz.decode" and candidate not in list(die.iter_children()) \
                        and name not in {"input_ptr", "input_size"}:
                    continue
                location = locations.parse_from_attribute(
                    location_attr, candidate.cu["version"], candidate)
                unit = candidate.cu.get_top_DIE()
                low_pc = unit.attributes.get("DW_AT_low_pc")
                expression = active_expression(location, pc, low_pc.value if low_pc else 0)
                if expression is None:
                    continue
                key = (candidate.tag, name, bytes(expression))
                if key in seen:
                    continue
                seen.add(key)
                bindings.append({
                    "kind": "parameter" if candidate.tag == "DW_TAG_formal_parameter" else "variable",
                    "name": name,
                    "expression": describe_DWARF_expr(expression, dwarf.structs,
                                                       candidate.cu.cu_offset),
                    "machineRegister": direct_register(expression),
                })
            bindings.sort(key=lambda row: (row["kind"], row["name"], row["expression"]))
            rows.append({
                "id": instance["id"],
                "qualified": instance["qualified"],
                "entryPc": pc,
                "bindings": bindings,
            })
        decode = next(row for row in manifest["instances"] if row["qualified"] == "ssz.decode")
        success_pc = decode["exitPcs"][1]
        decoded_locations = []
        for candidate in dies.values():
            if candidate.tag != "DW_TAG_variable":
                continue
            name_attr = inherited_attribute(candidate, "DW_AT_name")
            location_attr = candidate.attributes.get("DW_AT_location")
            if name_attr is None or name_attr.value != b"decoded" or location_attr is None:
                continue
            location = locations.parse_from_attribute(
                location_attr, candidate.cu["version"], candidate)
            unit = candidate.cu.get_top_DIE()
            low_pc = unit.attributes.get("DW_AT_low_pc")
            expression = active_expression(location, success_pc, low_pc.value if low_pc else 0)
            if expression is not None:
                decoded_locations.append(describe_DWARF_expr(
                    expression, dwarf.structs, candidate.cu.cu_offset))
        if decoded_locations != ["(DW_OP_fbreg: 1176)"]:
            raise ValueError(f"unexpected decoded continuation locations: {decoded_locations}")
    return {
        "schemaVersion": 1,
        "artifact": manifest["artifact"],
        "level": manifest["level"],
        "instances": rows,
        "continuations": [{
            "qualified": "ssz.decode",
            "pc": success_pc,
            "value": "decoded",
            "expression": decoded_locations[0],
        }],
        "interpretation": "same-ELF DWARF locations live at the exact selected entry PC",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = generate(json.loads(args.manifest.read_text()), args.elf)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
