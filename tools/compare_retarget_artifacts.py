#!/usr/bin/env python3
"""Compare exact function bytes and address-independent CFG shapes for two RV64 ELFs."""

import argparse
import collections
import json
import re
from pathlib import Path

from elftools.elf.elffile import ELFFile


IMMEDIATE = re.compile(r"(?<![A-Za-z_])-?(?:0x[0-9a-f]+|\d+)")


def functions(path: Path) -> dict[str, tuple[int, bytes]]:
    with path.open("rb") as stream:
        elf = ELFFile(stream)
        symbols = elf.get_section_by_name(".symtab")
        result = {}
        for symbol in symbols.iter_symbols():
            section_index = symbol["st_shndx"]
            if (symbol["st_info"]["type"] != "STT_FUNC" or not symbol["st_size"] or
                    not isinstance(section_index, int)):
                continue
            section = elf.get_section(section_index)
            offset = symbol["st_value"] - section["sh_addr"]
            result[symbol.name] = (
                symbol["st_value"], section.data()[offset:offset + symbol["st_size"]])
        return result


def number(value):
    return int(value, 0) if isinstance(value, str) else value


def normalized_cfg(function: dict) -> tuple:
    """Erase addresses/immediates but retain block topology, mnemonics, and registers."""
    base = function["start"]
    return tuple(
        (block["start"] - base, block["end"] - base,
         tuple(number(successor) - base for successor in block["successors"]),
         tuple((instruction["mnemonic"], IMMEDIATE.sub("#", instruction["operands"]))
               for instruction in block["instructions"]))
        for block in function["blocks"])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--old-elf", required=True, type=Path)
    parser.add_argument("--new-elf", required=True, type=Path)
    parser.add_argument("--old-cfg", required=True, type=Path)
    parser.add_argument("--new-cfg", required=True, type=Path)
    args = parser.parse_args()

    old_functions = functions(args.old_elf)
    new_functions = functions(args.new_elf)
    common = old_functions.keys() & new_functions.keys()
    same_bytes = sorted(
        name for name in common if old_functions[name][1] == new_functions[name][1])
    exact = sorted(name for name in common if old_functions[name] == new_functions[name])

    old_cfg = json.loads(args.old_cfg.read_text())
    new_cfg = json.loads(args.new_cfg.read_text())
    old_shapes = collections.defaultdict(list)
    new_shapes = collections.defaultdict(list)
    for function in old_cfg["functions"]:
        old_shapes[normalized_cfg(function)].append(function)
    for function in new_cfg["functions"]:
        new_shapes[normalized_cfg(function)].append(function)
    matched_functions = 0
    matched_instructions = 0
    for shape in old_shapes.keys() | new_shapes.keys():
        count = min(len(old_shapes[shape]), len(new_shapes[shape]))
        matched_functions += count
        matched_instructions += sum(
            function["instructionCount"] for function in old_shapes[shape][:count])

    print(json.dumps({
        "exact": {
            "commonNamedFunctions": len(common),
            "sameAddressAndBytes": len(exact),
            "sameAddressAndByteNames": exact,
            "sameAddressAndBytesCount": sum(len(old_functions[name][1]) for name in exact),
            "sameBytesAtAnyAddress": len(same_bytes),
            "sameBytesAtAnyAddressCount": sum(len(old_functions[name][1]) for name in same_bytes),
            "commonNamedFunctionBytes": sum(len(old_functions[name][1]) for name in common),
        },
        "normalized": {
            "matchedFunctions": matched_functions,
            "matchedInstructions": matched_instructions,
            "oldInstructions": old_cfg["totals"]["instructions"],
            "newInstructions": new_cfg["totals"]["instructions"],
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
