#!/usr/bin/env python3
"""Fail unless a retarget changes only the four reviewed host functions."""

import argparse
import json
from pathlib import Path

from elftools.elf.elffile import ELFFile


HOST_FUNCTIONS = {"_start", "read_input", "write_output", "zkvm_exit"}
PRESERVED_DATA = {
    "ZKVM_HEAP_TOP", "ZKVM_HEAP_POS", "heap_buffer", "input_buffer",
    "alt_fl_alloc.state",
}


def symbols(path: Path):
    with path.open("rb") as stream:
        elf = ELFFile(stream)
        table = elf.get_section_by_name(".symtab")
        return {symbol.name: (symbol["st_value"], symbol["st_size"],
                             symbol["st_info"]["type"])
                for symbol in table.iter_symbols() if symbol.name}


def functions(path: Path):
    with path.open("rb") as stream:
        elf = ELFFile(stream)
        table = elf.get_section_by_name(".symtab")
        result = {}
        for symbol in table.iter_symbols():
            index = symbol["st_shndx"]
            if (symbol["st_info"]["type"] != "STT_FUNC" or not symbol["st_size"] or
                    not isinstance(index, int)):
                continue
            section = elf.get_section(index)
            offset = symbol["st_value"] - section["sh_addr"]
            result[symbol.name] = (symbol["st_value"], section.data()[offset:offset + symbol["st_size"]])
        return result


def cfg_functions(path: Path):
    return {function["name"]: function for function in json.loads(path.read_text())["functions"]}


def validate(old_elf: Path, new_elf: Path, old_cfg: Path, new_cfg: Path):
    old_functions, new_functions = functions(old_elf), functions(new_elf)
    assert old_functions.keys() == new_functions.keys()
    assert {name for name in old_functions if old_functions[name] != new_functions[name]} == HOST_FUNCTIONS

    old_symbols, new_symbols = symbols(old_elf), symbols(new_elf)
    for name in PRESERVED_DATA:
        assert old_symbols[name][0] == new_symbols[name][0], name
    assert new_symbols["binary_fv_io_context"][:2] == (0x2401A0B8, 32)

    old_control, new_control = cfg_functions(old_cfg), cfg_functions(new_cfg)
    assert old_control.keys() == new_control.keys()
    assert {name for name in old_control if old_control[name] != new_control[name]} == HOST_FUNCTIONS
    instructions = (instruction for function in new_control.values() for block in function["blocks"]
                    for instruction in block["instructions"])
    assert all(instruction["mnemonic"] != "ecall" for instruction in instructions)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old-elf", required=True, type=Path)
    parser.add_argument("--new-elf", required=True, type=Path)
    parser.add_argument("--old-cfg", required=True, type=Path)
    parser.add_argument("--new-cfg", required=True, type=Path)
    args = parser.parse_args()
    validate(args.old_elf, args.new_elf, args.old_cfg, args.new_cfg)


if __name__ == "__main__":
    main()
