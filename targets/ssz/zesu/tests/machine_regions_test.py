#!/usr/bin/env python3
"""Unit and corruption tests for the canonical machine-region database."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location(
    "machine_regions", ROOT / "tools" / "generate_machine_regions.py"
)
assert SPEC and SPEC.loader
machine_regions = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(machine_regions)


class MachineRegionTests(unittest.TestCase):
    def test_llvm_disassembly_parser(self) -> None:
        parsed = machine_regions.parse_disassembly(
            """
00000000000102b0 <zesu_decode_raw>:
   102b0: 81010113      addi sp, sp, -0x7f0
   102b4: 7e113423      sd ra, 0x7e8(sp)
   102b8: 02050063      beqz a0, 0x102d8 <zesu_decode_raw+0x28>
"""
        )
        self.assertEqual(parsed[0x102B0]["word"], 0x81010113)
        self.assertEqual(parsed[0x102B8]["mnemonic"], "beqz")

    def test_register_effects(self) -> None:
        load = {"mnemonic": "ld", "operands": "a0, 0x8(sp)"}
        reads, writes, memory, known = machine_regions.register_effects(load)
        self.assertEqual(reads, {"sp"})
        self.assertEqual(writes, {"a0"})
        self.assertEqual(memory, [{"kind": "read", "bytes": 8}])
        self.assertTrue(known)

    def test_resolves_auipc_jalr_from_words(self) -> None:
        instructions = {
            0x1000: {"mnemonic": "auipc", "word": 0x00000097},
            0x1004: {"mnemonic": "jalr", "word": 0x100080E7},
        }
        self.assertEqual(
            machine_regions.resolved_auipc_jalr_target(0x1004, instructions[0x1004], instructions),
            0x1100,
        )

    def test_tarjan_finds_loop(self) -> None:
        graph = {0: {1}, 1: {2}, 2: {1, 3}, 3: set()}
        self.assertIn([1, 2], machine_regions.strongly_connected_components(graph))

    def test_condensation_ranks_increase_across_edges(self) -> None:
        graph = {0: {1}, 1: {2}, 2: set()}
        ranks = machine_regions.condensation_ranks(graph, {0: 0, 1: 1, 2: 2}, 3)
        self.assertLess(ranks[0], ranks[1])
        self.assertLess(ranks[1], ranks[2])

    def test_liveness_equation(self) -> None:
        graph = {0: {1}, 1: set()}
        effects = {0: ({"a0"}, {"a1"}), 1: ({"a1"}, set())}
        live_in, live_out = machine_regions.liveness(graph, effects)
        self.assertEqual(live_out[0], {"a1"})
        self.assertEqual(live_in[0], {"a0"})

    def valid_database(self) -> dict:
        return {
            "instructions": [{
                "address": 4,
                "owner": "unit",
                "successors": [],
                "transfer": "return",
                "reads": ["ra"],
                "writes": [],
                "liveIn": ["ra"],
                "liveOut": [],
            }],
            "entry": 4,
            "owners": [{"id": "unit", "instructions": [4], "entries": [4], "exits": []}],
            "sccs": [{"id": 0, "rank": 0, "instructions": [4], "loop": False}],
            "sccForwardTree": [{"address": 4, "parent": 4, "depth": 0}],
            "sccReverseTree": [{"address": 4, "parent": 4, "depth": 0}],
            "unresolvedIndirectTransfers": [],
        }

    def assert_corruption_rejected(self, mutate) -> None:
        database = copy.deepcopy(self.valid_database())
        mutate(database)
        with self.assertRaises(ValueError):
            machine_regions.validate(database)

    def test_missing_owner_instruction_rejected(self) -> None:
        self.assert_corruption_rejected(lambda db: db["owners"][0].update(instructions=[]))

    def test_duplicate_owner_instruction_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["owners"].append({"id": "other", "instructions": [4]})
        )

    def test_absent_successor_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["instructions"][0].update(successors=[8])
        )

    def test_bad_liveness_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["instructions"][0].update(liveIn=[])
        )

    def test_missing_scc_member_rejected(self) -> None:
        self.assert_corruption_rejected(lambda db: db["sccs"][0].update(instructions=[]))

    def test_invented_exit_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["owners"][0].update(exits=[{"source": 4, "target": 4}])
        )

    def test_false_indirect_resolution_rejected(self) -> None:
        def mutate(database: dict) -> None:
            database["instructions"][0]["transfer"] = "indirectTransfer"

        self.assert_corruption_rejected(mutate)

    def test_stale_input_hash_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            elf, program = root / "decoder.elf", root / "program.json"
            elf.write_bytes(b"elf")
            program.write_text("{}")
            database = {
                "inputs": {
                    "elfSha256": machine_regions.sha256(elf),
                    "programJsonSha256": machine_regions.sha256(program),
                }
            }
            machine_regions.validate_input_hashes(database, elf, program)
            elf.write_bytes(b"changed")
            with self.assertRaises(ValueError):
                machine_regions.validate_input_hashes(database, elf, program)


if __name__ == "__main__":
    unittest.main()
