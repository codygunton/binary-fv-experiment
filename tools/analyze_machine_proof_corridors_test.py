import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("analyzer", Path(__file__).with_name("analyze_machine_proof_corridors.py"))
analyzer = importlib.util.module_from_spec(SPEC)
assert SPEC.loader
sys.modules[SPEC.name] = analyzer
SPEC.loader.exec_module(analyzer)


class CorridorAnalysisTests(unittest.TestCase):
    def test_normalizes_register_roles_across_the_full_corridor(self):
        first = analyzer.Corridor("M", "first", (4, 8), (
            analyzer.Instruction(4, "add", "a0, a1, a2", (), (), (8,), "ordinary"),
            analyzer.Instruction(8, "sd", "a0, 0(sp)", (), (("write", 8),), (12,), "ordinary"),
        ), ())
        renamed = analyzer.Corridor("M", "renamed", (16, 20), (
            analyzer.Instruction(16, "add", "s4, s5, s6", (), (), (20,), "ordinary"),
            analyzer.Instruction(20, "sd", "s4, 0(sp)", (), (("write", 8),), (24,), "ordinary"),
        ), ())
        different_flow = analyzer.Corridor("M", "different", (32, 36), (
            analyzer.Instruction(32, "add", "s4, s5, s6", (), (), (36,), "ordinary"),
            analyzer.Instruction(36, "sd", "s5, 0(sp)", (), (("write", 8),), (40,), "ordinary"),
        ), ())
        self.assertEqual(first.signature, renamed.signature)
        self.assertNotEqual(first.signature, different_flow.signature)

    def test_retrieves_only_composition_backed_lists(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); lean = root / "M.lean"; machine_path = root / "machine.json"
            lean.write_text(
                "def inventoryPcs : List Nat := [0x10, 0x14]\n"
                "def secondPcs : List Nat := [0x20, 0x24]\n"
                "theorem second_composed : True := by\n"
                "  have _ := secondPcs\n"
                "  exact Seg.step\n"
            )
            machine_path.write_text(json.dumps({"instructions": [
                {"address": 16, "mnemonic": "sub", "operands": "a0, s9, s7", "writes": ["a0"], "memory": [], "successors": [20], "transfer": "ordinary"},
                {"address": 20, "mnemonic": "li", "operands": "a2, 44", "writes": ["a2"], "memory": [], "successors": [24], "transfer": "ordinary"},
                {"address": 32, "mnemonic": "sub", "operands": "s4, a2, a3", "writes": ["s4"], "memory": [], "successors": [36], "transfer": "ordinary"},
                {"address": 36, "mnemonic": "li", "operands": "a2, 12", "writes": ["a2"], "memory": [], "successors": [40], "transfer": "ordinary"},
            ]}))
            machine = analyzer.machine_instructions(machine_path)
            corridors = analyzer.lean_corridors(root, machine)
            self.assertEqual(len(corridors), 2)
            inventory, composed = corridors
            self.assertFalse(inventory.composition_backed)
            self.assertTrue(composed.composition_backed)
            result = analyzer.report(corridors, machine, [(16, 20)])
            self.assertEqual(result["queries"][0]["matches"][0]["pcs"], [32, 36])
            self.assertTrue(result["queries"][0]["matches"][0]["compositionBacked"])

    def test_query_comes_from_machine_not_named_inventory(self):
        machine = {
            16: analyzer.Instruction(16, "sub", "a0, a1, a2", (), (), (20,), "ordinary"),
            20: analyzer.Instruction(20, "li", "a0, 2", (), (), (24,), "ordinary"),
        }
        self.assertEqual(analyzer.retrieve([], machine, (16, 20), 5), [])

    def test_length_aware_subsequence_score(self):
        def instruction(pc, mnemonic):
            return analyzer.Instruction(pc, mnemonic, "a0, a1, a2", (), (), (pc + 4,), "ordinary")
        query = analyzer.Corridor("q", "q", (4, 8), (instruction(4, "sub"), instruction(8, "li")), ())
        short = analyzer.Corridor("c", "short", (12,), (instruction(12, "sub"),), ("t",))
        extended = analyzer.Corridor("c", "extended", (16, 20, 24), (instruction(16, "sub"), instruction(20, "li"), instruction(24, "add")), ("t",))
        self.assertGreater(analyzer.score(query, extended)[1], analyzer.score(query, short)[1])

    def test_r7_query_uses_machine_map(self):
        root = Path(__file__).resolve().parents[1]
        machine = analyzer.machine_instructions(root / "build/machine-regions-lean/machine-regions.json")
        r7 = tuple(range(0x12924, 0x1294C, 4))
        self.assertTrue(analyzer.retrieve([], machine, r7, 5) == [])


if __name__ == "__main__":
    unittest.main()
