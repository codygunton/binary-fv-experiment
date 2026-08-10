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
    def test_normalizes_roles_and_memory_not_literals(self):
        first = analyzer.Instruction(4, "sd", "s8, 0x250(sp)", (), (("write", 8),), (8,), "ordinary")
        second = analyzer.Instruction(8, "sd", "s3, 0x240(sp)", (), (("write", 8),), (12,), "ordinary")
        self.assertEqual(first.normalized(), second.normalized())

    def test_extracts_and_retrieves_sub_li_corridor(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); lean = root / "M.lean"; machine = root / "machine.json"; output = root / "out.json"
            lean.write_text("def firstPcs : List Nat := [0x10, 0x14]\n theorem x := by\n  exact decoderRTypeStepOfDecoderAgree\n"
                            "def secondPcs : List Nat := [0x20, 0x24]\n theorem y := by\n  exact Seg.step\n")
            machine.write_text(json.dumps({"instructions": [
                {"address": 16, "mnemonic": "sub", "operands": "a0, s9, s7", "writes": ["a0"], "memory": [], "successors": [20], "transfer": "ordinary"},
                {"address": 20, "mnemonic": "li", "operands": "a2, 44", "writes": ["a2"], "memory": [], "successors": [24], "transfer": "ordinary"},
                {"address": 32, "mnemonic": "sub", "operands": "s4, a2, a3", "writes": ["s4"], "memory": [], "successors": [36], "transfer": "ordinary"},
                {"address": 36, "mnemonic": "li", "operands": "a2, 12", "writes": ["a2"], "memory": [], "successors": [40], "transfer": "ordinary"},
            ]}))
            corridors = analyzer.lean_corridors(root, analyzer.machine_instructions(machine))
            self.assertEqual(len(corridors), 2)
            result = analyzer.report(corridors, [(16, 20)])
            self.assertEqual(result["queries"][0]["matches"][0]["pcs"], [32, 36])


if __name__ == "__main__":
    unittest.main()
