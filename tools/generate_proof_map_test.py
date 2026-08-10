import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SPEC = importlib.util.spec_from_file_location("proof_map", Path(__file__).with_name("generate_proof_map.py"))
assert SPEC and SPEC.loader
proof_map = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = proof_map
SPEC.loader.exec_module(proof_map)


class ProofMapTests(unittest.TestCase):
    def setUp(self):
        self.pcs = [0x1000 + 4 * index for index in range(172)]
        self.machine = {
            "callGraph": {"owners": [{"id": "fi:6", "qualified": "ssz_raw.decodeRaw",
                                        "entryPc": self.pcs[0], "instructions": self.pcs,
                                        "sourceFile": "ssz_raw.zig", "declLine": 1}]},
            "instructions": [
                {"address": pc, "mnemonic": "addi", "operands": "a0, a0, 1",
                 "successors": [] if index == 171 else [self.pcs[index + 1]],
                 "reads": ["a0"], "writes": ["a0"], "memory": [], "transfer": "ordinary",
                 "symbol": "zesu_decode_raw", "owner": "fi:6"}
                for index, pc in enumerate(self.pcs)
            ],
        }
        self.boundaries = {"boundaries": [{"id": "fi:9", "qualified": "ssz_raw.readOffset",
                                             "entryPc": 0x2000, "instructionPcs": [0x2000]}]}
        self.manifests = {
            "schemaVersion": 1, "ownerInstructionCount": 172,
            "formalCoverage": {"localPcCount": 1, "level4PcCount": 0, "rootPcCount": 0},
            "phases": [{"id": "entry", "label": "entry", "pcs": self.pcs[:60]},
                       {"id": "specialized", "label": "specialized", "pcs": self.pcs[60:120]},
                       {"id": "cleanup", "label": "cleanup", "pcs": self.pcs[120:]}],
            "manifests": [{"id": "m", "pcs": [self.pcs[0]]}],
        }
        self.authoring = {"schemaVersion": 1, "regions": [{
            "id": "r", "label": "reader", "scope": "boundary-family",
            "boundaryQualified": "ssz_raw.readOffset", "authoringState": "ready", "blocker": "none",
        }]}

    def run_generate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            return proof_map.generate(self.machine, self.boundaries, self.manifests, self.authoring,
                                      root, Path(__file__).with_name("analyze_machine_proof_corridors.py"))

    def test_exact_inventory_and_formal_overlay(self):
        result = self.run_generate()
        self.assertEqual(len(result["instructions"]), 172)
        self.assertEqual(result["formalCoverage"]["localPcCount"], 1)
        self.assertEqual(result["instructions"][0]["formalManifests"], ["m"])
        self.assertEqual(len(result["cfgGraph"]["nodes"]), len(result["blocks"]) + 1)
        self.assertEqual(result["blocks"][0]["instructionCount"], 172)
        self.assertEqual(result["blocks"][0]["provedParentInstructionCount"], 1)
        self.assertEqual(result["blocks"][0]["sourceMappings"][0]["qualified"],
                         "ssz_raw.decodeRaw")
        refinement = result["refinementGraph"]
        self.assertEqual(len(refinement["nodes"]), 6)  # one contract + three glue + edge + target
        self.assertEqual(len(refinement["edges"]), 5)
        glue = next(row for row in refinement["nodes"] if row["id"] == "glue-entry")
        self.assertEqual(glue["provedInstructionCount"], 1)
        self.assertEqual(glue["instructionCount"], 60)

    def test_rejects_forged_manifest_pc(self):
        self.manifests["manifests"][0]["pcs"] = [0xDEAD]
        with self.assertRaisesRegex(ValueError, "non-parent PCs"):
            self.run_generate()

    def test_rejects_coverage_count_drift(self):
        self.manifests["formalCoverage"]["localPcCount"] = 2
        with self.assertRaisesRegex(ValueError, "exact manifest union"):
            self.run_generate()

    def test_rejects_phase_partition_gap(self):
        self.manifests["phases"][2]["pcs"].pop()
        with self.assertRaisesRegex(ValueError, "do not partition"):
            self.run_generate()

    def test_rejects_absent_boundary_annotation(self):
        self.authoring["regions"][0]["boundaryQualified"] = "missing"
        with self.assertRaisesRegex(ValueError, "absent boundary"):
            self.run_generate()

    def test_preparation_packet_and_starter_are_untrusted(self):
        region = self.authoring["regions"][0]
        region["pcs"] = self.pcs[:2]
        region["prerequisites"] = ["typed frame"]
        region["protectedMemory"] = ["input bytes"]
        result = self.run_generate()["authoringRegions"][0]
        self.assertEqual(result["preparation"]["liveRegisters"], ["a0"])
        self.assertEqual(result["preparation"]["prerequisites"], ["typed frame"])
        self.assertEqual(result["starterProof"]["trust"], "authoring-suggestion")
        self.assertIn("TODO", result["starterProof"]["text"])


if __name__ == "__main__":
    unittest.main()
