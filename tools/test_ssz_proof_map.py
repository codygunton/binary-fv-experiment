#!/usr/bin/env python3
import copy
import importlib.util
import json
import sys
import unittest
from pathlib import Path

INPUTS = sys.argv[1:]
sys.argv[:] = sys.argv[:1]

class ProofMapTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if len(INPUTS) != 8:
            raise RuntimeError(
                "expected CFG FLAME L1_MANIFEST L1_EVIDENCE L1_BINDINGS "
                "L2_MANIFEST L2_EVIDENCE L2_BINDINGS")
        cls.documents = [json.loads(Path(path).read_text()) for path in INPUTS]
        module_path = Path(__file__).with_name("build_ssz_proof_map.py")
        spec = importlib.util.spec_from_file_location("proof_map", module_path)
        cls.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.module)

    def test_exact_level_relationship(self):
        result = self.module.build(*self.documents)
        contracts = [node for node in result["refinementGraph"]["nodes"]
                     if node["kind"] == "level1Contract"]
        self.assertEqual(len(contracts), 6)
        self.assertEqual(sum(region["scope"] == "parent"
                             for region in result["authoringRegions"]), 1)
        self.assertEqual(result["phases"][0]["label"], "main parent-owned glue")
        decode = next(row for row in result["boundaries"]
                      if row["qualified"] == "ssz_decode_root.decodeInput")
        locations = {row["name"]: row for row in decode["dwarfBindings"]}
        self.assertEqual(locations["alloc"]["addressRegister"], 11)
        self.assertEqual(decode["contractStatus"], "specified_assumption")
        self.assertTrue(all(row["evidenceStatus"] == "captured"
                            for row in result["boundaries"]))
        level1_boundaries = [row for row in result["boundaries"]
                             if row["id"].startswith("level1-")]
        level2_boundaries = [row for row in result["boundaries"]
                             if row["id"].startswith("level2-")]
        self.assertEqual(len(level1_boundaries), 6)
        self.assertEqual(len(level2_boundaries), 20)
        self.assertTrue(all(row["contractStatus"] == "specified_assumption"
                            for row in level1_boundaries))
        self.assertTrue(all(row["contractStatus"] == "specified"
                            for row in level2_boundaries))
        self.assertTrue(all(row["parentInstanceIds"]
                            for row in level2_boundaries))
        consumed = {row["qualified"] for row in result["boundaries"]
                    if row["level0UseStatus"] == "consumed"}
        self.assertEqual(consumed,
                         {"read_input", "zkvm_exit", "alt_fl_alloc.get",
                          "ssz_decode_root.decodeInput",
                          "ssz_decode_observation.writeSuccess",
                          "ssz_decode_observation.writeFailure"})
        glue = next(node for node in result["refinementGraph"]["nodes"]
                    if node["kind"] == "parentGlue")
        self.assertEqual((glue["proofStatus"], glue["provedInstructionCount"]),
                         ("proof_revalidation_pending", 24))
        self.assertEqual(glue["instructionCount"], 24)
        self.assertEqual(glue["absorbedInlineInstructionCount"], 2)
        progress = {row["owner"]: row["status"]
                    for row in result["flameProgress"]["states"]}
        main = next(row for row in self.documents[0]["functionInstances"]
                    if row["kind"] == "concrete" and row["entryPc"] == 0x14cb0)
        self.assertEqual(progress[main["id"]], "proof_revalidation_pending")
        memcpy = next(row for row in self.documents[5]["instances"]
                      if row["qualified"] == "memcpy")
        self.assertEqual(progress[memcpy["id"]], "proof_revalidation_pending")
        self.assertEqual({progress[row["id"]] for row in self.documents[5]["instances"]
                          if row["id"] != memcpy["id"]},
                         {"contract_specified_assumption"})
        read_input = next(row for row in level1_boundaries if row["qualified"] == "read_input")
        zkvm_exit = next(row for row in level1_boundaries if row["qualified"] == "zkvm_exit")
        self.assertEqual(read_input["proofStatus"], "not_started")
        self.assertEqual(zkvm_exit["proofStatus"], "not_started")
        self.assertEqual(result["targetModel"]["status"], "valid_bare_metal")
        self.assertEqual(len(progress), 27)

    def test_rejects_artifact_mismatch(self):
        documents = copy.deepcopy(self.documents)
        documents[4]["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "artifact identities differ"):
            self.module.build(*documents)

        documents = copy.deepcopy(self.documents)
        documents[7]["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "Level 2 artifact identities differ"):
            self.module.build(*documents)


if __name__ == "__main__":
    unittest.main()
