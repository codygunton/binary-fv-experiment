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
        if len(INPUTS) != 4:
            raise RuntimeError("expected CFG FLAME MANIFEST EVIDENCE")
        cls.documents = [json.loads(Path(path).read_text()) for path in INPUTS]
        module_path = Path(__file__).with_name("build_ssz_proof_map.py")
        spec = importlib.util.spec_from_file_location("proof_map", module_path)
        cls.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.module)

    def test_exact_level_relationship(self):
        result = self.module.build(*self.documents)
        contracts = [node for node in result["refinementGraph"]["nodes"]
                     if node["kind"] == "level1Contract"]
        self.assertEqual(len(contracts), 9)
        self.assertEqual(sum(region["scope"] == "parent"
                             for region in result["authoringRegions"]), 1)
        self.assertEqual(result["phases"][0]["label"], "main parent-owned glue")

    def test_rejects_artifact_mismatch(self):
        documents = copy.deepcopy(self.documents)
        documents[3]["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "artifact identities differ"):
            self.module.build(*documents)


if __name__ == "__main__":
    unittest.main()
