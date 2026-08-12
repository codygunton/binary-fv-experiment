#!/usr/bin/env python3

import copy
import json
import sys
import unittest
from pathlib import Path

import generate_level2_admission as admission

INPUTS = sys.argv[1:]
sys.argv[:] = sys.argv[:1]


class Level2AdmissionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if len(INPUTS) != 4:
            raise RuntimeError("expected MANIFEST EVIDENCE BINDINGS CFG")
        cls.documents = [json.loads(Path(path).read_text()) for path in INPUTS]
        cls.module = admission

    def test_reviews_exact_inventory_without_admitting_contracts(self):
        result = self.module.build(*self.documents)
        self.assertEqual(len(result["instances"]), 22)
        self.assertEqual({row["semanticReview"]["status"] for row in result["instances"]},
                         {"reviewed"})
        self.assertEqual({row["contractStatus"] for row in result["instances"]},
                         {"not-admitted"})
        memcpy = next(row for row in result["instances"] if row["leanName"] == "memcpy")
        self.assertEqual({row["name"] for row in memcpy["measured"]["dwarfBindings"]
                          if row["kind"] == "parameter"}, {"dst", "src", "n"})
        inline_raw = next(row for row in result["instances"]
                          if row["leanName"] == "writeSuccessRawLine131")
        self.assertEqual(inline_raw["measured"]["dwarfBindings"], [])
        self.assertIn("source-value relation at optimized inline boundary", inline_raw["unmeasured"])

    def test_rejects_artifact_mismatch(self):
        documents = copy.deepcopy(self.documents)
        documents[2]["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "different ELFs"):
            self.module.build(*documents)

    def test_rejects_missing_semantic_mapping(self):
        saved = self.module.SEMANTICS.pop("writeSuccessBoolean")
        try:
            with self.assertRaises(KeyError):
                self.module.build(*self.documents)
        finally:
            self.module.SEMANTICS["writeSuccessBoolean"] = saved


if __name__ == "__main__":
    unittest.main()
