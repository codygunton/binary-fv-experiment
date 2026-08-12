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
        self.assertEqual(len(result["instances"]), 20)
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
        self.assertTrue(inline_raw["measured"]["hostWrites"])
        self.assertIn("source-value relation at optimized inline boundary", inline_raw["unmeasured"])
        parent_hash = next(row for row in result["instances"]
                           if row["leanName"] == "writeSuccessRawLine135")
        self.assertEqual(parent_hash["measured"]["validatedEntryBinding"],
                         {"pointerRegister": 10, "width": 32})
        self.assertEqual(set(parent_hash["measured"]["vectors"]), {
            "minimal", "block-number", "chain-id-zero", "legacy-requests",
            "legacy-payload", "future-activation", "extra-data-33",
            "public-key-overflow", "versioned-hash-overflow",
        })
        failure = next(row for row in result["instances"]
                       if row["leanName"] == "writeFailureRawLine127")
        self.assertEqual(failure["measured"]["vectors"], ["invalid"])
        boolean = next(row for row in result["instances"]
                       if row["leanName"] == "writeSuccessBoolean")
        self.assertEqual(boolean["measured"]["validatedEntryBinding"],
                         {"valueRegister": 10, "encoding": "low-bit-u8"})
        encoded_bytes = next(row for row in result["instances"]
                             if row["leanName"] == "writeSuccessBytes")
        self.assertEqual(encoded_bytes["measured"]["validatedEntryBinding"], {
            "pointerRegister": 10, "lengthRegister": 11,
            "encoding": "length-prefixed-bytes",
        })

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

    def test_rejects_forged_fixed_write(self):
        evidence = copy.deepcopy(self.documents[1])
        row = next(row for vector in evidence["vectors"] if vector["label"] == "minimal"
                   for row in vector["instances"] if row["id"] == "fi:1:3d4e")
        row["hostWrites"][0]["bytes"] = "0053535a0101"
        with self.assertRaisesRegex(ValueError, "fixed source write mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3])

    def test_rejects_forged_fixed_pointer_binding(self):
        evidence = copy.deepcopy(self.documents[1])
        row = next(row for vector in evidence["vectors"] if vector["label"] == "minimal"
                   for row in vector["instances"] if row["id"] == "fi:1:3d77")
        row["entryRegisters"][0]["values"][10] += 1
        with self.assertRaisesRegex(ValueError, "fixed source pointer binding mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3])

    def test_rejects_forged_boolean_value_binding(self):
        evidence = copy.deepcopy(self.documents[1])
        row = next(row for vector in evidence["vectors"] if vector["label"] == "minimal"
                   for row in vector["instances"] if row["id"] == "fi:1:4276")
        row["occurrences"][0]["entryRegisters"]["values"][10] ^= 1
        with self.assertRaisesRegex(ValueError, "boolean entry/output binding mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3])

    def test_rejects_forged_byte_slice_pointer_binding(self):
        evidence = copy.deepcopy(self.documents[1])
        rows = (row for vector in evidence["vectors"] for row in vector["instances"]
                if row["id"] == "fi:1:4333")
        occurrence = next(occurrence for row in rows for occurrence in row["occurrences"]
                          if occurrence["entryRegisters"]["values"][11] > 0)
        occurrence["entryRegisters"]["values"][10] += 1
        with self.assertRaisesRegex(ValueError, "byte-slice pointer/length binding mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3])

if __name__ == "__main__":
    unittest.main()
