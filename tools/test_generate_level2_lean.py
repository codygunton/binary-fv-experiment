#!/usr/bin/env python3

import copy
import json
import sys
import unittest
from pathlib import Path

from generate_level2_lean import generate

INPUTS = sys.argv[1:]
sys.argv[:] = sys.argv[:1]


class GenerateLevel2LeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if len(INPUTS) != 2:
            raise RuntimeError("expected LEVEL2_MANIFEST CFG")
        cls.manifest, cls.cfg = (json.loads(Path(path).read_text()) for path in INPUTS)

    def test_exact_reviewed_inventory(self):
        output = generate(self.manifest, self.cfg)
        self.assertIn("def level2InstanceCount : Nat := 20", output)
        self.assertIn("def writeSuccessRawLine131Entry : Nat := 0x14e00", output)
        self.assertIn("def writeFailureRawLine127Entry : Nat := 0x161c0", output)

    def test_rejects_artifact_mismatch(self):
        cfg = copy.deepcopy(self.cfg)
        cfg["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "different ELFs"):
            generate(self.manifest, cfg)

    def test_rejects_missing_instance(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["instances"].pop()
        with self.assertRaisesRegex(ValueError, "20-instance"):
            generate(manifest, self.cfg)


if __name__ == "__main__":
    unittest.main()
