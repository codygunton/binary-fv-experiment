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
        if len(INPUTS) != 3:
            raise RuntimeError("expected LEVEL2_MANIFEST CFG PROFILES")
        cls.manifest, cls.cfg, cls.profiles = (
            json.loads(Path(path).read_text()) for path in INPUTS)

    def test_exact_reviewed_inventory(self):
        output = generate(self.manifest, self.cfg, self.profiles)
        self.assertIn("def level2InstanceCount : Nat := 20", output)
        self.assertIn("def writeSuccessRawLine131Entry : Nat := 0x14e00", output)
        self.assertIn("def writeFailureRawLine127Entry : Nat := 0x161c0", output)
        self.assertIn("def writeSuccessOptionalU64FrameSize : Nat := 32", output)
        self.assertIn("def writeSuccessByteListsFrameSize : Nat := 80", output)
        self.assertIn(
            'def encoderCallAllowedStoreRegionNames : List String := '
            '["child-frame", "output-buffer-word", "output-length-word"]', output)

    def test_rejects_artifact_mismatch(self):
        cfg = copy.deepcopy(self.cfg)
        cfg["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "different ELFs"):
            generate(self.manifest, cfg, self.profiles)

    def test_rejects_missing_instance(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["instances"].pop()
        with self.assertRaisesRegex(ValueError, "20-instance"):
            generate(manifest, self.cfg, self.profiles)

    def test_contract_parameters_follow_profiles(self):
        profiles = copy.deepcopy(self.profiles)
        profiles["instances"]["writeSuccessOptionalU64"]["frameSize"] = 16
        output = generate(self.manifest, self.cfg, profiles)
        self.assertIn("def writeSuccessOptionalU64FrameSize : Nat := 16", output)


if __name__ == "__main__":
    unittest.main()
