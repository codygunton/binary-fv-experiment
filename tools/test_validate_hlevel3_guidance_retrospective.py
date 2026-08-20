#!/usr/bin/env python3

import copy
import json
import os
import unittest
from pathlib import Path

from validate_hlevel3_guidance_retrospective import build


ROOT = Path(__file__).resolve().parents[1]


class RetrospectiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        manifest = Path(os.environ.get(
            "HLEVEL3_LEVEL2_MANIFEST", ROOT / "result-binary-regions-ui/level2-manifest.json"))
        if not manifest.exists():
            raise unittest.SkipTest("built Level 2 manifest is unavailable")
        cls.manifest = json.loads(manifest.read_text())
        cls.source = (ROOT / "BinaryFv/Zesu/MachineExecution/Level1WriteSuccessSteps.lean").read_text()

    def test_two_completed_contracts(self):
        result = build(self.manifest, self.source)
        self.assertEqual(result["caseCount"], 2)
        self.assertEqual({row["entryPc"] for row in result["cases"]}, {0x14E00, 0x14E7C})

    def test_wrong_entry_is_rejected(self):
        manifest = copy.deepcopy(self.manifest)
        row = next(row for row in manifest["instances"] if row["entryPc"] == 0x14E00)
        row["entryPc"] = 0xDEAD
        with self.assertRaisesRegex(ValueError, "missing held-out"):
            build(manifest, self.source)

    def test_missing_theorem_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing completed theorem"):
            build(self.manifest, self.source.replace("writeSuccessPrefixInstanceContract", "removed"))


if __name__ == "__main__":
    unittest.main()
