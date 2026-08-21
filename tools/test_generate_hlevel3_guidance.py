#!/usr/bin/env python3

import json
import os
import unittest
from pathlib import Path


GUIDANCE = Path(os.environ.get("HLEVEL3_GUIDANCE", "/tmp/hlevel3-guidance.json"))


@unittest.skipUnless(GUIDANCE.exists(), "generated hLevel3 guidance is unavailable")
class GuidanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.document = json.loads(GUIDANCE.read_text())

    def test_every_glue_fragment_has_guidance(self):
        summary = self.document["summary"]
        self.assertEqual(summary["obligationCount"], 218)
        self.assertEqual(summary["unmatchedObligationCount"], 0)
        self.assertEqual(len(self.document["obligations"]), 218)

    def test_all_motifs_are_analyzed_without_top_n_cutoff(self):
        summary = self.document["summary"]
        self.assertEqual(summary["analyzedMotifCount"], 9118)
        self.assertEqual(summary["selectedMotifCount"], len(self.document["motifs"]))
        self.assertTrue(all(row["length"] >= 2 for row in self.document["motifs"]))

    def test_all_hints_name_typed_apis(self):
        for obligation in self.document["obligations"]:
            for hint in obligation["idiomHints"]:
                self.assertIn(hint["api"]["kind"], {"declaration", "tactic"})
                self.assertTrue(hint["api"]["name"])

    def test_normalized_sibling_reuse_is_recorded(self):
        self.assertEqual(len(self.document["exactSiblingGroups"]), 12)
        self.assertTrue(all(len(row["occurrences"]) >= 2
                            for row in self.document["exactSiblingGroups"]))


if __name__ == "__main__":
    unittest.main()
