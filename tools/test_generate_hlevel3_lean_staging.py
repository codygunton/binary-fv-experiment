#!/usr/bin/env python3

import json
import os
import unittest
from pathlib import Path

from generate_hlevel3_lean_staging import generate, idiom_checks


ROOT = Path(__file__).resolve().parents[1]
PREWORK = Path(os.environ.get("HLEVEL3_PREWORK_DIR", "/tmp"))
CATALOGUE = Path(os.environ.get(
    "HLEVEL3_CATALOGUE", str(ROOT / "tools/hlevel3_proof_idioms.json")))


@unittest.skipUnless(all((PREWORK / name).exists() for name in (
    "hlevel3-prework.json", "hlevel3-guidance.json", "hlevel3-admission.json")),
    "generated hLevel3 staging inputs are unavailable")
class LeanStagingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory, cls.guidance, cls.admission = [
            json.loads((PREWORK / name).read_text()) for name in (
                "hlevel3-prework.json", "hlevel3-guidance.json", "hlevel3-admission.json")]
        cls.catalogue = json.loads(CATALOGUE.read_text())
        cls.source = generate(cls.inventory, cls.guidance, cls.admission, cls.catalogue)

    def test_exact_typed_holes(self):
        self.assertEqual(self.source.count("  sorry"), 74)
        self.assertEqual(self.source.count("def Proposed_"), 58)
        self.assertEqual(self.source.count("private theorem resolve_"), 17)
        self.assertIn(
            "def Proposed_ssz_readU32_fi_1_33a1_Contract : Prop := by\n  exact ∃ stepBound",
            self.source)

    def test_read_u32_destination_tuple_is_instance_specific(self):
        self.assertIn(
            "sszReadU32Contract 0x12ca4 58 x16 x6 x17 x5 stepBound",
            self.source)
        self.assertNotIn(
            "sszReadU32Contract 0x12ca4 58 x10 x15 x13 x14 stepBound",
            self.source)

    def test_every_level3_field_is_passed_to_a_parent(self):
        for row in self.inventory["proposedLevel3Contracts"]:
            self.assertIn(f"hLevel3.{row['field']}", self.source)

    def test_idiom_file_checks_every_declaration(self):
        source = idiom_checks(self.catalogue)
        declarations = {row["declaration"] for row in self.catalogue["idioms"]
                        if "declaration" in row}
        self.assertEqual(source.count("#check "), len(declarations))
        self.assertIn("syntax", next(row for row in self.catalogue["idioms"]
                                     if row["id"] == "owned-pc"))


if __name__ == "__main__":
    unittest.main()
