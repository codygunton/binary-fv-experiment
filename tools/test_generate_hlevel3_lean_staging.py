#!/usr/bin/env python3

import json
import os
import unittest
from pathlib import Path

from generate_hlevel3_lean_staging import DIRECT_PROOFS, generate, idiom_checks


ROOT = Path(__file__).resolve().parents[1]
PREWORK = Path(os.environ.get("HLEVEL3_PREWORK_DIR", "/tmp"))
CATALOGUE = Path(os.environ.get(
    "HLEVEL3_CATALOGUE", str(ROOT / "tools/hlevel3_proof_idioms.json")))
READ_U32_SOURCE = Path(os.environ.get(
    "HLEVEL3_READ_U32_SOURCE", str(ROOT / "BinaryFv/Zesu/Staging/ReadU32.lean")))


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
        cls.read_u32_source = READ_U32_SOURCE.read_text()

    def test_exact_typed_holes(self):
        external_contracts = set(DIRECT_PROOFS) | {"ssz_readU32_fi_1_33a1"}
        self.assertEqual(self.source.count(": Prop := by\n  sorry"), 58 - len(external_contracts))
        self.assertEqual(self.source.count("private theorem resolve_"), 17)
        self.assertEqual(self.source.count("  sorry"), 58 - len(external_contracts) + 17)
        self.assertEqual(self.source.count("def Proposed_"), 58)
        self.assertIn(
            "def Proposed_ssz_readU32_fi_1_33a1_Contract : Prop := by\n"
            "  exact BinaryFv.Zesu.Staging.Proposed_ssz_readU32_fi_1_33a1_Contract",
            self.source)

    def test_read_u32_destination_tuple_is_instance_specific(self):
        self.assertIn(
            "sszReadU32Contract 0x12c18 22 sszReadU32Bindings3335",
            self.read_u32_source)
        self.assertIn(
            "sszReadU32Contract 0x12ca4 58 sszReadU32Bindings33a1",
            self.read_u32_source)
        self.assertNotIn(
            "sszReadU32Contract 0x12ca4 58 sszReadU32Bindings3335",
            self.read_u32_source)

    def test_read_u32_entry_requires_nonwrapping_source_window(self):
        self.assertIn(
            "args.sourceAddress + sourceOffset + 4 ≤ 2 ^ 64 ∧",
            self.read_u32_source)

    def test_every_level3_field_is_passed_to_a_parent(self):
        for row in self.inventory["proposedLevel3Contracts"]:
            if row["field"] in DIRECT_PROOFS:
                self.assertNotIn(f"hLevel3.{row['field']}", self.source)
                self.assertIn(DIRECT_PROOFS[row["field"]], self.source)
            else:
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
