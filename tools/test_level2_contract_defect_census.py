#!/usr/bin/env python3

import json
import unittest
from pathlib import Path

from level2_contract_defect_census import build_census


HERE = Path(__file__).parent


class Level2ContractDefectCensusTests(unittest.TestCase):
    def test_production_census_is_exact(self):
        admission = json.loads(Path("result/level2-admission.json").read_text())
        profiles = json.loads((HERE / "level2_contract_evidence_profiles.json").read_text())
        audits = json.loads((HERE / "level2_contract_defect_audits.json").read_text())
        census = build_census(admission, profiles, audits)
        self.assertEqual(census["totalInstanceCount"], 20)
        self.assertEqual(census["failingInstanceCount"], 8)
        self.assertEqual(
            [(row["id"], row["affectedInstanceCount"], row["observedCallerSiteCount"])
             for row in census["defects"]],
            [("called-and-inline-output-writes-omitted", 8, 49),
             ("optional-u64-frame-was-16", 1, 4),
             ("byte-lists-frame-was-64", 1, 5)])
        self.assertEqual(census["instancesWithMultipleDefects"], [
            {"leanName": "writeSuccessByteLists", "defectCount": 2},
            {"leanName": "writeSuccessOptionalU64", "defectCount": 2},
        ])


if __name__ == "__main__":
    unittest.main()
