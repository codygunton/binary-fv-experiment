#!/usr/bin/env python3

import copy
import json
import os
import unittest
from pathlib import Path

from generate_hlevel3_prework import build


HERE = Path(__file__).parent
RESULT = Path(os.environ.get(
    "HLEVEL3_ARTIFACT_DIR", "/home/cody/binary-fv-experiment/result-binary-regions-ui"))
CFG_RESULT = Path(os.environ.get("HLEVEL3_CFG_DIR", str(RESULT)))
CLAUSES = Path(os.environ.get(
    "HLEVEL3_CLAUSES", str(HERE / "level2_contract_clauses.json")))
TARGETS = Path(os.environ.get("HLEVEL3_TARGETS", str(HERE / "hlevel3_targets.json")))


@unittest.skipUnless(RESULT.exists(), "built binary-regions UI is unavailable")
class LiveArtifactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.documents = [json.loads((CFG_RESULT / name).read_text()) for name in (
            "zesu-cfg.json", "flame.json")]
        cls.documents.append(json.loads((RESULT / "level2-manifest.json").read_text()))
        level3_path = Path(os.environ.get("HLEVEL3_MANIFEST", str(RESULT / "level3-manifest.json")))
        if not level3_path.exists():
            raise unittest.SkipTest("generated Level 3 manifest is unavailable")
        cls.documents.append(json.loads(level3_path.read_text()))
        cls.documents.append(json.loads((RESULT / "level2-evidence.json").read_text()))
        level3_evidence = Path(os.environ.get(
            "HLEVEL3_EVIDENCE", str(RESULT / "level3-evidence.json")))
        if not level3_evidence.exists():
            raise unittest.SkipTest("generated Level 3 evidence is unavailable")
        cls.documents.append(json.loads(level3_evidence.read_text()))
        cls.documents.extend(json.loads(path.read_text()) for path in (CLAUSES, TARGETS))

    def test_exact_level2_boundary(self):
        result = build(*self.documents)
        self.assertEqual(17, result["summary"]["level2FieldCount"])
        self.assertEqual(17, len({row["field"] for row in result["parents"]}))
        self.assertEqual(40, result["summary"]["level3ContractCount"])
        self.assertEqual(88, result["summary"]["level3ChildRouteCount"])
        self.assertEqual(2753, result["summary"]["parentGlueInstructionCount"])
        self.assertEqual(218, result["summary"]["parentGlueObligationCount"])
        for parent in result["parents"]:
            covered = set(parent["gluePcs"])
            for child in parent["children"]:
                covered.update(child["subtreePcs"])
            self.assertEqual(set(parent["executionPcs"]), covered, parent["field"])
        ssz_decode = next(row for row in result["parents"] if row["field"] == "sszDecode")
        self.assertFalse(any(row.get("machineOwner") == "fi:1:33a1"
                             for row in ssz_decode["children"]))
        self.assertTrue({76964, 76968, 76972, 76976} <= set(ssz_decode["gluePcs"]))
        self.assertEqual(15, len(ssz_decode["parentComposedInlineInstances"]))
        self.assertEqual(
            {"fi:1:3167", "fi:1:31b1", "fi:1:3203", "fi:1:327b", "fi:1:32f5",
             "fi:1:34c1", "fi:1:35ab", "fi:1:361f", "fi:1:3693", "fi:1:36dd",
             "fi:1:3731", "fi:1:37a5", "fi:1:37cf", "fi:1:3823", "fi:1:3a74"},
            {row["instanceId"] for row in ssz_decode["parentComposedInlineInstances"]})
        write_bytes = next(row for row in result["parents"] if row["field"] == "writeSuccessBytes")
        self.assertEqual(
            {"fi:1:4350"},
            {row["instanceId"] for row in write_bytes["parentComposedInlineInstances"]})
        write_transactions = next(
            row for row in result["parents"] if row["field"] == "writeSuccessTransactions")
        self.assertEqual(
            {"fi:1:3ec4"},
            {row["instanceId"] for row in write_transactions["parentComposedInlineInstances"]})

    def test_every_level3_candidate_has_entry_evidence(self):
        result = build(*self.documents)
        missing = [row["instanceId"] for row in result["proposedLevel3Contracts"]
                   if row["evidence"]["entryCount"] == 0]
        self.assertEqual([], missing)

    def test_wrong_target_is_rejected(self):
        documents = copy.deepcopy(self.documents)
        documents[-1]["targets"][0]["instanceId"] = "fi:missing"
        with self.assertRaisesRegex(ValueError, "unknown Level 2 target"):
            build(*documents)

    def test_artifact_mismatch_is_rejected(self):
        documents = copy.deepcopy(self.documents)
        documents[4]["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "artifact identities differ"):
            build(*documents)

    def test_duplicate_field_is_rejected(self):
        documents = copy.deepcopy(self.documents)
        documents[-1]["targets"][1]["field"] = documents[-1]["targets"][0]["field"]
        with self.assertRaisesRegex(ValueError, "17 distinct"):
            build(*documents)

    def test_forged_absorbed_attribution_is_rejected(self):
        documents = copy.deepcopy(self.documents)
        documents[-1]["absorbedInlineAttributions"][0]["executionPcs"][0] += 4
        with self.assertRaisesRegex(ValueError, "absorbed inline attribution disagrees"):
            build(*documents)

    def test_forged_parent_composed_instance_is_rejected(self):
        documents = copy.deepcopy(self.documents)
        documents[-1]["parentComposedInlineInstances"][0]["qualified"] = "ssz.readU64"
        with self.assertRaisesRegex(ValueError, "parent-composed inline instance disagrees"):
            build(*documents)

    def test_fork_dispatch_keeps_linked_jump_table_order(self):
        result = build(*self.documents)
        row = next(contract for contract in result["proposedLevel3Contracts"]
                   if contract["instanceId"] == "fi:1:2fe4")
        table = next(table for table in self.documents[0]["resolvedJumpTables"]
                     if table["source"] == 0x12248)
        self.assertEqual(row["jumpTableTargets"], table["targets"])
        self.assertEqual(len(row["jumpTableTargets"]), 21)


if __name__ == "__main__":
    unittest.main()
