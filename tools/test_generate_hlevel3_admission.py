#!/usr/bin/env python3
"""Mutation tests for the hLevel3 contract-review matrix."""

from __future__ import annotations

import copy
import json
import os
import unittest
from pathlib import Path

from generate_hlevel3_admission import build


ROOT = Path(__file__).resolve().parents[1]
RESULT = Path(os.environ.get("HLEVEL3_PREWORK_DIR", "/tmp"))
EVIDENCE = Path(os.environ.get("HLEVEL3_EVIDENCE", "/tmp/level3-evidence-placeholder.json"))
BINDINGS = Path(os.environ.get("HLEVEL3_BINDINGS", "/tmp/level3-boundary-bindings.json"))
REGISTRY = Path(os.environ.get(
    "HLEVEL3_REGISTRY", str(ROOT / "tools/hlevel3_contract_schemas.json")))


@unittest.skipUnless((RESULT / "hlevel3-prework.json").exists() and EVIDENCE.exists() and BINDINGS.exists(),
                     "generated hLevel3 artifacts are unavailable")
class AdmissionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory = json.loads((RESULT / "hlevel3-prework.json").read_text())
        cls.evidence = json.loads(EVIDENCE.read_text())
        cls.bindings = json.loads(BINDINGS.read_text())
        cls.registry = json.loads(REGISTRY.read_text())

    def test_exact_boundary(self):
        result = build(self.inventory, self.evidence, self.bindings, self.registry)
        self.assertEqual(result["summary"]["instanceCount"], 41)
        self.assertEqual(result["summary"]["familyCount"], 14)
        self.assertEqual(result["summary"]["admittedContractCount"], 0)

    def test_missing_schema_is_rejected(self):
        registry = copy.deepcopy(self.registry)
        del registry["families"]["fork-name"]
        with self.assertRaisesRegex(ValueError, "contract family set"):
            build(self.inventory, self.evidence, self.bindings, registry)

    def test_artifact_mismatch_is_rejected(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["artifact"] = {"sha256": "forged"}
        with self.assertRaisesRegex(ValueError, "different ELFs"):
            build(self.inventory, evidence, self.bindings, self.registry)

    def test_missing_binding_is_rejected(self):
        bindings = copy.deepcopy(self.bindings)
        bindings["instances"].pop()
        with self.assertRaisesRegex(ValueError, "missing boundary bindings"):
            build(self.inventory, self.evidence, bindings, self.registry)

    def test_forged_machine_boundary_is_rejected(self):
        inventory = copy.deepcopy(self.inventory)
        inventory["proposedLevel3Contracts"][0]["executionPcs"] = []
        with self.assertRaisesRegex(
                ValueError, "failed generated contract requirements|observed exits disagree"):
            build(inventory, self.evidence, self.bindings, self.registry)

    def test_forged_entry_address_is_rejected(self):
        inventory = copy.deepcopy(self.inventory)
        inventory["proposedLevel3Contracts"][0]["entryPc"] += 4
        with self.assertRaisesRegex(ValueError, "boundary identity disagrees"):
            build(inventory, self.evidence, self.bindings, self.registry)

    def test_forged_ownership_is_rejected(self):
        inventory = copy.deepcopy(self.inventory)
        inventory["proposedLevel3Contracts"][0]["ownedPcs"].append(0xDEADBEEF)
        with self.assertRaisesRegex(ValueError, "failed generated contract requirements"):
            build(inventory, self.evidence, self.bindings, self.registry)

    def test_forged_exit_is_rejected(self):
        evidence = copy.deepcopy(self.evidence)
        contract = self.inventory["proposedLevel3Contracts"][0]
        instance = next(row for vector in evidence["vectors"] for row in vector["instances"]
                        if row["id"] == contract["instanceId"] and row["entryReached"])
        instance["observedExitTransitions"] = [[contract["entryPc"], 0xDEAD]]
        with self.assertRaisesRegex(ValueError, "observed exits disagree"):
            build(self.inventory, evidence, self.bindings, self.registry)

    def test_missing_value_binding_clause_is_rejected(self):
        registry = copy.deepcopy(self.registry)
        registry["commonClauses"] = [
            row for row in registry["commonClauses"] if row["id"] != "entry-state"]
        with self.assertRaisesRegex(ValueError, "invalid common contract clauses"):
            build(self.inventory, self.evidence, self.bindings, registry)

    def test_missing_frame_clause_is_rejected(self):
        registry = copy.deepcopy(self.registry)
        registry["commonClauses"] = [
            row for row in registry["commonClauses"]
            if row["id"] != "frames-and-termination"]
        with self.assertRaisesRegex(ValueError, "invalid common contract clauses"):
            build(self.inventory, self.evidence, self.bindings, registry)

    def test_missing_output_bytes_clause_is_rejected(self):
        registry = copy.deepcopy(self.registry)
        registry["families"]["host-write"]["extraClauses"] = []
        with self.assertRaisesRegex(ValueError, "invalid semantic clauses"):
            build(self.inventory, self.evidence, self.bindings, registry)

    def test_missing_decoded_bytes_clause_is_rejected(self):
        registry = copy.deepcopy(self.registry)
        registry["families"]["read-integer"]["extraClauses"] = []
        with self.assertRaisesRegex(ValueError, "invalid semantic clauses"):
            build(self.inventory, self.evidence, self.bindings, registry)

    def test_checked_slice_family_matches_source_operation(self):
        result = build(self.inventory, self.evidence, self.bindings, self.registry)
        rows = [row for row in result["instances"]
                if row["qualified"] == "ssz.decode__struct_1051.f"]
        self.assertEqual(len(rows), 5)
        self.assertEqual({row["contractFamily"] for row in rows},
                         {"checked-slice-selection"})
        self.assertEqual({clause["id"] for row in rows for clause in row["clauses"]
                          if clause["id"] == "checked-slice-result"},
                         {"checked-slice-result"})

    def test_missing_fork_case_is_rejected(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"] = [row for row in evidence["vectors"]
                               if row["label"] != "fork-schema-0a"]
        with self.assertRaisesRegex(ValueError, "missing fork-name evidence vector"):
            build(self.inventory, evidence, self.bindings, self.registry)

    def test_wrong_fork_case_target_is_rejected(self):
        evidence = copy.deepcopy(self.evidence)
        vector = next(row for row in evidence["vectors"] if row["label"] == "fork-schema-0a")
        instance = next(row for row in vector["instances"] if row["id"] == "fi:1:2fe4")
        instance["observedExitTransitions"][0][1] += 4
        with self.assertRaisesRegex(ValueError, "fork-name evidence route mismatch"):
            build(self.inventory, evidence, self.bindings, self.registry)


if __name__ == "__main__":
    unittest.main()
