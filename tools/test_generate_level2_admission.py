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
        if len(INPUTS) != 7:
            raise RuntimeError(
                "expected MANIFEST EVIDENCE BINDINGS CFG REGISTRY PROFILES DEFECT_AUDITS")
        cls.documents = [json.loads(Path(path).read_text()) for path in INPUTS]
        cls.module = admission

    def test_reviews_exact_inventory_without_admitting_contracts(self):
        result = self.module.build(*self.documents)
        self.assertEqual(len(result["instances"]), 20)
        self.assertEqual({row["semanticReview"]["status"] for row in result["instances"]},
                         {"reviewed"})
        self.assertEqual({row["contractStatus"] for row in result["instances"]},
                         {"not-admitted"})
        self.assertTrue(all(
            row["measured"]["entryToExitCompatibility"]["status"] == "measured-compatible"
            and row["measured"]["entryToExitCompatibility"]["occurrenceCount"] > 0
            for row in result["instances"]))
        self.assertTrue(all(row["proofOnly"] == [
            "Sail choiceState/tags/sailOutput preservation is machine-execution bookkeeping, "
            "not an empirically observable function result",
        ] for row in result["instances"]))
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
            "public-key-overflow", "versioned-hash-overflow", "one-transaction",
            "one-withdrawal",
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
        transactions = next(row for row in result["instances"]
                            if row["leanName"] == "writeSuccessTransactions")
        self.assertEqual(transactions["measured"]["validatedEntryBinding"], {
            "countRegister": 10, "encoding": "little-u64-prefix",
        })
        self.assertIn(0, transactions["measured"]["observedCollectionCounts"])
        self.assertTrue(any(count > 0
                            for count in transactions["measured"]["observedCollectionCounts"]))
        withdrawals = next(row for row in result["instances"]
                           if row["leanName"] == "writeSuccessWithdrawals")
        self.assertEqual(withdrawals["measured"]["validatedEntryBinding"], {
            "countRegister": 9, "encoding": "little-u64-prefix",
        })
        self.assertIn(0, withdrawals["measured"]["observedCollectionCounts"])
        self.assertTrue(any(count > 0
                            for count in withdrawals["measured"]["observedCollectionCounts"]))
        hashes = next(row for row in result["instances"]
                      if row["leanName"] == "writeSuccessHashes")
        self.assertEqual(hashes["measured"]["validatedEntryBinding"], {
            "countRegister": 8, "encoding": "little-u64-prefix",
        })
        self.assertIn(0, hashes["measured"]["observedCollectionCounts"])
        self.assertTrue(any(count > 0
                            for count in hashes["measured"]["observedCollectionCounts"]))
        self.assertEqual(result["summary"]["instanceCount"], 20)
        self.assertEqual(result["summary"]["schemaCount"], 6)
        self.assertEqual(result["measuredDefectCensus"]["totalInstanceCount"], 20)
        self.assertEqual(result["measuredDefectCensus"]["failingInstanceCount"], 8)
        encoder = next(row for row in result["contractSchemas"]
                       if row["name"] == "encoder-call")
        self.assertTrue(encoder["entryAndExecutionReady"])
        representatives = {
            row["name"]: row["level3RepresentativeProof"]
            for row in result["contractSchemas"]
        }
        self.assertEqual(representatives["constant-encoder"],
                         "writeSuccessPrefixInstanceContract")
        self.assertEqual(representatives["raw-encoder"],
                         "writeSuccessPrevRandaoInstanceContract")
        self.assertEqual({item["schema"] for item in result["workItems"]
                          if item["clause"] == "representative-proof"},
                         {"decode-inline", "encoder-call", "inline-array-encoder"})
        self.assertFalse(any(item["schema"] == "encoder-call" and
                             item["status"] == "contradiction"
                             for item in result["workItems"]))

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

    def test_requires_clause_registry(self):
        with self.assertRaisesRegex(ValueError, "registry is required"):
            self.module.build(*self.documents[:4])

    def test_requires_representative_proof_work(self):
        documents = copy.deepcopy(self.documents)
        documents[4]["schemas"]["encoder-call"].pop("representativeProofWork")
        with self.assertRaisesRegex(ValueError, "encoder-call lacks representative proof work"):
            self.module.build(*documents)

    def test_requires_defect_audits(self):
        with self.assertRaisesRegex(ValueError, "defect audits are required"):
            self.module.build(*self.documents[:6])

    def test_rejects_incomplete_clause_inventory(self):
        documents = copy.deepcopy(self.documents)
        documents[4]["schemas"]["raw-encoder"]["instanceNames"].pop()
        with self.assertRaisesRegex(ValueError, "does not cover exact inventory"):
            self.module.build(*documents)

    def test_rejects_malformed_clause_support(self):
        documents = copy.deepcopy(self.documents)
        del documents[4]["schemas"]["raw-encoder"]["clauses"][1]["support"]["mutationTest"]
        with self.assertRaisesRegex(ValueError, "malformed support"):
            self.module.build(*documents)

    def test_rejects_unsupported_entry_or_execution_requirement(self):
        documents = copy.deepcopy(self.documents)
        support = documents[4]["schemas"]["raw-encoder"]["clauses"][0]["support"]
        support.clear()
        support.update({"kind": "missing", "remaining": "no configured machine evidence"})
        with self.assertRaisesRegex(ValueError, "unsupported entry or execution requirement"):
            self.module.build(*documents)

    def test_rejects_forged_fixed_write(self):
        evidence = copy.deepcopy(self.documents[1])
        row = next(row for vector in evidence["vectors"] if vector["label"] == "minimal"
                   for row in vector["instances"] if row["id"] == "fi:1:3d4e")
        row["hostWrites"][0]["bytes"] = "0053535a0101"
        with self.assertRaisesRegex(ValueError, "fixed source write mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3],
                              self.documents[4], self.documents[5])

    def test_rejects_forged_fixed_pointer_binding(self):
        evidence = copy.deepcopy(self.documents[1])
        row = next(row for vector in evidence["vectors"] if vector["label"] == "minimal"
                   for row in vector["instances"] if row["id"] == "fi:1:3d77")
        row["entryRegisters"][0]["values"][10] += 1
        with self.assertRaisesRegex(ValueError, "fixed source pointer binding mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3],
                              self.documents[4], self.documents[5])

    def test_rejects_forged_boolean_value_binding(self):
        evidence = copy.deepcopy(self.documents[1])
        row = next(row for vector in evidence["vectors"] if vector["label"] == "minimal"
                   for row in vector["instances"] if row["id"] == "fi:1:4276")
        row["occurrences"][0]["entryRegisters"]["values"][10] ^= 1
        with self.assertRaisesRegex(ValueError, "boolean entry/output binding mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3],
                              self.documents[4], self.documents[5])

    def test_rejects_forged_byte_slice_pointer_binding(self):
        evidence = copy.deepcopy(self.documents[1])
        rows = (row for vector in evidence["vectors"] for row in vector["instances"]
                if row["id"] == "fi:1:4333")
        occurrence = next(occurrence for row in rows for occurrence in row["occurrences"]
                          if occurrence["entryRegisters"]["values"][11] > 0)
        occurrence["entryRegisters"]["values"][10] += 1
        with self.assertRaisesRegex(ValueError, "byte-slice pointer/length binding mismatch"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3],
                              self.documents[4], self.documents[5])

    def test_rejects_forged_collection_count_bindings(self):
        ids = {
            "fi:1:3e96": "writeSuccessTransactions",
            "fi:1:40af": "writeSuccessWithdrawals",
            "fi:1:4116": "writeSuccessHashes",
        }
        for instance_id, name in ids.items():
            with self.subTest(name=name):
                occurrence = next(
                    occurrence
                    for vector in self.documents[1]["vectors"]
                    for row in vector["instances"] if row["id"] == instance_id
                    for occurrence in row["occurrences"])
                original = occurrence["hostWrites"][0]["bytes"]
                occurrence["hostWrites"][0]["bytes"] = "0100000000000000"
                try:
                    with self.assertRaisesRegex(ValueError, f"{name} count binding mismatch"):
                        self.module.build(*self.documents)
                finally:
                    occurrence["hostWrites"][0]["bytes"] = original

    def test_requires_nonempty_collection_evidence(self):
        vector = next(row for row in self.documents[1]["vectors"]
                      if row["label"] == "one-transaction")
        instance = next(row for row in vector["instances"] if row["id"] == "fi:1:3e96")
        occurrence = instance["occurrences"][0]
        original_count = occurrence["entryRegisters"]["values"][10]
        original_bytes = occurrence["hostWrites"][0]["bytes"]
        occurrence["entryRegisters"]["values"][10] = 0
        occurrence["hostWrites"][0]["bytes"] = "0000000000000000"
        try:
            with self.assertRaisesRegex(
                    ValueError, "writeSuccessTransactions lacks empty/nonempty evidence"):
                self.module.build(*self.documents)
        finally:
            occurrence["entryRegisters"]["values"][10] = original_count
            occurrence["hostWrites"][0]["bytes"] = original_bytes

    def test_requires_empty_collection_evidence(self):
        evidence = copy.deepcopy(self.documents[1])
        for vector in evidence["vectors"]:
            row = next(row for row in vector["instances"] if row["id"] == "fi:1:3e96")
            for occurrence in row["occurrences"]:
                if occurrence["entryRegisters"]["values"][10] == 0:
                    occurrence["entryRegisters"]["values"][10] = 1
                    occurrence["hostWrites"][0]["bytes"] = "0100000000000000"
        with self.assertRaisesRegex(
                ValueError, "writeSuccessTransactions lacks empty/nonempty evidence"):
            self.module.build(self.documents[0], evidence, self.documents[2], self.documents[3],
                              self.documents[4], self.documents[5])

if __name__ == "__main__":
    unittest.main()
