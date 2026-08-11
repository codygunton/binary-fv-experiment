#!/usr/bin/env python3
import copy
import hashlib
import tempfile
import unittest
from pathlib import Path

from analyze import make_report, parse_trace, reduce_trace


class EvidenceTest(unittest.TestCase):
    def setUp(self):
        self.manifest = {
            "artifact": {"kind": "ELF", "sha256": hashlib.sha256(b"elf").hexdigest()},
            "instances": [{
                "id": "fi:1", "qualified": "child", "entryPc": 4,
                "instructionPcs": [4, 8], "executionPcs": [4, 8, 12],
            }],
        }
        self.trace = {
            "executed": [0, 4, 8, 12, 16],
            "registers": {4: [[0] * 32]}, "loads": [[8, 100, 8, 7]], "stores": [],
        }

    def test_reduces_boundary(self):
        row = reduce_trace(self.manifest, self.trace, "ok")["instances"][0]
        self.assertTrue(row["entryReached"])
        self.assertEqual(row["executedOwnedPcs"], [4, 8])
        self.assertEqual(row["observedExitTransitions"], [[12, 16]])

    def test_missing_entry_is_not_inferred(self):
        trace = copy.deepcopy(self.trace)
        trace["registers"] = {}
        self.assertFalse(reduce_trace(self.manifest, trace, "missing")["instances"][0]["entryReached"])

    def test_rejects_wrong_artifact(self):
        with tempfile.TemporaryDirectory() as directory:
            elf = Path(directory) / "elf"
            elf.write_bytes(b"wrong")
            with self.assertRaisesRegex(ValueError, "digests differ"):
                make_report(self.manifest, elf, [])

    def test_rejects_deleted_entry_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            elf = Path(directory) / "elf"
            trace = Path(directory) / "trace"
            elf.write_bytes(b"elf")
            trace.write_text("E 4\nE 8\nE 12\nE 16\n")
            with self.assertRaisesRegex(ValueError, "entry coverage is incomplete"):
                make_report(self.manifest, elf, [("mutated", trace)])

    def test_parser_rejects_bad_register_record(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("R 4 0\n")
            with self.assertRaisesRegex(ValueError, "malformed"):
                parse_trace(trace)


if __name__ == "__main__":
    unittest.main()
