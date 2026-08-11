#!/usr/bin/env python3
import copy
import hashlib
import tempfile
import unittest
from pathlib import Path

from analyze import make_report, parse_trace, reduce_trace, validate_decode_runs


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
            "executions": [
                {"pc": pc, "registers": ({"available": 2 ** 32 - 1, "values": [0] * 32}
                                           if pc in {4, 16} else None)}
                for pc in [0, 4, 8, 12, 16]
            ],
            "registers": {4: [{"available": 2 ** 32 - 1, "values": [0] * 32}]},
            "loads": [[8, 100, 8, 7]], "stores": [],
        }

    def test_reduces_boundary(self):
        row = reduce_trace(self.manifest, self.trace, "ok")["instances"][0]
        self.assertTrue(row["entryReached"])
        self.assertEqual(row["executedOwnedPcs"], [4, 8])
        self.assertEqual(row["observedExitTransitions"], [[12, 16]])
        self.assertEqual(row["observedExits"][0]["afterPc"], 16)

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

    def test_rejects_missing_exit_snapshot(self):
        trace = copy.deepcopy(self.trace)
        trace["executions"][-1]["registers"] = None
        with self.assertRaisesRegex(ValueError, "missing exit register snapshot"):
            reduce_trace(self.manifest, trace, "missing-exit")

    def test_rejects_forged_decode_input_size(self):
        from analyze import validate_bindings
        manifest = copy.deepcopy(self.manifest)
        manifest["instances"][0]["qualified"] = "ssz.decode"
        bindings = {
            "artifact": manifest["artifact"],
            "instances": [{"id": "fi:1", "qualified": "ssz.decode", "bindings": [
                {"name": "input_ptr", "machineRegister": 23},
                {"name": "input_size", "machineRegister": 18},
            ]}],
        }
        snapshot = [0] * 32
        snapshot[18], snapshot[23] = 4, 100
        vector = {"label": "sample", "instances": [{
            "qualified": "ssz.decode", "entryReached": True,
            "entryRegisters": [{"values": snapshot}],
            "memoryAccesses": [{"kind": "load", "address": 100}],
        }]}
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "input"
            fixture.write_bytes(b"wrong")
            with self.assertRaisesRegex(ValueError, "input_size mismatch"):
                validate_bindings(manifest, bindings, [vector], {"sample": fixture})

    def test_decode_run_records_exact_observed_interval(self):
        manifest = {"instances": [
            {"qualified": "ssz.decode", "entryPc": 4},
            {"qualified": "ssz_decode_observation.writeSuccess", "entryPc": 20},
            {"qualified": "ssz_decode_observation.writeFailure", "entryPc": 24},
        ]}
        before, after = [0] * 32, [0] * 32
        after[10] = 100
        trace = {"executed": [4, 8, 12, 20], "registers": {
            4: [{"values": before}], 20: [{"values": after}],
        }}
        report = validate_decode_runs(manifest, [("ok", trace)])[0]
        self.assertEqual(report["outcome"], "success")
        self.assertEqual(report["observedStepCount"], 3)
        self.assertEqual(report["changedIntegerRegisters"], [10])
        self.assertEqual(report["successResultAddress"], 100)

    def test_decode_run_rejects_missing_outcome(self):
        manifest = {"instances": [
            {"qualified": "ssz.decode", "entryPc": 4},
            {"qualified": "ssz_decode_observation.writeSuccess", "entryPc": 20},
            {"qualified": "ssz_decode_observation.writeFailure", "entryPc": 24},
        ]}
        trace = {"executed": [4, 8, 12], "registers": {4: [{"values": [0] * 32}]}}
        with self.assertRaisesRegex(ValueError, "outcome boundary absent"):
            validate_decode_runs(manifest, [("bad", trace)])


if __name__ == "__main__":
    unittest.main()
