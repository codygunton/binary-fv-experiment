#!/usr/bin/env python3
import copy
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

from analyze import (make_report, parse_trace, reduce_trace, validate_decode_runs,
                     validate_initialized_decoded_prefixes)
from elf_identity import load_image_sha256


class EvidenceTest(unittest.TestCase):
    def setUp(self):
        self.manifest = {
            "artifact": {"kind": "ELF", "sha256": load_image_sha256(Path(sys.executable))},
            "instances": [{
                "id": "fi:1", "qualified": "child", "entryPc": 4,
                "instructionPcs": [4, 8], "executionPcs": [4, 8, 12], "exitPcs": [16],
            }],
        }
        self.trace = {
            "executed": [0, 4, 8, 12, 16],
            "executions": [
                {"pc": pc, "registers": ({"available": 2 ** 32 - 1, "values": [0] * 32}
                                           if pc in {4, 16} else None), "hostWrites": []}
                for pc in [0, 4, 8, 12, 16]
            ],
            "registers": {4: [{"available": 2 ** 32 - 1, "values": [0] * 32}]},
            "loads": [[8, 100, 8, 7, 2]], "stores": [],
        }

    def test_reduces_boundary(self):
        row = reduce_trace(self.manifest, self.trace, "ok")["instances"][0]
        self.assertTrue(row["entryReached"])
        self.assertEqual(row["executedOwnedPcs"], [4, 8])
        self.assertEqual(row["observedExitTransitions"], [[12, 16]])
        self.assertEqual(row["observedExits"][0]["afterPc"], 16)
        self.assertEqual(len(row["occurrences"]), 1)
        self.assertEqual(row["occurrences"][0]["hostWrites"], [])
        self.assertEqual(row["occurrences"][0]["memoryWrites"], [])
        self.assertEqual(row["memoryAccessSummary"], {"loads": 1, "stores": 0})

    def test_pairs_each_occurrence_with_its_own_host_writes(self):
        trace = copy.deepcopy(self.trace)
        first = trace["executions"][2]
        first["hostWrites"] = [{"pc": 8, "address": 100, "bytes": "01"}]
        second = copy.deepcopy(trace["executions"][1:])
        second[1]["hostWrites"] = [{"pc": 8, "address": 200, "bytes": "02"}]
        trace["executions"].extend(second)
        trace["registers"][4].append(copy.deepcopy(trace["registers"][4][0]))
        row = reduce_trace(self.manifest, trace, "twice")["instances"][0]
        self.assertEqual([[write["bytes"] for write in occurrence["hostWrites"]]
                          for occurrence in row["occurrences"]], [["01"], ["02"]])

    def test_pairs_each_occurrence_with_its_own_memory_accesses(self):
        trace = copy.deepcopy(self.trace)
        trace["loads"] = []
        trace["stores"] = [[8, 100, 8, 1, 2]]
        trace["executions"].extend(copy.deepcopy(trace["executions"][1:]))
        trace["registers"][4].append(copy.deepcopy(trace["registers"][4][0]))
        trace["stores"].append([8, 200, 8, 2, 6])
        row = reduce_trace(self.manifest, trace, "twice")["instances"][0]
        self.assertEqual([[access["address"] for access in occurrence["memoryWrites"]]
                          for occurrence in row["occurrences"]], [[100], [200]])

    def test_missing_entry_is_not_inferred(self):
        trace = copy.deepcopy(self.trace)
        trace["registers"] = {}
        self.assertFalse(reduce_trace(self.manifest, trace, "missing")["instances"][0]["entryReached"])

    def test_rejects_wrong_artifact(self):
        with tempfile.TemporaryDirectory() as directory:
            elf = Path(directory) / "elf"
            shutil.copyfile(sys.executable, elf)
            self.manifest["artifact"]["sha256"] = "forged"
            with self.assertRaisesRegex(ValueError, "digests differ"):
                make_report(self.manifest, elf, [])

    def test_rejects_deleted_entry_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            elf = Path(directory) / "elf"
            trace = Path(directory) / "trace"
            shutil.copyfile(sys.executable, elf)
            trace.write_text("E 4\nE 8\nE 12\nE 16\n")
            with self.assertRaisesRegex(ValueError, "entry coverage is incomplete"):
                make_report(self.manifest, elf, [("mutated", trace)])

    def test_parser_rejects_bad_register_record(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("R 4 0\n")
            with self.assertRaisesRegex(ValueError, "malformed"):
                parse_trace(trace)

    def test_parser_reads_host_write_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("E 65972\nB 65972 4096 3 0102ff\n")
            self.assertEqual(parse_trace(trace)["hostWrites"], [{
                "pc": 65972, "address": 4096, "bytes": "0102ff",
            }])

    def test_parser_reads_empty_host_write(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("E 65936\nB 65936 4096 0 \n")
            self.assertEqual(parse_trace(trace)["hostWrites"], [{
                "pc": 65936, "address": 4096, "bytes": "",
            }])

    def test_parser_separates_terminal_output(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("E 66000\nO 66000 4096 2 aabb\n")
            parsed = parse_trace(trace)
            self.assertEqual(parsed["hostWrites"], [])
            self.assertEqual(parsed["terminalOutputs"], [{
                "pc": 66000, "address": 4096, "bytes": "aabb",
            }])

    def test_parser_reads_initialized_memory_window(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("W 85296 4096 3 0102ff\n")
            self.assertEqual(parse_trace(trace)["memoryWindows"], [{
                "pc": 85296, "address": 4096, "bytes": "0102ff",
            }])

    def test_parser_rejects_wrong_memory_window_width(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("W 85296 4096 4 0102ff\n")
            with self.assertRaisesRegex(ValueError, "malformed"):
                parse_trace(trace)

    def test_rejects_missing_initialized_decoded_prefix(self):
        vectors = [{"label": "ok"}]
        with self.assertRaisesRegex(ValueError, "do not match"):
            validate_initialized_decoded_prefixes(
                vectors, [("ok", {"executed": [0x14d30], "memoryWindows": []})])

    def test_rejects_stale_decoded_prefix_capture_pc(self):
        with self.assertRaisesRegex(ValueError, "no successful vectors"):
            validate_initialized_decoded_prefixes(
                [{"label": "ok"}], [("ok", {"executed": [], "memoryWindows": []})])

    def test_rejects_missing_exit_snapshot(self):
        trace = copy.deepcopy(self.trace)
        trace["executions"][-1]["registers"] = None
        with self.assertRaisesRegex(ValueError, "missing exit register snapshot"):
            reduce_trace(self.manifest, trace, "missing-exit")

    def test_rejects_forged_decode_input_size(self):
        from analyze import validate_bindings
        manifest = copy.deepcopy(self.manifest)
        manifest["instances"][0]["qualified"] = "ssz_decode_root.decodeInput"
        bindings = {
            "artifact": manifest["artifact"],
            "instances": [{"id": "fi:1", "qualified": "ssz_decode_root.decodeInput", "bindings": [
                {"name": "alloc", "addressRegister": 11},
            ]}],
        }
        snapshot = [0] * 32
        snapshot[13], snapshot[12] = 4, 100
        vector = {"label": "sample", "instances": [{
            "qualified": "ssz_decode_root.decodeInput", "entryReached": True,
            "entryRegisters": [{"values": snapshot}],
            "memoryAccesses": [{"kind": "load", "address": 100}],
        }]}
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "input"
            fixture.write_bytes(b"wrong")
            with self.assertRaisesRegex(ValueError, "input_size mismatch"):
                validate_bindings(manifest, bindings, [vector], {"sample": fixture})

    def test_rejects_forged_decode_result_location(self):
        from analyze import validate_bindings
        manifest = {"artifact": {"sha256": "digest"}, "instances": [
            {"id": "decode", "qualified": "ssz_decode_root.decodeInput"},
            {"id": "success", "qualified": "ssz_decode_observation.writeSuccess"},
        ]}
        bindings = {"artifact": manifest["artifact"], "instances": [
            {"id": "decode", "qualified": "ssz_decode_root.decodeInput", "bindings": [
                {"name": "alloc", "addressRegister": 11},
            ]},
            {"id": "success", "qualified": "ssz_decode_observation.writeSuccess",
             "bindings": []},
        ]}
        decode_regs, success_regs = [0] * 32, [0] * 32
        decode_regs[10], decode_regs[13], decode_regs[12] = 1000, 4, 100
        success_regs[10] = 2177
        vector = {"label": "sample", "instances": [
            {"qualified": "ssz_decode_root.decodeInput", "entryReached": True,
             "entryRegisters": [{"values": decode_regs}],
             "memoryAccesses": [{"kind": "load", "address": 100}]},
            {"qualified": "ssz_decode_observation.writeSuccess", "entryReached": True,
             "entryRegisters": [{"values": success_regs}], "memoryAccesses": []},
        ]}
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "input"
            fixture.write_bytes(b"data")
            with self.assertRaisesRegex(ValueError, "decoded-result ABI slot mismatch"):
                validate_bindings(manifest, bindings, [vector], {"sample": fixture})

    def test_decode_run_records_exact_observed_interval(self):
        manifest = {"instances": [
            {"qualified": "ssz_decode_root.decodeInput", "entryPc": 4},
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
            {"qualified": "ssz_decode_root.decodeInput", "entryPc": 4},
            {"qualified": "ssz_decode_observation.writeSuccess", "entryPc": 20},
            {"qualified": "ssz_decode_observation.writeFailure", "entryPc": 24},
        ]}
        trace = {"executed": [4, 8, 12], "registers": {4: [{"values": [0] * 32}]}}
        with self.assertRaisesRegex(ValueError, "outcome boundary absent"):
            validate_decode_runs(manifest, [("bad", trace)])


if __name__ == "__main__":
    unittest.main()
