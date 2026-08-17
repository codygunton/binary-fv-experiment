#!/usr/bin/env python3

import copy
import json
import unittest
from pathlib import Path

from level2_contract_execution_evidence import evaluate_instance


PROFILES = json.loads(
    (Path(__file__).with_name("level2_contract_evidence_profiles.json")).read_text())


def occurrence(stack=0x10000):
    before = [0] * 32
    after = [0] * 32
    before[1] = after[1] = 0x1234
    before[2] = after[2] = stack
    for register in [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]:
        before[register] = after[register] = register * 17
    return {
        "entryRegisters": {"available": 2 ** 32 - 1, "values": before},
        "afterPc": 0x2000,
        "afterRegisters": {"available": 2 ** 32 - 1, "values": after},
        "hostWrites": [{"pc": 0x10190, "address": stack - 8, "bytes": "00"}],
        "memoryWrites": [
            {"kind": "store", "pc": 0x200, "address": stack - 8, "width": 8, "value": 1},
            {"kind": "store", "pc": 0x10198, "address": 0x2401a0c0, "width": 8, "value": 2},
            {"kind": "store", "pc": 0x1019c, "address": 0x2401a0c8, "width": 8, "value": 1},
        ],
        "executedInstructionCount": 9,
    }


class ContractExecutionEvidenceTests(unittest.TestCase):
    def test_accepts_complete_called_occurrence(self):
        report = evaluate_instance(
            "writeSuccessInt", "encoder-call", [occurrence()], PROFILES)
        self.assertEqual(report["status"], "measured-compatible")
        self.assertEqual(report["occurrenceCount"], 1)

    def test_rejects_missing_exit_snapshot(self):
        sample = occurrence()
        sample["afterRegisters"] = None
        with self.assertRaisesRegex(ValueError, "no exit register snapshot"):
            evaluate_instance("writeSuccessInt", "encoder-call", [sample], PROFILES)

    def test_rejects_empty_execution(self):
        sample = occurrence()
        sample["executedInstructionCount"] = 0
        with self.assertRaisesRegex(ValueError, "empty execution"):
            evaluate_instance("writeSuccessInt", "encoder-call", [sample], PROFILES)

    def test_rejects_misaligned_stack(self):
        with self.assertRaisesRegex(ValueError, "misaligned entry stack"):
            evaluate_instance("writeSuccessInt", "encoder-call", [occurrence(0x10001)], PROFILES)

    def test_rejects_small_stack(self):
        sample = occurrence(0)
        with self.assertRaisesRegex(ValueError, "child frame underflows"):
            evaluate_instance("writeSuccessInt", "encoder-call", [sample], PROFILES)

    def test_rejects_changed_preserved_register(self):
        sample = occurrence()
        sample["afterRegisters"]["values"][8] += 1
        with self.assertRaisesRegex(ValueError, "changed preserved registers"):
            evaluate_instance("writeSuccessInt", "encoder-call", [sample], PROFILES)

    def test_rejects_store_outside_frame(self):
        sample = occurrence()
        sample["memoryWrites"].append(
            {"kind": "store", "pc": 0x204, "address": 0xdeadbeef, "width": 8, "value": 0})
        with self.assertRaisesRegex(ValueError, "stores outside its declared frame"):
            evaluate_instance("writeSuccessInt", "encoder-call", [sample], PROFILES)

    def test_rejects_missing_host_write(self):
        sample = occurrence()
        sample["hostWrites"] = []
        with self.assertRaisesRegex(ValueError, "emitted no host write"):
            evaluate_instance("writeSuccessInt", "encoder-call", [sample], PROFILES)

    def test_rejects_stack_overlapping_output_context(self):
        with self.assertRaisesRegex(ValueError, "stack overlaps output context"):
            evaluate_instance(
                "writeSuccessInt", "encoder-call", [occurrence(0x2401a0d0)], PROFILES)

    def test_rejects_raw_source_store_overlap(self):
        sample = occurrence()
        sample["memoryWrites"] = sample["memoryWrites"][1:]
        sample["entryRegisters"]["values"][10] = 0x2401a0c0
        with self.assertRaisesRegex(ValueError, "source overlaps a machine store"):
            evaluate_instance("writeSuccessRawLine135", "raw-encoder", [sample], PROFILES)

    def test_profile_mutation_cannot_remove_output_store_region(self):
        profiles = copy.deepcopy(PROFILES)
        profiles["schemas"]["encoder-call"]["allowedStoreRegions"] = \
            profiles["schemas"]["encoder-call"]["allowedStoreRegions"][:1]
        with self.assertRaisesRegex(ValueError, "stores outside its declared frame"):
            evaluate_instance("writeSuccessInt", "encoder-call", [occurrence()], profiles)


if __name__ == "__main__":
    unittest.main()
