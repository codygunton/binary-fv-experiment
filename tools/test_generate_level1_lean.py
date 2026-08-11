#!/usr/bin/env python3

import copy
import unittest

from generate_level1_lean import NAMES, generate


SHA = "ab" * 32


def fixture() -> tuple[dict, dict]:
    instances = []
    functions = []
    for index, qualified in enumerate(NAMES):
        entry = 0x1000 + 0x20 * index
        instances.append({
            "qualified": qualified,
            "entryPc": entry,
            "instructionPcs": [entry],
            "executionPcs": [entry],
        })
        instruction = {"pc": entry, "mnemonic": "addi", "bytes": "13000000"}
        if qualified in ("read_input", "write_output", "zkvm_exit"):
            instruction = {"pc": entry, "mnemonic": "ecall", "bytes": "73000000"}
        functions.append({
            "start": entry,
            "blocks": [{"instructions": [instruction]}],
        })
    return (
        {"artifact": {"sha256": SHA}, "instances": instances},
        {"artifact": {"sha256": SHA}, "functions": functions},
    )


class GenerateLevel1LeanTests(unittest.TestCase):
    def test_generates_exact_syscall_pcs(self):
        manifest, cfg = fixture()
        output = generate(manifest, cfg)
        self.assertIn("def readInputEcallPc : Nat := 0x1000", output)
        self.assertIn("def writeOutputEcallPc : Nat := 0x1020", output)
        self.assertIn("def zkvmExitEcallPc : Nat := 0x1040", output)

    def test_rejects_noncanonical_ecall(self):
        manifest, cfg = fixture()
        changed = copy.deepcopy(cfg)
        changed["functions"][0]["blocks"][0]["instructions"][0]["bytes"] = "00000000"
        with self.assertRaisesRegex(ValueError, "canonical ecall"):
            generate(manifest, changed)

    def test_rejects_artifact_mismatch(self):
        manifest, cfg = fixture()
        cfg["artifact"]["sha256"] = "cd" * 32
        with self.assertRaisesRegex(ValueError, "different ELFs"):
            generate(manifest, cfg)


if __name__ == "__main__":
    unittest.main()
