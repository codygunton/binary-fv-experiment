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
            "absorbedInstructionPcs": [],
            "executionPcs": [entry],
            "exitPcs": [entry + 4],
        })
        instruction = {"pc": entry, "mnemonic": "addi", "bytes": "13000000"}
        if qualified in ("read_input", "write_output", "zkvm_exit"):
            instruction = {"pc": entry, "mnemonic": "ecall", "bytes": "73000000"}
        functions.append({
            "name": qualified,
            "start": entry,
            "blocks": [{"instructions": [instruction]}],
        })
    functions.append({
        "name": "write_output",
        "start": 0x2000,
        "blocks": [{"instructions": [{
            "pc": 0x2000, "mnemonic": "ecall", "bytes": "73000000",
        }]}],
    })
    main_pcs = list(range(0x1000, 0x1080, 4))
    instances[0]["executionPcs"] = [0x1000, 0x1064, 0x1068, 0x106c, 0x1070]
    functions.append({
        "name": "ssz_decode_root.main",
        "start": 0x1000,
        "blocks": [{"instructions": [
            {"pc": pc, "mnemonic": "addi", "operands": "zero, zero, 0",
             "bytes": "13000000"}
            for pc in main_pcs
        ]}],
    })
    return (
        {"artifact": {"identityScope": "ELF PT_LOAD memory image", "sha256": SHA},
         "instances": instances},
        {"artifact": {"identityScope": "ELF PT_LOAD memory image", "sha256": SHA},
         "functions": functions, "functionInstances": [{
            "kind": "concrete",
            "parent": None,
            "name": "ssz_decode_root.main",
            "entryPc": 0x1000,
            "pcs": main_pcs,
        }]},
    )


class GenerateLevel1LeanTests(unittest.TestCase):
    def test_generates_bare_metal_context_addresses(self):
        manifest, cfg = fixture()
        output = generate(manifest, cfg)
        self.assertIn("def inputBufferAddress : Nat := 0x2001a000", output)
        self.assertIn("def ioContextAddress : Nat := 0x2401a0b8", output)
        self.assertIn("def mainGlueInstructionCount : Nat := 24", output)
        self.assertIn("(0x1004, 0x00000013)", output)
        self.assertIn("def mainGlueWordAt1004 : Nat := 0x00000013", output)

    def test_rejects_artifact_mismatch(self):
        manifest, cfg = fixture()
        cfg["artifact"]["sha256"] = "cd" * 32
        with self.assertRaisesRegex(ValueError, "different load images"):
            generate(manifest, cfg)

    def test_rejects_non_word_level0_instruction(self):
        manifest, cfg = fixture()
        cfg["functions"][-1]["blocks"][0]["instructions"][1]["bytes"] = "1300"
        with self.assertRaisesRegex(ValueError, "not a four-byte word"):
            generate(manifest, cfg)


if __name__ == "__main__":
    unittest.main()
