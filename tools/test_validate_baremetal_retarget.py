#!/usr/bin/env python3

import copy
import unittest

from validate_baremetal_retarget import SEMANTIC_ANCHORS, validate_semantic_anchors


def valid_control():
    return {
        name: {"blocks": [{"instructions": [{"pc": pc, "mnemonic": mnemonic}]}]}
        for name, (pc, mnemonic) in SEMANTIC_ANCHORS.items()
    }


class SemanticAnchorTest(unittest.TestCase):
    def test_current_anchors(self):
        validate_semantic_anchors(valid_control())

    def test_rejects_dead_padding_anchor(self):
        control = valid_control()
        control["read_input"]["blocks"][0]["instructions"][0]["pc"] = 0x1018C
        with self.assertRaisesRegex(AssertionError, "unreachable semantic anchor"):
            validate_semantic_anchors(control)

    def test_rejects_wrong_instruction(self):
        control = copy.deepcopy(valid_control())
        control["write_output"]["blocks"][0]["instructions"][0]["mnemonic"] = "nop"
        with self.assertRaises(AssertionError):
            validate_semantic_anchors(control)


if __name__ == "__main__":
    unittest.main()
