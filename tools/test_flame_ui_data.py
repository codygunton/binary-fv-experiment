#!/usr/bin/env python3
"""Regression checks for compact flamegraph UI payload generation."""

import unittest

from build_flame_ui_data import split_flame


class FlameUiDataTest(unittest.TestCase):
    def test_identity_and_details_stay_aligned(self) -> None:
        root_key = "root"
        child_key = "root|child"
        data = {
            "schemaVersion": 3,
            "tree": {
                "key": root_key,
                "name": "root",
                "self": 1,
                "value": 3,
                "children": [{"key": child_key, "name": "child", "self": 2, "value": 2}],
            },
            "meta": {
                root_key: {"owner": "root-owner", "qualified": "root", "src": {"text": "r"}},
                child_key: {"owner": "child-owner", "qualified": "child", "src": {"text": "c"}},
            },
            "total": 3,
            "programTotal": 3,
            "machineRegionInputs": {"target": "fixture"},
        }
        core, details = split_flame(data)
        self.assertEqual(core["tree"]["uiId"], 0)
        self.assertEqual(core["tree"]["children"][0]["uiId"], 1)
        self.assertEqual(core["meta"][1]["owner"], "child-owner")
        self.assertEqual(details[1]["src"]["text"], "c")
        self.assertNotIn("key", core["tree"])


if __name__ == "__main__":
    unittest.main()
