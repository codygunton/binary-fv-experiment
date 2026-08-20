import unittest

from analyze_hlevel3_discharge import classify, flame_meta_instances, validate_direct_children


class Level3DischargeReviewTests(unittest.TestCase):
    def test_small_leaf_is_direct(self):
        self.assertEqual(classify("mem.readInt")[0], "direct-now")

    def test_wrapper_waits_for_shared_leaf(self):
        self.assertEqual(classify("ssz.readU32")[0], "direct-after-dependencies")

    def test_runtime_loop_retains_contract(self):
        self.assertEqual(classify("ssz.decodeByteListList")[0], "retain-contract")

    def test_unknown_operation_fails_closed(self):
        with self.assertRaises(ValueError):
            classify("unknown.operation")

    def test_read_wrapper_requires_read_child(self):
        validate_direct_children("ssz.readU32", ["mem.readInt [fi:1:test]"])
        with self.assertRaises(ValueError):
            validate_direct_children("ssz.readU32", [])

    def test_core_metadata_records_expanded_shared_body(self):
        flame = {"meta": [
            {"machineOwner": "fi:1:43a9"},
            {"machineOwner": "fn:0x15cb0"},
        ]}
        self.assertEqual(flame_meta_instances(flame), {"fi:1:43a9"})


if __name__ == "__main__":
    unittest.main()
