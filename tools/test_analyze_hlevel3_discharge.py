import unittest

from analyze_hlevel3_discharge import (
    classify, classify_instance, flame_meta_instances, validate_direct_children,
)


class Level3DischargeReviewTests(unittest.TestCase):
    def test_small_leaf_is_direct(self):
        self.assertEqual(classify("mem.readInt")[0], "direct-now")

    def test_contiguous_checked_slice_is_direct(self):
        self.assertEqual(
            classify_instance("fi:1:351c", "ssz.decode__struct_1051.f")[0],
            "direct-now",
        )

    def test_checked_slice_reentry_keeps_contract(self):
        for instance_id in ("fi:1:34fd", "fi:1:3541", "fi:1:3566", "fi:1:358b"):
            self.assertEqual(
                classify_instance(instance_id, "ssz.decode__struct_1051.f")[0],
                "retain-contract",
            )

    def test_reentry_exception_rejects_changed_source(self):
        with self.assertRaisesRegex(ValueError, "changed source operation"):
            classify_instance("fi:1:34fd", "ssz.readU32")

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
