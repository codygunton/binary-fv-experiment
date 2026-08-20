import unittest

from make_minimal_ssz import activation_timestamp_input, blob_transaction_input


class MinimalSszFixtureTests(unittest.TestCase):
    def test_activation_timestamp_layout(self):
        data = activation_timestamp_input()
        self.assertEqual(int.from_bytes(data[14:18], "little"), 672)
        self.assertEqual(int.from_bytes(data[666:674], "little"), 1)

    def test_blob_transaction_has_type_and_one_hash(self):
        data = blob_transaction_input()
        transaction = data[606:655]
        self.assertEqual(transaction[0], 3)
        self.assertEqual(transaction.count(bytes((0xA0,))), 1)
        self.assertEqual(len(transaction), 49)


if __name__ == "__main__":
    unittest.main()
