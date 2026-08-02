#!/usr/bin/env python3

import unittest

import level_refinement_vectors as evidence


class LevelRefinementVectorTests(unittest.TestCase):
    def test_every_deep_contract_has_accepted_and_rejected_vectors(self) -> None:
        by_contract = {}
        for vector in evidence.vectors():
            by_contract.setdefault(vector.qualified, set()).add(vector.valid)
        self.assertEqual(
            by_contract,
            {
                "ssz_raw.decodeNewPayloadRequest": {False, True},
                "ssz_raw.decodeExecutionWitness": {False, True},
                "ssz_raw.decodeChainConfig": {False, True},
                "ssz_raw.decodePublicKeys": {False, True},
            },
        )

    def test_vectors_have_unique_names(self) -> None:
        names = [vector.name for vector in evidence.vectors()]
        self.assertEqual(len(names), len(set(names)))

    def test_public_key_mutation_reaches_nondivisible_length(self) -> None:
        vector = next(v for v in evidence.vectors() if v.name == "public-keys-nondivisible")
        public_keys_start = 2 + int.from_bytes(vector.data[14:18], "little")
        self.assertEqual(len(vector.data) - public_keys_start, 64)

    def test_each_rejection_changes_an_accepted_fixture(self) -> None:
        accepted = {v.data for v in evidence.vectors() if v.valid}
        for vector in evidence.vectors():
            if not vector.valid:
                self.assertNotIn(vector.data, accepted)


if __name__ == "__main__":
    unittest.main()
