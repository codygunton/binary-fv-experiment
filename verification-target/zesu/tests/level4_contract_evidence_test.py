#!/usr/bin/env python3
"""Focused unit and corruption tests for Level 4 empirical evidence."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import level4_contract_evidence as evidence


def inventory(*, count: int = 18, families: int = 15) -> dict:
    rows = []
    for index in range(count):
        rows.append({
            "id": f"boundary-{index}",
            "kind": "inlined",
            "qualified": f"ssz_raw.family{index % families}",
            "entryPc": 0x1000 + index * 0x10,
            "instructionPcs": [0x1000 + index * 0x10, 0x1004 + index * 0x10],
            "exits": [0x1004 + index * 0x10],
            "parent": "ssz_raw.decodeRaw",
            "functionInstanceIdentity": {
                "qualified": f"ssz_raw.family{index % families}",
                "sourceFile": "src/stateless/stateless/ssz_raw.zig",
                "specialization": [],
                "inlineStack": [],
            },
        })
    return {"schemaVersion": 1, "boundaries": rows}


class InventoryTests(unittest.TestCase):
    def load(self, document: dict) -> tuple[evidence.Boundary, ...]:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "inventory.json"
            path.write_text(json.dumps(document))
            return evidence.load_inventory(path)

    def test_accepts_reviewed_18_by_15_shape(self) -> None:
        boundaries = self.load(inventory())
        self.assertEqual(len(boundaries), 18)
        self.assertEqual(len({boundary.qualified for boundary in boundaries}), 15)

    def test_rejects_stale_eight_boundary_shape(self) -> None:
        with self.assertRaisesRegex(ValueError, "expected 18"):
            self.load(inventory(count=8, families=5))

    def test_rejects_wrong_family_count(self) -> None:
        with self.assertRaisesRegex(ValueError, "expected 15"):
            self.load(inventory(families=14))

    def test_rejects_entry_not_owned(self) -> None:
        document = inventory()
        document["boundaries"][0]["instructionPcs"] = [0x1004]
        with self.assertRaisesRegex(ValueError, "include its entry"):
            self.load(document)

    def test_source_less_dynamic_frame_is_retained_but_not_made_traceable(self) -> None:
        document = inventory()
        row = document["boundaries"][0]
        row["calls"] = [{
            "kind": "direct", "sourcePc": None, "targetPc": 0x3000,
            "targetIdentity": {"qualified": "mem.Allocator.free"},
            "activeCalleeExecutionPcs": [0x3000, 0x3004],
        }]
        [boundary] = self.load({**document, "boundaries": [row, *document["boundaries"][1:]]})[:1]
        self.assertEqual(boundary.calls, ())
        self.assertEqual(boundary.untraceable_calls[0]["targetPc"], 0x3000)
        del row["calls"][0]["activeCalleeExecutionPcs"]
        with self.assertRaisesRegex(ValueError, "source-less call lacks"):
            self.load(document)


class ObservationTests(unittest.TestCase):
    boundary = evidence.Boundary("x", "inlined", "ssz_raw.x", 4, (4, 8), (8,), "decodeRaw", None, (), ())
    public_keys_identity = {
        "qualified": "ssz_raw.decodePublicKeys",
        "sourceFile": "src/stateless/stateless/ssz_raw.zig",
        "specialization": [],
        "inlineStack": [],
    }

    def test_observation_records_entry_exit_and_writes(self) -> None:
        record = evidence.observation(self.boundary, [0, 4, 8], [{"pc": 8, "width": 8, "sp": 7}])
        self.assertEqual(evidence.validate_observation(self.boundary, record), [])
        self.assertEqual(record["observedStores"], [{"pc": 8, "width": 8, "sp": 7}])

    def test_each_measurable_clause_mutation_is_rejected(self) -> None:
        record = evidence.observation(self.boundary, [4, 8], [])
        self.assertEqual(evidence.mutation_checks(self.boundary, record), {
            "entry": True, "exit": True, "instruction-count": True,
        })

    def test_declared_call_and_store_mutations_are_rejected(self) -> None:
        boundary = evidence.Boundary(
            "x", "inlined", "ssz_raw.x", 4, (4, 8), (8,), "decodeRaw", None,
            ((4, 99),), ({"pc": 8, "address": 100, "width": 8, "value": 2},),
        )
        record = evidence.observation(boundary, [4, 8, 4, 99], [{"pc": 8, "address": 100, "width": 8, "value": 2, "sp": 3}])
        self.assertEqual(evidence.validate_observation(boundary, record), [])
        self.assertEqual(
            evidence.validate_observed_claims(record, record["declaredCallsReached"], record["declaredStoresReached"]), []
        )
        self.assertTrue(all(evidence.mutation_checks(boundary, record).values()))

    def test_observed_outcome_carrier_mutation_is_rejected(self) -> None:
        route = {
            "sourceIdentity": self.public_keys_identity,
            "handoff": {"sourcePc": 8, "targetPc": 12},
            "classification": "sourceReviewedOutcomePath",
            "carrierPcs": [16], "carrierPaths": [{"carrierPc": 16, "pcs": [12, 16]}],
            "registers": [], "stackDescriptors": [],
            "statusTag": {"state": "static-ELF"}, "allocation": {"state": "source-reviewed"},
            "heapArrayRep": {"state": "obligation"},
        }
        boundary = evidence.Boundary(
            "fi:120", "inlined", "ssz_raw.decodePublicKeys", 4, (4, 8), (8,), "decodeRaw",
            self.public_keys_identity, (), (), (), (route,),
        )
        record = evidence.observation(boundary, [4, 8, 12, 16], [])
        self.assertEqual(record["observedCarrierRoutes"][0]["observedCarrierPcs"], [16])
        self.assertTrue(evidence.mutation_checks(boundary, record)["outcome-carrier-pc"])

    def test_carrier_observation_never_pairs_handoff_and_pc_from_different_vectors(self) -> None:
        route = {
            "sourceIdentity": self.public_keys_identity,
            "handoff": {"sourcePc": 8, "targetPc": 12},
            "classification": "sourceReviewedOutcomePath",
            "carrierPcs": [16], "carrierPaths": [{"carrierPc": 16, "pcs": [12, 16]}],
            "registers": [], "stackDescriptors": [],
            "statusTag": {"state": "static-ELF"}, "allocation": {"state": "source-reviewed"},
            "heapArrayRep": {"state": "obligation"},
        }
        boundary = evidence.Boundary(
            "fi:120", "inlined", "ssz_raw.decodePublicKeys", 4, (4, 8), (8,), "decodeRaw",
            self.public_keys_identity, (), (), (), (route,),
        )
        first = evidence.observation(boundary, [4, 8, 12], [])
        second = evidence.observation(boundary, [4, 16], [])
        merged = evidence.merge_observations(boundary, [first, second])
        [claim] = merged["observedCarrierRoutes"]
        self.assertEqual(claim["handoffEvents"], 1)
        self.assertEqual(claim["observedCarrierPcs"], [])
        forged = {**merged, "observedCarrierRoutes": [{**claim, "observedCarrierPcs": [16]}]}
        self.assertEqual(
            evidence.validate_merged_observation(boundary, forged, [first, second]),
            ["merged production observations were changed or cross-vector forged"],
        )

    def test_carrier_observation_never_crosses_a_second_invocation_in_one_vector(self) -> None:
        route = {"sourceIdentity": self.public_keys_identity, "handoff": {"sourcePc": 8, "targetPc": 12},
                 "classification": "sourceReviewedOutcomePath", "carrierPcs": [16],
                 "carrierPaths": [{"carrierPc": 16, "pcs": [12, 16]}], "registers": [], "stackDescriptors": [],
                 "statusTag": {"state": "static-ELF"}, "allocation": {"state": "source-reviewed"},
                 "heapArrayRep": {"state": "obligation"}}
        boundary = evidence.Boundary("fi:120", "inlined", "ssz_raw.decodePublicKeys", 4, (4, 8), (8,), "decodeRaw",
                                     self.public_keys_identity, (), (), (), (route,))
        [claim] = evidence.observation(boundary, [4, 8, 12, 4, 16], [])["observedCarrierRoutes"]
        self.assertEqual(claim["observedCarrierPcs"], [])

    def test_aggregate_edges_never_join_two_vectors(self) -> None:
        boundary = evidence.Boundary(
            "x", "inlined", "ssz_raw.x", 4, (4, 8), (8,), "decodeRaw", None,
            ((4, 99),), (),
        )
        # The first trace ends at the call source; the second begins at its target. Concatenating
        # them would invent (4, 99), but the union of trace-local edge sets must not.
        first, second = [4], [99, 8]
        record = evidence.observation(
            boundary, first + second, [], edges=set(zip(first, first[1:])) | set(zip(second, second[1:])),
        )
        self.assertIn(
            "an observed declared call target disappeared",
            evidence.validate_observed_claims(record, [{"sourcePc": 4, "targetPc": 99}], []),
        )

    def test_every_unobserved_call_requires_the_exact_cleanup_certificate(self) -> None:
        public_keys = evidence.Boundary(
            "fi:120", "inlined", "ssz_raw.decodePublicKeys", 4, (4, 77764), (77764,), "decodeRaw", self.public_keys_identity,
            ((77764, 66624),), (),
        )
        self.assertEqual(evidence.validate_observation(public_keys, evidence.observation(public_keys, [4, 77764], [])), [])
        wrong_target = evidence.Boundary(
            "fi:120", "inlined", "ssz_raw.decodePublicKeys", 4, (4, 77764), (77764,), "decodeRaw", self.public_keys_identity,
            ((77764, 66628),), (),
        )
        self.assertIn(
            "declared call targets were not observed: [(77764, 66628)]",
            evidence.validate_observation(wrong_target, evidence.observation(wrong_target, [4, 77764], [])),
        )
        changed_source = evidence.Boundary(
            "fi:120", "inlined", "ssz_raw.decodePublicKeys", 4, (4, 77764), (77764,), "decodeRaw",
            {**self.public_keys_identity, "sourceFile": "different.zig"}, ((77764, 66624),), (),
        )
        self.assertIn(
            "declared call targets were not observed: [(77764, 66624)]",
            evidence.validate_observation(changed_source, evidence.observation(changed_source, [4, 77764], [])),
        )

    def test_cleanup_certificate_does_not_mask_an_observed_call_mutation(self) -> None:
        boundary = evidence.Boundary(
            "fi:120", "inlined", "ssz_raw.decodePublicKeys", 4, (4, 8, 77764), (8,), "decodeRaw", self.public_keys_identity,
            ((8, 99), (77764, 66624)), (),
        )
        record = evidence.observation(boundary, [4, 8, 99], [])
        self.assertTrue(all(evidence.mutation_checks(boundary, record).values()))

    def test_refinement_vectors_keep_accepted_and_rejected_cases(self) -> None:
        vectors = evidence.default_vectors()
        self.assertEqual(len(vectors), 14)
        self.assertTrue(any(accepted for _name, _data, accepted in vectors))
        self.assertTrue(any(not accepted for _name, _data, accepted in vectors))

    def test_trace_parser_ignores_loads_and_keeps_stores(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "trace"
            trace.write_text("E 4\nL 4 99 8 1\nS 8 100 8 2 3\n")
            self.assertEqual(evidence.parse_trace(trace), ([4], [{"pc": 8, "address": 100, "width": 8, "value": 2, "sp": 3}]))

    def test_recursive_h_r_ra_state_machine_rejects_forged_transitions(self) -> None:
        frame = {"id": "child", "sourcePc": 8, "targetPc": 100, "activeCalleeExecutionPcs": [100, 104],
                 "returnSites": [{"sourcePc": 8, "targetPc": 100, "returnPc": 12}],
                 "activeCalleeFrames": [], "cycleBackEdge": None}
        boundary = evidence.Boundary("fi:16", "inlined", "x", 4, (4, 8, 12), (12,), "fi:6", None, (), (),
                                     subtree_pcs=(4, 8, 12), handoffs=((12, 20),), reentries=((24, 4),),
                                     active_frames=(frame,))
        failures, _ = evidence.attribution_state_failures(boundary, [4, 8, 100, 104, 12, 20, 24, 4], {20, 24})
        self.assertEqual(failures, [])
        self.assertTrue(evidence.attribution_state_failures(boundary, [4, 20], {20, 24})[0])
        self.assertTrue(evidence.attribution_state_failures(boundary, [4, 12, 20, 4], {20, 24})[0])
        self.assertTrue(evidence.attribution_state_failures(boundary, [4, 8, 100, 999], {20, 24})[0])

    def test_tail_frame_rejects_foreign_pc_before_generated_completion(self) -> None:
        boundary = evidence.Boundary("x", "inlined", "x", 4, (4, 8), (8,), "fi:6", None, (), (),
                                     subtree_pcs=(4, 8), handoffs=((8, 20),), reentries=((24, 4),), active_frames=())
        tails = {(8, 100): ({8, 100, 104}, {104})}
        self.assertEqual(evidence.attribution_state_failures(boundary, [4, 8, 100, 104], {20, 24}, tails)[0], [])
        self.assertTrue(evidence.attribution_state_failures(boundary, [4, 8, 100, 999], {20, 24}, tails)[0])

    def test_tail_requires_its_exact_generated_transfer(self) -> None:
        frame = {"id": "child", "activeCalleeExecutionPcs": [100, 50, 304],
                 "returnSites": [{"sourcePc": 8, "targetPc": 100, "returnPc": 12}],
                 "activeCalleeFrames": [], "cycleBackEdge": None}
        boundary = evidence.Boundary("x", "inlined", "x", 4, (4, 8, 12), (12,), "fi:6", None, (), (),
                                     subtree_pcs=(4, 8, 12), handoffs=((12, 20),), reentries=((24, 4),),
                                     active_frames=(frame,))
        tails = {(50, 300): ({300, 304}, {304})}
        self.assertTrue(evidence.attribution_state_failures(
            boundary, [4, 8, 100, 300], {20, 24}, tails)[0])
        self.assertEqual(evidence.attribution_state_failures(
            boundary, [4, 8, 100, 50, 300, 304, 12], {20, 24}, tails)[0], [])
        self.assertTrue(evidence.attribution_state_failures(
            boundary, [4, 8, 100, 50, 300, 12], {20, 24}, tails)[0])


if __name__ == "__main__":
    unittest.main()
