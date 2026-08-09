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


def bound_spec(document: dict) -> dict:
    return {
        "schemaVersion": 2,
        "claim": "finite sampled ceiling; universal validity remains an assumption",
        "metrics": {"rootSize": "root vector length is a conservative observable"},
        "bounds": [
            {"id": row["id"], "family": row["qualified"], "kind": "constant", "constant": 2}
            for row in document["boundaries"]
        ],
    }


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

    def test_evidence_bound_spec_lists_every_reviewed_occurrence(self) -> None:
        path = Path(__file__).parents[1] / "level4-bound-spec.json"
        document = json.loads(path.read_text())
        bounds = document["bounds"]
        self.assertEqual(document["schemaVersion"], 2)
        self.assertEqual(len(bounds), 18)
        self.assertEqual(len({bound["id"] for bound in bounds}), 18)
        self.assertTrue(all(bound["family"] and bound["kind"] for bound in bounds))
        self.assertTrue(all("formula" not in bound for bound in bounds))
        by_id = {bound["id"]: bound for bound in bounds}
        self.assertEqual([by_id[f"fi:{index}"]["constant"] for index in (8, 10, 12, 14)], [65] * 4)
        self.assertEqual({key: by_id["fi:16"][key] for key in (
            "id", "family", "kind", "constant", "coefficient", "metric", "divisor", "increment",
        )}, {
            "id": "fi:16", "family": "ssz_raw.decodeNewPayloadRequest", "kind": "affineFloor",
            "constant": 8192, "coefficient": 256, "metric": "rootSize", "divisor": 1, "increment": 0,
        })

    def test_bound_schema_rejects_wrong_id_family_or_missing_occurrence(self) -> None:
        document = inventory()
        boundaries = self.load(document)

        def rejects(mutator, message: str) -> None:
            spec = bound_spec(document)
            mutator(spec)
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bound-spec.json"
                path.write_text(json.dumps(spec))
                with self.assertRaisesRegex(ValueError, message):
                    evidence.load_bound_spec(path, boundaries)

        rejects(lambda spec: spec["bounds"][0].update(id="wrong"), "ids differ")
        rejects(lambda spec: spec["bounds"][0].update(family="ssz_raw.wrong"), "family differs")
        rejects(lambda spec: spec["bounds"].pop(), "ids differ")

    def test_rejects_unadmitted_dynamic_completion_metadata(self) -> None:
        document = inventory()
        document["boundaries"][0]["exits"] = [{"source": 0x1000, "target": 0x1004}]
        document["boundaries"][0]["calls"] = [{"sourcePc": 0x1000, "targetPc": 0x2000}]
        boundaries = self.load(document)

        def rejects(mutator, message: str) -> None:
            spec = bound_spec(document)
            mutator(spec["bounds"][0])
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bound-spec.json"
                path.write_text(json.dumps(spec))
                with self.assertRaisesRegex(ValueError, message):
                    evidence.load_bound_spec(path, boundaries)

        rejects(lambda row: row.update(dynamicCompletionTransfers=[[0x1000, 0x1004]]),
                "unsupported fields")


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

    def test_sampled_bound_rejects_a_too_small_ceiling(self) -> None:
        invocations, failures = evidence.segment_invocations(self.boundary, (8,), [4, 8])
        self.assertEqual(failures, [])
        self.assertEqual(
            evidence.validate_sampled_bound(evidence.Bound("x", "ssz_raw.x", "constant", 1), 0, invocations),
            ["invocation 0 has 2 owned instruction events, ceiling 1"],
        )

    def test_segmentation_rejects_an_unterminated_invocation(self) -> None:
        invocations, failures = evidence.segment_invocations(self.boundary, (8,), [0, 4])
        self.assertEqual(invocations, [])
        self.assertEqual(failures, ["invocation entered at event 1 was unterminated at trace end"])

    def dynamic_boundary(self) -> evidence.Boundary:
        # selected PCs 4/8/12; fi:6 owns 20/24; one ordinary frame and one source-less RA frame.
        return evidence.Boundary(
            "fi:16", "inlined", "ssz_raw.decodeNewPayloadRequest", 4, (4, 8, 12), (12,),
            "decodeRaw", None, ((8, 100),), (), (), (), (4, 8, 12), ((12, 20),), ((24, 4),),
            (evidence.ChildCall(8, 100, (100, 104)),
             evidence.ChildCall(None, 200, (200, 204), None, ((12, 200, 16),))),
        )

    def test_attribution_state_machine_accepts_exact_h_r_and_ra(self) -> None:
        boundary = self.dynamic_boundary()
        failures, observed = evidence.attribution_check(boundary, [4, 8, 100, 104, 12, 20, 24, 4, 12, 200, 204, 16], {20, 24})
        self.assertEqual(failures, [])
        self.assertEqual(observed.handoffs, ((12, 20),))
        self.assertEqual(observed.reentries, ((24, 4),))
        self.assertEqual(observed.source_less_returns, ((12, 200, 16),))

    def test_attribution_state_machine_rejects_exact_transition_and_frame_mutations(self) -> None:
        boundary = self.dynamic_boundary()
        trace = [4, 8, 100, 104, 12, 20, 24, 4, 12, 200, 204, 16]
        mutations = evidence.attribution_mutation_checks(boundary, trace, {20, 24})
        self.assertTrue(all(mutations.values()), mutations)
        self.assertEqual(set(mutations), {"skipped-handoff", "invented-handoff", "missing-reentry", "wrong-reentry", "return-deletion", "return-forgery"})

    def test_attribution_state_machine_rejects_parent_selected_and_foreign_frame_pcs(self) -> None:
        boundary = self.dynamic_boundary()
        failures, _ = evidence.attribution_check(boundary, [4, 20], {20, 24})
        self.assertIn("parent PC 0x14 in selected mode", failures[0])
        failures, _ = evidence.attribution_check(boundary, [4, 12, 20, 4], {20, 24})
        self.assertIn("selected PC 0x4 in parent mode", failures[0])
        failures, _ = evidence.attribution_check(boundary, [4, 8, 100, 24], {20, 24})
        self.assertTrue(any("foreign PC 0x18 in declared call frame" in failure for failure in failures))

    def test_attribution_state_machine_rejects_malformed_nesting_and_cross_vector_join(self) -> None:
        boundary = self.dynamic_boundary()
        nested = evidence.Boundary(
            boundary.identifier, boundary.kind, boundary.qualified, boundary.entry_pc, boundary.instruction_pcs, boundary.exits,
            boundary.parent, boundary.identity, boundary.calls, boundary.stores, boundary.tail_dependencies, boundary.cfg_edges,
            boundary.full_execution_pcs, boundary.fragment_handoffs, boundary.parent_reentry_edges,
            (evidence.ChildCall(8, 100, (8, 100, 104)),),
        )
        failures, _ = evidence.attribution_check(nested, [4, 8, 100, 8, 100], {20, 24})
        self.assertTrue(any("malformed nested call" in failure for failure in failures))
        # A fabricated cross-vector H is not supplied: each vector is checked on its own.
        first, second = [4, 12], [20, 24, 4]
        first_failures, first_observed = evidence.attribution_check(boundary, first, {20, 24})
        second_failures, second_observed = evidence.attribution_check(boundary, second, {20, 24})
        self.assertEqual(first_failures, [])
        self.assertEqual(second_failures, [])
        self.assertEqual(first_observed.handoffs + second_observed.handoffs, ())

    def test_reader_fragment_route_mutations_are_rejected(self) -> None:
        """Both an interleaved prefix and the final OR are required evidence routes."""
        trace = [0x10534, 0x10540, 0x10544, 0x10564, 0x10568, 0x105c4, 0x105c8]
        bound = evidence.Bound("fi:8", "ssz_raw.readOffset", "constant", 65,
            reader_fragment_edges=((0x10540, 0x10544), (0x10564, 0x10568), (0x105c4, 0x105c8)))
        self.assertEqual(evidence.validate_reader_fragments(bound, trace), [])
        missing_intermediate = evidence.Bound("fi:8", "ssz_raw.readOffset", "constant", 65,
            reader_fragment_edges=((0x10540, 0x10544), (0x10560, 0x10568), (0x105c4, 0x105c8)))
        missing_final = evidence.Bound("fi:8", "ssz_raw.readOffset", "constant", 65,
            reader_fragment_edges=((0x10540, 0x10544), (0x10564, 0x10568), (0x105c4, 0x105cc)))
        self.assertIn("0x10560->0x10568", evidence.validate_reader_fragments(missing_intermediate, trace)[0])
        self.assertIn("0x105c4->0x105cc", evidence.validate_reader_fragments(missing_final, trace)[0])


if __name__ == "__main__":
    unittest.main()
