#!/usr/bin/env python3
"""Unit and corruption tests for the canonical machine-region database."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location(
    "machine_regions", ROOT / "tools" / "generate_machine_regions.py"
)
assert SPEC and SPEC.loader
machine_regions = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(machine_regions)


class MachineRegionTests(unittest.TestCase):
    def level4_call_graph(self) -> dict:
        rows = [
            ("emitted", "raw_decoder_root.allocatorFree"),
            ("inlined", "ssz_raw.requireU32Length"),
            ("inlined", "ssz_raw.readOffset"),
            ("inlined", "ssz_raw.readOffset"),
            ("inlined", "ssz_raw.readOffset"),
            ("inlined", "ssz_raw.readOffset"),
            ("inlined", "ssz_raw.decodeNewPayloadRequest"),
            ("inlined", "ssz_raw.decodeExecutionWitness"),
            ("inlined", "ssz_raw.decodeChainConfig"),
            ("inlined", "ssz_raw.decodePublicKeys"),
            ("reachableCleanupNoOp", "ssz_raw.RawExecutionWitness.deinit"),
            ("reachableStdlib", "mem.Allocator.free__anon_1214"),
            ("reachableStdlib", "mem.Allocator.allocBytesWithAlignment__anon_1331"),
            ("reachableCleanupNoOp", "ssz_raw.RawNewPayloadRequest.deinit"),
            ("emitted", "ssz_raw.decodeByteListList"),
            ("emitted", "ssz_raw.requireCanonicalOffsets"),
            ("emitted", "raw_decoder_root.allocatorAlloc"),
            ("emitted", "memmove"),
        ]
        owners = [{
            "id": "decodeRaw", "kind": "emitted", "qualified": "ssz_raw.decodeRaw",
            "instructions": list(range(172)), "entryPc": 0, "regions": [{"start": 0, "size": 172}],
        }]
        read_offset_entries = (66868, 66884, 66920, 66976)
        for index, (kind, qualified) in enumerate(rows):
            owner = {
                "id": f"boundary:{index}", "kind": kind, "qualified": qualified,
                "instructions": [], "entryPc": 1000 + index * 4,
                "regions": [{"start": 1000 + index * 4, "size": 4}],
                "sourceFile": "test.zig", "specialization": [], "inlineStack": [],
            }
            if qualified == "ssz_raw.readOffset":
                offset_index = index - 2
                owner["entryPc"] = read_offset_entries[offset_index]
                owner["regions"] = [{"start": read_offset_entries[offset_index], "size": 4}]
                owner["inlineStack"] = [{
                    "callerQualified": "ssz_raw.decodeRaw", "line": 199 + offset_index,
                    "column": 23,
                }]
            owners.append(owner)
        return {
            "owners": owners,
            "dominatorParent": {f"boundary:{index}": "decodeRaw" for index in range(len(rows))},
        }

    def level4_database(self) -> dict:
        call_graph = self.level4_call_graph()
        instructions = [
            {"address": owner["entryPc"], "successors": [], "memory": []}
            for owner in call_graph["owners"][1:]
        ]
        return {
            "instructions": instructions,
            "callGraph": {
                **call_graph,
                "calls": [{
                    "caller": "boundary:0", "callee": "boundary:1", "kind": "direct",
                    "source": 1000, "evidence": 1004,
                }],
                "instructionAddresses": [row["address"] for row in instructions],
            },
        }

    def test_level4_displayed_boundaries_are_the_reviewed_inventory(self) -> None:
        call_graph = self.level4_call_graph()
        boundaries = machine_regions.level4_displayed_boundaries(call_graph, "decodeRaw")
        self.assertEqual(len(boundaries), 18)
        self.assertEqual(sum(row["qualified"] == "ssz_raw.readOffset" for row in boundaries), 4)
        machine_regions.validate_level4_displayed_boundaries(call_graph, "decodeRaw")

    def test_level4_displayed_boundary_corruption_is_rejected(self) -> None:
        call_graph = self.level4_call_graph()
        call_graph["dominatorParent"]["boundary:7"] = "somewhere-else"
        with self.assertRaisesRegex(ValueError, "Level 4 displayed boundary inventory"):
            machine_regions.validate_level4_displayed_boundaries(call_graph, "decodeRaw")

    def test_level4_boundary_manifest_carries_full_zero_self_regions(self) -> None:
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        self.assertEqual(manifest["schemaVersion"], 1)
        self.assertEqual(len(manifest["boundaries"]), 18)
        read_offsets = [
            row for row in manifest["boundaries"] if row["qualified"] == "ssz_raw.readOffset"
        ]
        self.assertEqual(len(read_offsets), 4)
        self.assertTrue(all(row["instructionPcs"] for row in read_offsets))
        self.assertTrue(all("functionInstanceIdentity" not in row
                            for row in manifest["boundaries"]
                            if row["kind"].startswith("reachable")))
        direct_call = manifest["boundaries"][0]["calls"]
        self.assertEqual(direct_call, [{
            "id": "boundary:1", "kind": "direct", "sourcePc": 1000, "targetPc": 1004,
        }])
        self.assertTrue(all("stores" not in row for row in manifest["boundaries"]))

    def test_level4_tail_dependency_has_identity_and_completion_geometry(self) -> None:
        database = self.level4_database()
        allocator = next(owner for owner in database["callGraph"]["owners"]
                         if owner["qualified"] == "raw_decoder_root.allocatorAlloc")
        raw_alloc = {
            "id": "fi:raw-alloc", "kind": "emitted", "qualified": "raw_allocator.zesu_raw_alloc",
            "instructions": [], "entryPc": 2000, "regions": [{"start": 2000, "size": 8}],
            "sourceFile": "raw_allocator.zig", "specialization": [], "inlineStack": [],
            "exitPcs": [2004],
        }
        allocator["exitPcs"] = [1064]
        database["callGraph"]["owners"].append(raw_alloc)
        database["callGraph"]["instructionAddresses"].extend([2000, 2004])
        database["instructions"].extend([
            {"address": 2000, "successors": [2004], "memory": []},
            {"address": 2004, "successors": [], "memory": []},
        ])
        database["callGraph"]["calls"].append({
            "caller": allocator["id"], "callee": raw_alloc["id"], "kind": "tail",
            "source": allocator["entryPc"], "evidence": raw_alloc["entryPc"],
        })
        manifest = machine_regions.level4_boundary_manifest(database)
        row = next(boundary for boundary in manifest["boundaries"]
                   if boundary["id"] == allocator["id"])
        [dependency] = row["tailDependencies"]
        self.assertEqual(dependency["functionInstanceIdentity"]["qualified"], raw_alloc["qualified"])
        self.assertEqual(dependency["transfer"], {"sourcePc": allocator["entryPc"], "targetPc": 2000})
        self.assertEqual(dependency["completionSourcePcs"], [2004])
        self.assertEqual(dependency["calleeInstructionPcs"], [2000, 2004])
        self.assertEqual(dependency["combinedInstructionPcs"], sorted(row["instructionPcs"] + [2000, 2004]))

    def test_level4_boundary_manifest_has_consumer_compatible_shape(self) -> None:
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        for row in manifest["boundaries"]:
            identity = row.get("functionInstanceIdentity")
            if identity is not None:
                # The evidence loader currently stores an identity string; its adapter can use this
                # stable structured source identity without treating excluded rows as functions.
                self.assertIsInstance(identity, dict)
                self.assertIsInstance(identity["sourceFile"], str)
                self.assertIsInstance(identity["qualified"], str)
            for call in row.get("calls", []):
                self.assertIsInstance(call["sourcePc"], int)
                self.assertIsInstance(call["targetPc"], int)
                self.assertNotIn("source", call)
                self.assertNotIn("target", call)
            self.assertNotIn("stores", row)

    def test_level4_boundary_manifest_corruption_is_rejected(self) -> None:
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        manifest["boundaries"][0]["instructionPcs"] = []
        with self.assertRaisesRegex(ValueError, "empty or unsorted instruction PCs"):
            machine_regions.validate_level4_boundary_manifest(manifest)
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        manifest["boundaries"][0]["exits"] = None
        with self.assertRaisesRegex(ValueError, "invalid required field"):
            machine_regions.validate_level4_boundary_manifest(manifest)
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        manifest["boundaries"][0]["calls"][0]["targetPc"] = None
        with self.assertRaisesRegex(ValueError, "call lacks concrete PCs"):
            machine_regions.validate_level4_boundary_manifest(manifest)
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        manifest["boundaries"][0]["stores"] = [{"pc": 1000, "bytes": 8}]
        with self.assertRaisesRegex(ValueError, "cannot claim dynamic stores"):
            machine_regions.validate_level4_boundary_manifest(manifest)
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        manifest["boundaries"][0]["tailDependencies"] = [{"functionInstanceId": "fi:0"}]
        with self.assertRaisesRegex(ValueError, "tail dependency lacks"):
            machine_regions.validate_level4_boundary_manifest(manifest)
        database = self.level4_database()
        allocator = next(owner for owner in database["callGraph"]["owners"]
                         if owner["qualified"] == "raw_decoder_root.allocatorAlloc")
        raw_alloc = {
            "id": "fi:raw-alloc", "kind": "emitted", "qualified": "raw_allocator.zesu_raw_alloc",
            "instructions": [], "entryPc": 2000, "regions": [{"start": 2000, "size": 8}],
            "sourceFile": "raw_allocator.zig", "specialization": [], "inlineStack": [], "exitPcs": [2004],
        }
        database["callGraph"]["owners"].append(raw_alloc)
        database["callGraph"]["instructionAddresses"].extend([2000, 2004])
        database["instructions"].extend([
            {"address": 2000, "successors": [2004], "memory": []},
            {"address": 2004, "successors": [], "memory": []},
        ])
        database["callGraph"]["calls"].append({"caller": allocator["id"], "callee": raw_alloc["id"],
            "kind": "tail", "source": allocator["entryPc"], "evidence": 2000})
        manifest = machine_regions.level4_boundary_manifest(database)
        dependency = next(row for row in manifest["boundaries"] if row["id"] == allocator["id"])["tailDependencies"][0]
        dependency["combinedInstructionPcs"].pop()
        with self.assertRaisesRegex(ValueError, "combined region is not exact"):
            machine_regions.validate_level4_boundary_manifest(manifest)
        manifest = machine_regions.level4_boundary_manifest(self.level4_database())
        manifest["boundaries"][0]["fullExecutionPcs"] = [1000]
        manifest["boundaries"][0]["fragmentHandoffs"] = [{"sourcePc": 1000, "targetPc": 1000}]
        with self.assertRaisesRegex(ValueError, "lacks owned execution PCs"):
            machine_regions.validate_level4_boundary_manifest(manifest)

    def test_dynamic_attribution_handoffs_use_decoded_deepest_ownership(self) -> None:
        parent = {
            "id": "fi:6", "kind": "emitted", "qualified": "ssz_raw.decodeRaw",
            "entryPc": 74000, "regions": [{"start": 74000, "size": 4000}], "parent": None,
        }
        decoder = {
            "id": "fi:102", "kind": "inlined", "qualified": "ssz_raw.decodeChainConfig",
            "entryPc": 76108, "regions": [{"start": 77400, "size": 12}], "parent": "fi:6",
            "inlineStack": [{"callerQualified": "ssz_raw.decodeRaw", "line": 211, "column": 48}],
        }
        nested = {
            "id": "fi:103", "kind": "inlined", "qualified": "nested", "entryPc": 77416,
            "regions": [{"start": 77416, "size": 4}], "parent": "fi:102",
        }
        sibling = {"id": "fi:104", "kind": "inlined", "qualified": "sibling", "entryPc": 77424,
                   "regions": [{"start": 77424, "size": 4}], "parent": "fi:6"}
        owners = {row["id"]: row for row in (parent, decoder, nested, sibling)}
        instructions = {
            77408: {"address": 77408, "owner": "fi:102", "successors": [77412]},
            77412: {"address": 77412, "owner": "fi:6", "successors": []},
            77396: {"address": 77396, "owner": "fi:6", "successors": [77408]},
            77416: {"address": 77416, "owner": "fi:103", "successors": [77412]},
            77392: {"address": 77392, "owner": "fi:6", "successors": [77416, 77424]},
        }
        self.assertEqual(machine_regions.dynamic_full_execution_pcs(decoder, owners), [77400, 77404, 77408, 77416])
        self.assertEqual(machine_regions.dynamic_owned_execution_pcs(decoder, instructions),
                         [77408])
        # A corruption that replaces the selected subtree by its direct-owner PCs would lose this
        # real nested handoff.  Keep it distinct from direct ownership: the emitted Lean evidence
        # must name `fi:103` for 77416 rather than assert that `fi:102` owns it directly.
        self.assertNotIn(77416, machine_regions.dynamic_owned_execution_pcs(decoder, instructions))
        self.assertEqual(machine_regions.attribution_fragment_handoffs(decoder, parent, owners, instructions),
                         [{"sourcePc": 77408, "targetPc": 77412}, {"sourcePc": 77416, "targetPc": 77412}])
        self.assertEqual(machine_regions.parent_fragment_reentries(decoder, parent, owners, instructions),
                         [{"sourcePc": 77392, "targetPc": 77416}, {"sourcePc": 77396, "targetPc": 77408}])

    def test_dynamic_attribution_ignores_non_parent_and_nested_edges(self) -> None:
        parent = {"id": "fi:6", "regions": [{"start": 77412, "size": 4}], "parent": None}
        decoder = {"id": "fi:102", "qualified": "ssz_raw.decodeChainConfig", "entryPc": 76108,
                   "regions": [{"start": 77408, "size": 4}], "parent": "fi:6", "inlineStack": [{"callerQualified": "ssz_raw.decodeRaw", "line": 211, "column": 48}]}
        owners = {"fi:6": parent, "fi:102": decoder}
        self.assertEqual(machine_regions.attribution_fragment_handoffs(decoder, parent, owners,
            {77408: {"address": 77408, "owner": "fi:102", "successors": [77416]}}), [])
        self.assertEqual(machine_regions.attribution_fragment_handoffs(decoder,
            {**parent, "regions": [{"start": 80000, "size": 4}]}, owners,
            {77408: {"address": 77408, "owner": "fi:102", "successors": [77412]}}), [])

    def test_admissible_route_predecessors_stop_at_other_handoffs_and_framed_calls(self) -> None:
        parent = {"id": "fi:6", "regions": [{"start": 96, "size": 32}], "parent": None}
        decoder = {
            "id": "fi:102", "qualified": "ssz_raw.decodeChainConfig", "entryPc": 100,
            "regions": [{"start": 100, "size": 20}], "parent": "fi:6",
            "inlineStack": [{"callerQualified": "ssz_raw.decodeRaw", "line": 211, "column": 48}],
        }
        owners = {"fi:6": parent, "fi:102": decoder}
        instructions = {
            96: {"address": 96, "owner": "fi:6", "successors": [112]},
            100: {"address": 100, "owner": "fi:102", "successors": [104]},
            104: {"address": 104, "owner": "fi:102", "transfer": "directCall",
                  "successors": [108, 1000]},
            108: {"address": 108, "owner": "fi:102", "successors": [112, 200]},
            112: {"address": 112, "owner": "fi:102", "successors": [116]},
            116: {"address": 116, "owner": "fi:102", "successors": [120]},
            120: {"address": 120, "owner": "fi:6", "successors": []},
            200: {"address": 200, "owner": "fi:6", "successors": []},
        }
        handoffs = machine_regions.attribution_fragment_handoffs(decoder, parent, owners, instructions)
        reentries = machine_regions.parent_fragment_reentries(decoder, parent, owners, instructions)
        self.assertEqual(handoffs, [{"sourcePc": 108, "targetPc": 200},
                                    {"sourcePc": 116, "targetPc": 120}])
        self.assertEqual(reentries, [{"sourcePc": 96, "targetPc": 112}])
        frame = {"targetPc": 1000, "activeCalleeExecutionPcs": [1000],
                 "returnSites": [{"sourcePc": 104, "returnPc": 108}],
                 "activeCalleeFrames": []}
        self.assertEqual(
            machine_regions.admissible_route_predecessors(
                decoder, handoffs[0], reentries, instructions, owners, [], handoffs),
            [],
        )
        self.assertEqual(
            machine_regions.admissible_route_predecessors(
                decoder, handoffs[0], reentries, instructions, owners, [frame], handoffs),
            [100],
        )
        # The initial stage reaches the first H source, but route two must stop there.  Only the
        # generated re-entry stage at 112 can precede its H source.
        self.assertEqual(
            machine_regions.admissible_route_predecessors(
                decoder, handoffs[1], reentries, instructions, owners, [frame], handoffs),
            [112],
        )

    def test_outcome_carrier_instruction_validator_rejects_deletion_and_forgery(self) -> None:
        route = {
            "classification": "sourceReviewedOutcomePath",
            "handoff": {"sourcePc": 0x12e60, "targetPc": 0x12e64},
            "carrierPcs": [0x12e64],
            "carrierPaths": [{"carrierPc": 0x12e64, "pcs": [0x12e64], "ownerIds": ["fi:6"]}],
            "registers": [{"pc": 0x12e64, "register": "a4", "role": "word-0"}],
            "stackDescriptors": [{"pc": 0x12e64, "instructionKind": "store", "register": "a4",
                                  "baseRegister": "sp", "offset": 0x5c0, "role": "word-0-store"}],
            "statusTag": {"state": "unmeasured"},
            "heapArrayRep": {"state": "not-applicable"},
        }
        instructions = {
            0x12e64: {"address": 0x12e64, "mnemonic": "sd", "operands": "a4, 0x5c0(sp)",
                      "owner": "fi:6", "reads": ["a4", "sp"], "writes": [],
                      "liveIn": ["a4", "sp"], "liveOut": []},
        }
        machine_regions.validate_outcome_carrier_instructions([route], "fi:6", instructions)
        with self.assertRaisesRegex(ValueError, "carrier PC is absent"):
            machine_regions.validate_outcome_carrier_instructions([route], "fi:6", {})
        forged = copy.deepcopy(route)
        forged["stackDescriptors"][0]["offset"] = 0x5c8
        with self.assertRaisesRegex(ValueError, "stack descriptor"):
            machine_regions.validate_outcome_carrier_instructions([forged], "fi:6", instructions)

    def test_outcome_carrier_successor_entry_rejects_nonentry_mutation(self) -> None:
        route = {
            "classification": "sourceReviewedOutcomePath",
            "handoff": {"sourcePc": 12, "targetPc": 16},
            "carrierPcs": [20],
            "carrierPaths": [{"carrierPc": 20, "pcs": [16, 20], "ownerIds": ["fi:6", "fi:102"]}],
            "registers": [], "stackDescriptors": [], "statusTag": {"state": "not-applicable"},
            "heapArrayRep": {"state": "not-applicable"},
        }
        instructions = {
            16: {"address": 16, "mnemonic": "addi", "operands": "a0, a0, 0",
                 "owner": "fi:6", "reads": ["a0"], "writes": ["a0"], "liveIn": [], "liveOut": [],
                 "successors": [20]},
            20: {"address": 20, "mnemonic": "addi", "operands": "a0, a0, 0",
                 "owner": "fi:102", "reads": ["a0"], "writes": ["a0"], "liveIn": [], "liveOut": [],
                 "successors": []},
        }
        owners = {"fi:102": {"id": "fi:102", "parent": "fi:6", "entryPc": 20}}
        machine_regions.validate_outcome_carrier_instructions(
            [route], "fi:6", instructions, {"fi:6"}, owners)
        owners["fi:102"]["entryPc"] = 24
        with self.assertRaisesRegex(ValueError, "carrier PC is absent"):
            machine_regions.validate_outcome_carrier_instructions(
                [route], "fi:6", instructions, {"fi:6"}, owners)

    def test_dynamic_attribution_validator_rejects_deletion_and_forgery(self) -> None:
        parent = {"id": "fi:6", "regions": [{"start": 77412, "size": 20}], "parent": None}
        decoder = {"id": "fi:102", "qualified": "ssz_raw.decodeChainConfig", "entryPc": 76108,
                   "regions": [{"start": 77404, "size": 8}], "parent": "fi:6",
                   "sourceFile": "src/stateless/stateless/ssz_raw.zig", "declLine": 349,
                   "specialization": [],
                   "inlineStack": [{"callerQualified": "ssz_raw.decodeRaw", "line": 211, "column": 48}]}
        database = {"instructions": [
            {"address": 77404, "owner": "fi:102", "successors": [77408]},
            {"address": 77408, "owner": "fi:102", "successors": [77412]},
            {"address": 77412, "owner": "fi:6", "successors": [77416], "mnemonic": "sd",
             "operands": "a4, 0x5c0(sp)", "reads": ["a4", "sp"], "writes": [],
             "liveIn": ["a4", "sp"], "liveOut": []},
            {"address": 77416, "owner": "fi:6", "successors": [77420], "mnemonic": "sd",
             "operands": "a5, 0x5c8(sp)", "reads": ["a5", "sp"], "writes": [],
             "liveIn": ["a5", "sp"], "liveOut": []},
            {"address": 77420, "owner": "fi:6", "successors": [77424], "mnemonic": "sd",
             "operands": "a6, 0x5d0(sp)", "reads": ["a6", "sp"], "writes": [],
             "liveIn": ["a6", "sp"], "liveOut": []},
            {"address": 77424, "owner": "fi:6", "successors": [], "mnemonic": "sd",
             "operands": "a7, 0x5d8(sp)", "reads": ["a7", "sp"], "writes": [],
             "liveIn": ["a7", "sp"], "liveOut": []},
            {"address": 77400, "owner": "fi:6", "successors": [77404]},
        ], "callGraph": {"owners": [parent, decoder]}}
        manifest = {"parent": {"id": "fi:6"}, "boundaries": [{
            "id": "fi:102", "instructionPcs": [77404, 77408], "ownedExecutionPcs": [77404, 77408],
            "subtreeOwnedExecutionPcs": [77404, 77408], "fullExecutionPcs": [77404, 77408],
            "parentReentryEdges": [{"sourcePc": 77400, "targetPc": 77404}],
            "fragmentHandoffs": [{"sourcePc": 77408, "targetPc": 77412}],
        }]}
        manifest["boundaries"][0]["carrierRoutes"] = machine_regions.outcome_carrier_routes(
            decoder, parent, {row["address"]: row for row in database["instructions"]}
        )
        machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["carrierRoutes"] = []
        with self.assertRaisesRegex(ValueError, "carrier routes are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["carrierRoutes"] = machine_regions.outcome_carrier_routes(
            decoder, parent, {row["address"]: row for row in database["instructions"]}
        )
        manifest["boundaries"][0]["carrierRoutes"][0]["classification"] = "unclassified"
        with self.assertRaisesRegex(ValueError, "carrier routes are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["carrierRoutes"] = machine_regions.outcome_carrier_routes(
            decoder, parent, {row["address"]: row for row in database["instructions"]}
        )
        manifest["boundaries"][0]["carrierRoutes"][0]["admissiblePredecessors"] = []
        with self.assertRaisesRegex(ValueError, "carrier routes are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["carrierRoutes"] = machine_regions.outcome_carrier_routes(
            decoder, parent, {row["address"]: row for row in database["instructions"]}
        )
        manifest["boundaries"][0]["carrierRoutes"][0]["admissiblePredecessors"] = [77408]
        with self.assertRaisesRegex(ValueError, "carrier routes are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["carrierRoutes"] = machine_regions.outcome_carrier_routes(
            decoder, parent, {row["address"]: row for row in database["instructions"]}
        )
        manifest["boundaries"][0]["fragmentHandoffs"] = []
        with self.assertRaisesRegex(ValueError, "handoffs are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["fragmentHandoffs"] = [{"sourcePc": 77404, "targetPc": 77412}]
        with self.assertRaisesRegex(ValueError, "handoffs are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["fragmentHandoffs"] = [{"sourcePc": 77408, "targetPc": 77412}]
        manifest["boundaries"][0]["fullExecutionPcs"] = [77408]
        with self.assertRaisesRegex(ValueError, "full execution PCs are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["fullExecutionPcs"] = [77404, 99999]
        with self.assertRaisesRegex(ValueError, "full execution PCs are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["fullExecutionPcs"] = [77404, 77408]
        manifest["boundaries"][0]["ownedExecutionPcs"] = [77408]
        with self.assertRaisesRegex(ValueError, "owned execution PCs are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["ownedExecutionPcs"] = [77404, 99999]
        with self.assertRaisesRegex(ValueError, "owned execution PCs are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["ownedExecutionPcs"] = [77404, 77408]
        manifest["boundaries"][0]["subtreeOwnedExecutionPcs"] = [77404]
        with self.assertRaisesRegex(ValueError, "subtree-owned execution PCs are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["subtreeOwnedExecutionPcs"] = [77404, 77408]
        manifest["boundaries"][0]["parentReentryEdges"] = []
        with self.assertRaisesRegex(ValueError, "re-entries are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)

    def test_dynamic_call_target_extent_validator_rejects_deletion_and_forgery(self) -> None:
        parent = {"id": "fi:6", "kind": "emitted", "qualified": "ssz_raw.decodeRaw",
                  "entryPc": 77400, "regions": [{"start": 77400, "size": 32}], "parent": None}
        decoder = {"id": "fi:102", "kind": "inlined", "qualified": "ssz_raw.decodeChainConfig",
                   "entryPc": 77404, "regions": [{"start": 77404, "size": 8}], "parent": "fi:6",
                   "sourceFile": "ssz_raw.zig", "specialization": [],
                   "inlineStack": [{"callerQualified": "ssz_raw.decodeRaw", "line": 211, "column": 48}]}
        callee = {"id": "fi:134", "kind": "emitted", "qualified": "ssz_raw.requireCanonicalOffsets",
                  "entryPc": 78000, "regions": [{"start": 78000, "size": 8}], "parent": None,
                  "sourceFile": "ssz_raw.zig", "specialization": [], "inlineStack": []}
        excluded = {"id": "excluded:9", "kind": "reachableStdlib", "qualified": "allocator.free",
                    "entryPc": 79000, "regions": [{"start": 79000, "size": 8}], "parent": None,
                    "sourceFile": "<zig-std>"}
        foreign = {"id": "fi:0", "kind": "emitted", "qualified": "raw_allocator.zesu_raw_alloc",
                   "entryPc": 66124, "regions": [{"start": 66124, "size": 4}], "parent": None,
                   "sourceFile": "raw_allocator.zig", "specialization": [], "inlineStack": []}
        database = {"instructions": [
            {"address": 77404, "owner": "fi:102", "successors": [77408, 78000],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 77408, "owner": "fi:102", "successors": [77412, 79000],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 77412, "owner": "fi:6", "successors": []},
            {"address": 77400, "owner": "fi:6", "successors": [77404]},
            {"address": 78000, "owner": "fi:134", "successors": [78004]},
            {"address": 78004, "owner": "fi:134", "successors": []},
            {"address": 79000, "owner": "excluded:9", "successors": [79004]},
            {"address": 79004, "owner": "excluded:9", "successors": []},
            {"address": 66124, "owner": "fi:0", "successors": []},
        ], "callGraph": {"owners": [parent, decoder, callee, excluded, foreign], "calls": []}}
        owners = {owner["id"]: owner for owner in database["callGraph"]["owners"]}
        instructions = {row["address"]: row for row in database["instructions"]}
        active_calls = machine_regions.active_extent_calls(decoder, database["callGraph"], owners, instructions)
        call = machine_regions.active_callee_frame(
            decoder, next(item for item in active_calls if item["id"] == "fi:134"),
            database["callGraph"], owners, instructions, frozenset({"fi:102"}),
        )
        excluded_call = machine_regions.active_callee_frame(
            decoder, next(item for item in active_calls if item["id"] == "excluded:9"),
            database["callGraph"], owners, instructions, frozenset({"fi:102"}),
        )
        manifest = {"parent": {"id": "fi:6"}, "boundaries": [{
            "id": "fi:102", "instructionPcs": [77404, 77408], "ownedExecutionPcs": [77404, 77408],
            "subtreeOwnedExecutionPcs": [77404, 77408], "fullExecutionPcs": [77404, 77408], "calls": [call, excluded_call],
            "parentReentryEdges": [{"sourcePc": 77400, "targetPc": 77404}],
            "fragmentHandoffs": [{"sourcePc": 77408, "targetPc": 77412}],
        }]}
        machine_regions.validate_level4_attribution_boundaries(database, manifest)
        self.assertEqual(
            [(call["sourcePc"], call["targetPc"], call["id"]) for call in active_calls],
            [(77404, 78000, "fi:134"), (77408, 79000, "excluded:9")],
        )
        duplicate = copy.deepcopy(manifest["boundaries"][0]["calls"][0])
        duplicate["sourcePc"] = None
        manifest["boundaries"][0]["calls"].append(duplicate)
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"].pop()
        manifest["boundaries"][0]["calls"][1].pop("returnSites")
        with self.assertRaisesRegex(ValueError, "lacks per-site RA obligations"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["returnSites"] = [{
            "sourcePc": 77408, "targetPc": 79000, "returnPc": 99999, "linkRegister": "ra",
        }]
        with self.assertRaisesRegex(ValueError, "invalid RA obligation"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["returnSites"] = [{
            "sourcePc": 77408, "targetPc": 79000, "returnPc": 77412, "linkRegister": "ra",
        }]
        database["instructions"][1]["transfer"] = "ordinary"
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        database["instructions"][1]["transfer"] = "directCall"
        database["instructions"][1]["mnemonic"] = "jal"
        with self.assertRaisesRegex(ValueError, "direct jalr call"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        database["instructions"][1]["mnemonic"] = "jalr"
        database["instructions"][1]["word"] = 0x00008067  # rd = x0, rs1 = x1
        with self.assertRaisesRegex(ValueError, "jalr x1, x1"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        database["instructions"][1]["word"] = 0x000000e7  # rd = x1, rs1 = x0
        with self.assertRaisesRegex(ValueError, "jalr x1, x1"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        database["instructions"][1]["word"] = 0x000080e7
        database["instructions"][1]["successors"] = [79000]
        with self.assertRaisesRegex(ValueError, "RA fall-through"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        database["instructions"][1]["successors"] = [77412, 79000]
        manifest["boundaries"][0]["calls"][0].pop("activeCalleeExecutionPcs")
        with self.assertRaisesRegex(ValueError, "invalid exact execution extent"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][0]["activeCalleeExecutionPcs"] = [78000, 99999]
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][0]["activeCalleeExecutionPcs"] = [78000, 78004]
        manifest["boundaries"][0]["calls"][1].pop("activeCalleeExecutionPcs")
        with self.assertRaisesRegex(ValueError, "invalid exact execution extent"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["activeCalleeExecutionPcs"] = [79000, 99999]
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["activeCalleeExecutionPcs"] = [79000, 79004]
        manifest["boundaries"][0]["calls"][0]["activeCalleeExecutionPcs"] = [78000, 78004, 66124]
        with self.assertRaisesRegex(ValueError, "invalid exact execution extent"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][0]["activeCalleeExecutionPcs"] = [78000, 78004]
        manifest["boundaries"][0]["parentReentryEdges"] = [{"sourcePc": 77400, "targetPc": 77408}]
        with self.assertRaisesRegex(ValueError, "re-entries are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)

    def test_recursive_active_callee_frames_reject_nested_ra_cycle_and_sibling_forgery(self) -> None:
        def owner(identifier: str, kind: str, qualified: str, entry: int, parent: str | None = None) -> dict:
            return {
                "id": identifier, "kind": kind, "qualified": qualified, "entryPc": entry,
                "regions": [{"start": entry, "size": 8}], "parent": parent,
                "sourceFile": "test.zig", "specialization": [], "inlineStack": [],
            }

        parent = owner("fi:6", "emitted", "ssz_raw.decodeRaw", 96)
        decoder = owner("fi:102", "inlined", "ssz_raw.decodeChainConfig", 100, "fi:6")
        decoder["inlineStack"] = [{"callerQualified": "ssz_raw.decodeRaw", "line": 211, "column": 48}]
        callee = owner("fi:134", "emitted", "ssz_raw.requireCanonicalOffsets", 200)
        nested = owner("fi:135", "emitted", "nested", 300)
        foreign = owner("fi:136", "emitted", "foreign", 400)
        owners = [parent, decoder, callee, nested, foreign]
        instructions = [
            {"address": 96, "owner": "fi:6", "successors": [100]},
            {"address": 100, "owner": "fi:102", "successors": [104, 200],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 104, "owner": "fi:6", "successors": []},
            {"address": 200, "owner": "fi:134", "successors": [204, 300],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 204, "owner": "fi:134", "successors": []},
            {"address": 300, "owner": "fi:135", "successors": [304, 200],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 304, "owner": "fi:135", "successors": []},
            {"address": 400, "owner": "fi:136", "successors": [404]},
            {"address": 404, "owner": "fi:136", "successors": []},
        ]
        call_graph = {"owners": owners, "calls": [
            {"caller": "fi:102", "callee": "fi:134", "kind": "direct", "source": 100},
            {"caller": "fi:134", "callee": "fi:135", "kind": "direct", "source": 200},
            {"caller": "fi:135", "callee": "fi:134", "kind": "direct", "source": 300},
        ]}
        database = {"instructions": instructions, "callGraph": call_graph}
        by_id = {item["id"]: item for item in owners}
        by_pc = {item["address"]: item for item in instructions}
        root_call = machine_regions.active_extent_calls(decoder, call_graph, by_id, by_pc)[0]
        frame = machine_regions.active_callee_frame(
            decoder, root_call, call_graph, by_id, by_pc, frozenset({"fi:102"})
        )
        self.assertEqual(machine_regions.active_callee_frame_count([frame]), 3)
        self.assertIsNone(frame["cycleBackEdge"])
        cycle = frame["activeCalleeFrames"][0]["activeCalleeFrames"][0]["cycleBackEdge"]
        self.assertEqual(cycle["ancestorId"], "fi:134")
        self.assertEqual(cycle["transitions"], [{"sourcePc": 300, "targetPc": 200}])
        manifest = {"parent": {"id": "fi:6"}, "boundaries": [{
            "id": "fi:102", "instructionPcs": [100, 104], "ownedExecutionPcs": [100],
            "subtreeOwnedExecutionPcs": [100], "fullExecutionPcs": [100, 104],
            "calls": [frame], "parentReentryEdges": [{"sourcePc": 96, "targetPc": 100}],
            "fragmentHandoffs": [{"sourcePc": 100, "targetPc": 104}],
        }]}
        machine_regions.validate_level4_attribution_boundaries(database, manifest)

        deletion = copy.deepcopy(manifest)
        deletion["boundaries"][0]["calls"][0]["activeCalleeFrames"] = []
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, deletion)

        bad_ra = copy.deepcopy(manifest)
        bad_ra["boundaries"][0]["calls"][0]["returnSites"][0]["returnPc"] = 108
        with self.assertRaisesRegex(ValueError, "invalid RA obligation"):
            machine_regions.validate_level4_attribution_boundaries(database, bad_ra)

        forged_cycle = copy.deepcopy(manifest)
        forged_cycle["boundaries"][0]["calls"][0]["cycleBackEdge"] = copy.deepcopy(cycle)
        forged_cycle["boundaries"][0]["calls"][0]["activeCalleeFrames"] = []
        with self.assertRaisesRegex(ValueError, "forged ancestor cycle back-edge"):
            machine_regions.validate_level4_attribution_boundaries(database, forged_cycle)

        missing_cycle_transition = copy.deepcopy(manifest)
        missing_cycle_transition["boundaries"][0]["calls"][0]["activeCalleeFrames"][0]["activeCalleeFrames"][0]["cycleBackEdge"]["transitions"] = []
        with self.assertRaisesRegex(ValueError, "incomplete cycle back-edge transitions"):
            machine_regions.validate_level4_attribution_boundaries(database, missing_cycle_transition)

        foreign_sibling = copy.deepcopy(manifest)
        forged_foreign = copy.deepcopy(foreign_sibling["boundaries"][0]["calls"][0]["activeCalleeFrames"][0])
        forged_foreign.update({
            "id": "fi:136", "targetPc": 400,
            "targetIdentity": machine_regions.generated_target_identity(foreign),
            "activeCalleeExecutionPcs": [400, 404],
            "returnSites": [{"sourcePc": 200, "targetPc": 400, "returnPc": 204,
                             "linkRegister": "ra"}],
            "activeCalleeFrames": [], "cycleBackEdge": None,
        })
        foreign_sibling["boundaries"][0]["calls"][0]["activeCalleeFrames"].append(forged_foreign)
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, foreign_sibling)

    def test_active_extent_calls_include_fi45_allocator_and_memmove_calls(self) -> None:
        def owner(identifier: str, kind: str, qualified: str, entry: int, parent: str | None,
                  size: int = 4) -> dict:
            return {
                "id": identifier, "kind": kind, "qualified": qualified, "entryPc": entry,
                "regions": [{"start": entry, "size": size}], "parent": parent,
                "sourceFile": "test.zig", "specialization": [], "inlineStack": [],
            }

        parent = owner("fi:6", "emitted", "ssz_raw.decodeRaw", 0x11004, None)
        decoder = owner("fi:16", "inlined", "ssz_raw.decodeNewPayloadRequest", 0x11000, "fi:6")
        decoder["inlineStack"] = [{"callerQualified": "ssz_raw.decodeRaw", "line": 207, "column": 61}]
        inline_parent = owner("fi:23", "inlined", "ssz_raw.decodeExecutionPayload", 0x11200, "fi:16")
        fi45 = owner("fi:45", "inlined", "ssz_raw.decodeWithdrawals", 0x115e8, "fi:23", 16)
        excluded7 = owner("excluded:7", "reachableStdlib", "allocator.alloc", 0x13600, None, 4)
        fi140 = owner("fi:140", "emitted", "memmove", 0x13edc, None, 4)
        owners = [parent, decoder, inline_parent, fi45, excluded7, fi140]
        instructions = [
            {"address": 0x10ffc, "owner": "fi:6", "successors": [0x11000]},
            {"address": 0x11000, "owner": "fi:16", "successors": [0x11004]},
            {"address": 0x11004, "owner": "fi:6", "successors": []},
            {"address": 0x11200, "owner": "fi:23", "successors": []},
            {"address": 0x115e8, "owner": "fi:45", "successors": [0x115ec, 0x13600],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 0x115ec, "owner": "fi:45", "successors": []},
            {"address": 0x115f0, "owner": "fi:45", "successors": [0x115f4, 0x13edc],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 0x115f4, "owner": "fi:45", "successors": []},
            {"address": 0x13600, "owner": "excluded:7", "successors": []},
            {"address": 0x13edc, "owner": "fi:140", "successors": []},
        ]
        call_graph = {"owners": owners, "calls": []}
        database = {"instructions": instructions, "callGraph": call_graph}
        by_id = {item["id"]: item for item in owners}
        by_pc = {item["address"]: item for item in instructions}
        calls = machine_regions.active_extent_calls(decoder, call_graph, by_id, by_pc)
        self.assertEqual(
            [(call["callerId"], call["sourcePc"], call["targetPc"]) for call in calls],
            [("fi:45", 0x115e8, 0x13600), ("fi:45", 0x115f0, 0x13edc)],
        )
        frames = [machine_regions.active_callee_frame(
            decoder, call, call_graph, by_id, by_pc, frozenset({"fi:16"})
        ) for call in calls]
        self.assertTrue(all(frame["callerIdentity"]["qualified"] == "ssz_raw.decodeWithdrawals"
                            for frame in frames))
        manifest = {"parent": {"id": "fi:6"}, "boundaries": [{
            "id": "fi:16", "instructionPcs": [0x11000], "ownedExecutionPcs": [0x11000],
            "subtreeOwnedExecutionPcs": [0x11000, 0x11200, 0x115e8, 0x115ec, 0x115f0, 0x115f4],
            "fullExecutionPcs": [0x11000, 0x11200, 0x115e8, 0x115ec, 0x115f0, 0x115f4],
            "calls": frames, "parentReentryEdges": [{"sourcePc": 0x10ffc, "targetPc": 0x11000}],
            "fragmentHandoffs": [{"sourcePc": 0x11000, "targetPc": 0x11004}],
        }]}
        machine_regions.validate_level4_attribution_boundaries(database, manifest)
        omitted_memmove = copy.deepcopy(manifest)
        omitted_memmove["boundaries"][0]["calls"] = omitted_memmove["boundaries"][0]["calls"][:1]
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, omitted_memmove)

    def test_decoded_excluded_body_calls_ignore_missing_call_graph_declarations(self) -> None:
        def owner(identifier: str, qualified: str, entry: int, size: int) -> dict:
            return {
                "id": identifier, "kind": "reachableStdlib", "qualified": qualified,
                "entryPc": entry, "regions": [{"start": entry, "size": size}], "parent": None,
                "sourceFile": "test.zig", "specialization": [], "inlineStack": [],
            }

        excluded5 = owner("excluded:5", "mem.Allocator.alloc__anon_1475", 0x13518, 0x58)
        cleanup = owner("excluded:10", "ssz_raw.RawExecutionPayload.deinit", 0x13698, 0x50)
        excluded1 = owner("excluded:1", "mem.Allocator.free__anon_1214", 0x130ac, 4)
        excluded7 = owner("excluded:7", "mem.Allocator.allocBytesWithAlignment__anon_1511", 0x13600, 4)
        excluded11 = owner("excluded:11", "mem.Allocator.free__anon_1555", 0x136f8, 4)
        owners = [excluded1, excluded5, excluded7, cleanup, excluded11]
        instructions = {
            0x1356c: {"address": 0x1356c, "owner": "excluded:5",
                      "successors": [0x13570, 0x13600], "transfer": "directCall",
                      "mnemonic": "jalr", "word": 0x000080e7},
            0x136d0: {"address": 0x136d0, "owner": "excluded:10",
                      "successors": [0x136d4, 0x130ac], "transfer": "directCall",
                      "mnemonic": "jalr", "word": 0x000080e7},
            0x136e4: {"address": 0x136e4, "owner": "excluded:10",
                      "successors": [0x136e8, 0x136f8], "transfer": "directCall",
                      "mnemonic": "jalr", "word": 0x000080e7},
        }
        graph = {"owners": owners, "calls": []}
        by_id = {item["id"]: item for item in owners}
        self.assertEqual(
            [(call["sourcePc"], call["targetPc"], call["id"])
             for call in machine_regions.active_extent_calls(excluded5, graph, by_id, instructions)],
            [(0x1356c, 0x13600, "excluded:7")],
        )
        self.assertEqual(
            [(call["sourcePc"], call["targetPc"], call["id"])
             for call in machine_regions.active_extent_calls(cleanup, graph, by_id, instructions)],
            [(0x136d0, 0x130ac, "excluded:1"), (0x136e4, 0x136f8, "excluded:11")],
        )

    def test_llvm_disassembly_parser(self) -> None:
        parsed = machine_regions.parse_disassembly(
            """
00000000000102b0 <zesu_decode_raw>:
   102b0: 81010113      addi sp, sp, -0x7f0
   102b4: 7e113423      sd ra, 0x7e8(sp)
   102b8: 02050063      beqz a0, 0x102d8 <zesu_decode_raw+0x28>
"""
        )
        self.assertEqual(parsed[0x102B0]["word"], 0x81010113)
        self.assertEqual(parsed[0x102B8]["mnemonic"], "beqz")

    def test_register_effects(self) -> None:
        load = {"mnemonic": "ld", "operands": "a0, 0x8(sp)"}
        reads, writes, memory, known = machine_regions.register_effects(load)
        self.assertEqual(reads, {"sp"})
        self.assertEqual(writes, {"a0"})
        self.assertEqual(memory, [{"kind": "read", "bytes": 8}])
        self.assertTrue(known)

    def test_resolves_auipc_jalr_from_words(self) -> None:
        instructions = {
            0x1000: {"mnemonic": "auipc", "word": 0x00000097},
            0x1004: {"mnemonic": "jalr", "word": 0x100080E7},
        }
        self.assertEqual(
            machine_regions.resolved_auipc_jalr_target(0x1004, instructions[0x1004], instructions),
            0x1100,
        )

    def test_tarjan_finds_loop(self) -> None:
        graph = {0: {1}, 1: {2}, 2: {1, 3}, 3: set()}
        self.assertIn([1, 2], machine_regions.strongly_connected_components(graph))

    def test_condensation_ranks_increase_across_edges(self) -> None:
        graph = {0: {1}, 1: {2}, 2: set()}
        ranks = machine_regions.condensation_ranks(graph, {0: 0, 1: 1, 2: 2}, 3)
        self.assertLess(ranks[0], ranks[1])
        self.assertLess(ranks[1], ranks[2])

    def test_liveness_equation(self) -> None:
        graph = {0: {1}, 1: set()}
        effects = {0: ({"a0"}, {"a1"}), 1: ({"a1"}, set())}
        live_in, live_out = machine_regions.liveness(graph, effects)
        self.assertEqual(live_out[0], {"a1"})
        self.assertEqual(live_in[0], {"a0"})

    def valid_database(self) -> dict:
        return {
            "inputs": {},
            "instructions": [{
                "address": 4,
                "owner": "unit",
                "successors": [],
                "transfer": "return",
                "reads": ["ra"],
                "writes": [],
                "liveIn": ["ra"],
                "liveOut": [],
            }],
            "entry": 4,
            "owners": [{"id": "unit", "instructions": [4], "entries": [4], "exits": []}],
            "sccs": [{"id": 0, "rank": 0, "instructions": [4], "loop": False}],
            "sccForwardTree": [{"address": 4, "parent": 4, "depth": 0}],
            "sccReverseTree": [{"address": 4, "parent": 4, "depth": 0}],
            "unresolvedIndirectTransfers": [],
            "callGraph": {
                "owners": [{
                    "id": "unit", "qualified": "unit", "kind": "emitted",
                    "parent": None, "instructions": [4], "entryPc": 4,
                }],
                "calls": [{"caller": "program", "callee": "unit", "kind": "runner"}],
                "reachableOwners": ["unit"],
                "unreachableOwners": [],
                "dominatorParent": {"unit": "program"},
                "instructionAddresses": [4],
            },
        }

    def test_call_hierarchy_has_one_runner_root(self) -> None:
        flame = machine_regions.build_flame(self.valid_database())
        binary_children = flame["tree"]["children"]
        program = next(node for node in binary_children if node["name"] == "program")
        self.assertEqual([node["name"] for node in program["children"]], ["unit [unit]"])

    def assert_corruption_rejected(self, mutate) -> None:
        database = copy.deepcopy(self.valid_database())
        mutate(database)
        with self.assertRaises(ValueError):
            machine_regions.validate(database)

    def test_missing_owner_instruction_rejected(self) -> None:
        self.assert_corruption_rejected(lambda db: db["owners"][0].update(instructions=[]))

    def test_duplicate_owner_instruction_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["owners"].append({"id": "other", "instructions": [4]})
        )

    def test_absent_successor_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["instructions"][0].update(successors=[8])
        )

    def test_bad_liveness_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["instructions"][0].update(liveIn=[])
        )

    def test_missing_scc_member_rejected(self) -> None:
        self.assert_corruption_rejected(lambda db: db["sccs"][0].update(instructions=[]))

    def test_invented_exit_rejected(self) -> None:
        self.assert_corruption_rejected(
            lambda db: db["owners"][0].update(exits=[{"source": 4, "target": 4}])
        )

    def test_false_indirect_resolution_rejected(self) -> None:
        def mutate(database: dict) -> None:
            database["instructions"][0]["transfer"] = "indirectTransfer"

        self.assert_corruption_rejected(mutate)

    def test_stale_input_hash_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            elf, program = root / "decoder.elf", root / "program.json"
            elf.write_bytes(b"elf")
            program.write_text("{}")
            database = {
                "inputs": {
                    "elfSha256": machine_regions.sha256(elf),
                    "programJsonSha256": machine_regions.sha256(program),
                }
            }
            machine_regions.validate_input_hashes(database, elf, program)
            elf.write_bytes(b"changed")
            with self.assertRaises(ValueError):
                machine_regions.validate_input_hashes(database, elf, program)


if __name__ == "__main__":
    unittest.main()
