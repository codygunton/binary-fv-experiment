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

    def test_dynamic_attribution_validator_rejects_deletion_and_forgery(self) -> None:
        parent = {"id": "fi:6", "regions": [{"start": 77412, "size": 8}], "parent": None}
        decoder = {"id": "fi:102", "qualified": "ssz_raw.decodeChainConfig", "entryPc": 76108,
                   "regions": [{"start": 77404, "size": 8}], "parent": "fi:6", "inlineStack": [{"callerQualified": "ssz_raw.decodeRaw", "line": 211, "column": 48}]}
        database = {"instructions": [
            {"address": 77404, "owner": "fi:102", "successors": [77408]},
            {"address": 77408, "owner": "fi:102", "successors": [77412]},
            {"address": 77412, "owner": "fi:6", "successors": []},
            {"address": 77400, "owner": "fi:6", "successors": [77404]},
        ], "callGraph": {"owners": [parent, decoder]}}
        manifest = {"parent": {"id": "fi:6"}, "boundaries": [{
            "id": "fi:102", "instructionPcs": [77404, 77408], "ownedExecutionPcs": [77404, 77408],
            "subtreeOwnedExecutionPcs": [77404, 77408], "fullExecutionPcs": [77404, 77408],
            "parentReentryEdges": [{"sourcePc": 77400, "targetPc": 77404}],
            "fragmentHandoffs": [{"sourcePc": 77408, "targetPc": 77412}],
        }]}
        machine_regions.validate_level4_attribution_boundaries(database, manifest)
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
        call = {"id": "fi:134", "kind": "direct", "sourcePc": 77404, "targetPc": 78000,
                **machine_regions.dynamic_call_target_extent(callee, {"fi:6": parent, "fi:102": decoder,
                                                                        "fi:134": callee})}
        excluded_call = {"id": "excluded:9", "kind": "direct", "sourcePc": None, "targetPc": 79000,
                         **machine_regions.dynamic_call_target_extent(excluded, {"fi:6": parent,
                                                                                   "fi:102": decoder,
                                                                                   "fi:134": callee,
                                                                                   "excluded:9": excluded}),
                         "returnSites": [{"sourcePc": 77408, "targetPc": 79000,
                                          "returnPc": 77412, "linkRegister": "ra"}]}
        database = {"instructions": [
            {"address": 77404, "owner": "fi:102", "successors": [77408, 78000]},
            {"address": 77408, "owner": "fi:102", "successors": [77412, 79000],
             "transfer": "directCall", "mnemonic": "jalr", "word": 0x000080e7},
            {"address": 77412, "owner": "fi:6", "successors": []},
            {"address": 77400, "owner": "fi:6", "successors": [77404]},
            {"address": 78000, "owner": "fi:134", "successors": [78004]},
            {"address": 78004, "owner": "fi:134", "successors": []},
            {"address": 79000, "owner": "excluded:9", "successors": [79004]},
            {"address": 79004, "owner": "excluded:9", "successors": []},
            {"address": 66124, "owner": "fi:0", "successors": []},
        ], "callGraph": {"owners": [parent, decoder, callee, excluded, foreign], "calls": [
            {"caller": "fi:102", "callee": "fi:134", "kind": "direct", "source": 77404},
            {"caller": "fi:102", "callee": "fi:134", "kind": "direct", "source": None},
            {"caller": "fi:102", "callee": "excluded:9", "kind": "direct", "source": None},
        ]}}
        manifest = {"parent": {"id": "fi:6"}, "boundaries": [{
            "id": "fi:102", "instructionPcs": [77404, 77408], "ownedExecutionPcs": [77404, 77408],
            "subtreeOwnedExecutionPcs": [77404, 77408], "fullExecutionPcs": [77404, 77408], "calls": [call, excluded_call],
            "parentReentryEdges": [{"sourcePc": 77400, "targetPc": 77404}],
            "fragmentHandoffs": [{"sourcePc": 77408, "targetPc": 77412}],
        }]}
        machine_regions.validate_level4_attribution_boundaries(database, manifest)
        self.assertEqual(
            [call["sourcePc"] for call in machine_regions.declared_level4_calls(
                "fi:102", database["callGraph"], {owner["id"]: owner for owner in database["callGraph"]["owners"]}
            )],
            [77404, None],
        )
        duplicate = copy.deepcopy(manifest["boundaries"][0]["calls"][0])
        duplicate["sourcePc"] = None
        manifest["boundaries"][0]["calls"].append(duplicate)
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"].pop()
        manifest["boundaries"][0]["calls"][1].pop("returnSites")
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["returnSites"] = [{
            "sourcePc": 77408, "targetPc": 79000, "returnPc": 99999, "linkRegister": "ra",
        }]
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["returnSites"] = [{
            "sourcePc": 77408, "targetPc": 79000, "returnPc": 77412, "linkRegister": "ra",
        }]
        database["instructions"][1]["transfer"] = "ordinary"
        with self.assertRaisesRegex(ValueError, "direct jalr call"):
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
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][0]["activeCalleeExecutionPcs"] = [78000, 99999]
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][0]["activeCalleeExecutionPcs"] = [78000, 78004]
        manifest["boundaries"][0]["calls"][1].pop("activeCalleeExecutionPcs")
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["activeCalleeExecutionPcs"] = [79000, 99999]
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["calls"][1]["activeCalleeExecutionPcs"] = [79000, 79004]
        manifest["boundaries"][0]["calls"][0]["activeCalleeExecutionPcs"] = [78000, 78004, 66124]
        with self.assertRaisesRegex(ValueError, "call target extents are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)
        manifest["boundaries"][0]["parentReentryEdges"] = [{"sourcePc": 77400, "targetPc": 77408}]
        with self.assertRaisesRegex(ValueError, "re-entries are incomplete or forged"):
            machine_regions.validate_level4_attribution_boundaries(database, manifest)

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
