#!/usr/bin/env python3
"""Empirical admission evidence for the reviewed Level 4 ``decodeRaw`` boundaries.

This program checks executions of the unchanged RV64 production ELF.  Its inventory is deliberately
an input, rather than a copy of hierarchy-generator logic: the hierarchy stream owns which 18 local
boundaries/15 function families Level 4 selects, while this program owns how those boundaries are
observed and falsified.  A legacy four-reader/four-decoder inventory is rejected.

The report distinguishes observed facts from contract clauses that the present QEMU plugin cannot
measure.  In particular, instruction PCs can establish sampled entry and exit observations, but do
not bind optimized argument/result registers, prove a caller frame, or establish a universal bound.
Passing this program is admission evidence only; it is never a premise of the Lean compliance proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import ssz_differential_audit as fixtures


EXPECTED_BOUNDARIES = 18
EXPECTED_FAMILIES = 15
UNMEASURED_CLAUSES = (
    "optimized argument locations",
    "optimized result carrier",
    "complete write set or frame condition",
    "caller-frame preservation",
    "universal step bound",
)

# `decodePublicKeys` validates `data.len % 65 == 0` and `count <= MAX_PUBLIC_KEYS` before the
# allocation. Its only post-allocation fallible expression is `readArray(65, data, index * 65)` in a
# loop with `index < count`; the validated length gives that expression exactly 65 available bytes.
# Allocation failure occurs before `result` exists. Thus Zig's `errdefer alloc.free(result)` edge is
# compiled but infeasible for every root input. This is deliberately a singleton certificate: another
# unobserved static edge is a gate failure, not an inference from this source argument.
PUBLIC_KEYS_CLEANUP = ("ssz_raw.decodePublicKeys", 77764, 66624)


@dataclass(frozen=True)
class Boundary:
    identifier: str
    kind: str
    qualified: str
    entry_pc: int
    instruction_pcs: tuple[int, ...]
    exits: tuple[int, ...]
    parent: str
    identity: dict[str, Any] | None
    calls: tuple[tuple[int, int], ...]
    stores: tuple[dict[str, int], ...]
    # A source-less dynamic call frame has a checked target identity/extent but no traceable
    # machine edge.  Keeping it separate prevents empirical evidence from inventing one.
    untraceable_calls: tuple[dict[str, Any], ...] = ()
    carrier_routes: tuple[dict[str, Any], ...] = ()
    subtree_pcs: tuple[int, ...] = ()
    handoffs: tuple[tuple[int, int], ...] = ()
    reentries: tuple[tuple[int, int], ...] = ()
    active_frames: tuple[dict[str, Any], ...] = ()
    tail_dependencies: tuple[dict[str, Any], ...] = ()


def _frame_tree(frames: tuple[dict[str, Any], ...]) -> dict[str, dict[str, Any]]:
    canonical = {}
    def visit(frame: dict[str, Any]) -> None:
        canonical.setdefault(frame["id"], frame)
        for child in frame["activeCalleeFrames"]:
            visit(child)
    for frame in frames: visit(frame)
    return canonical


def _frame_at(frame: dict[str, Any], pair: tuple[int, int] | None) -> tuple[dict[str, Any], dict[str, Any]] | None:
    """Find only an immediate decoded callee transition of `frame`."""
    if pair is None:
        return None
    for child in frame.get("activeCalleeFrames", []):
        for site in child["returnSites"]:
            if (site["sourcePc"], site["targetPc"]) == pair:
                return child, site
    return None


def attribution_state_failures(boundary: Boundary, pcs: list[int], parent_pcs: set[int],
                               tails: dict[tuple[int, int], tuple[set[int], set[int]]] | None = None,
                               indirect_transfers: set[int] | None = None) -> tuple[list[str], dict[str, list[list[int]]]]:
    """Exact H/R selected-parent state machine with recursive generated callee frames."""
    selected, handoffs, reentries = set(boundary.subtree_pcs), set(boundary.handoffs), set(boundary.reentries)
    canonical = _frame_tree(boundary.active_frames); tails = tails or {}; indirect_transfers = indirect_transfers or set()
    mode: str | None = None; stack: list[tuple[dict[str, Any], int]] = []; failures: list[str] = []
    seen = {"handoffs": [], "reentries": [], "returns": []}
    for i, pc in enumerate(pcs):
        pair = (pcs[i-1], pc) if i else None
        # Tail geometry is entered only at the generated decoded-CFG transfer.
        # A matching target PC by itself is not a transition.
        if pair in tails and not (stack and stack[-1][0].get("pendingTail")):
            allowed, completion = tails[pair]
            stack.append(({"tail": True, "activeCalleeExecutionPcs": allowed,
                           "completion": completion, "completed": False}, None))
        if mode is None:
            if pc == boundary.entry_pc: mode = "selected"
            if not stack:
                continue
        if stack:
            frame, ret = stack[-1]
            if frame.get("pendingTail"):
                if pair == frame["transfer"]:
                    frame.pop("pendingTail"); frame["tail"] = True; frame["completed"] = False
                elif pc not in frame["activeCalleeExecutionPcs"]:
                    failures.append(f"forged allocator tail prelude at event {i}"); mode = None; stack.clear()
                continue
            if frame.get("tail"):
                if pc in frame["completion"]:
                    frame["completed"] = True
                    if ret is None:
                        stack.pop(); continue
                if frame.get("completed") and ret is not None and pc == ret:
                    stack.pop(); continue
                if pc not in frame["activeCalleeExecutionPcs"]:
                    failures.append(f"foreign PC {pc:#x} in allocator tail frame at event {i}"); mode = None; stack.clear()
                continue
            if pc == ret and pcs[i-1] in frame["activeCalleeExecutionPcs"]:
                stack.pop(); seen["returns"].append([pair[0], pc])
                # A direct call replaces the decoded H/R fall-through in the execution
                # trace.  Its RA is nevertheless the declared boundary target exactly.
                boundary_pair = (pc - 4, pc)
                if boundary_pair in handoffs:
                    mode = "parent"; seen["handoffs"].append(list(boundary_pair))
                elif boundary_pair in reentries:
                    mode = "selected"; seen["reentries"].append(list(boundary_pair))
                continue
            child_at = _frame_at(frame, pair)
            if child_at is not None:
                child, site = child_at
                if child.get("cycleBackEdge") is not None: child = canonical[child["id"]]
                stack.append((child, site["returnPc"])); continue
            if pc not in frame["activeCalleeExecutionPcs"]:
                pending = next(((transfer, value) for transfer, value in tails.items()
                                if pc in value[0] and pc != transfer[1]), None)
                if pending is not None:
                    transfer, (allowed, completion) = pending
                    stack.append(({"pendingTail": True, "transfer": transfer,
                                   "activeCalleeExecutionPcs": allowed, "completion": completion}, None)); continue
                if pair is not None and pair[0] in indirect_transfers:
                    # This is an unresolved dynamic tail transfer, not a fabricated direct
                    # call edge.  Its target remains explicitly unmeasured.
                    stack.pop(); mode = None; continue
                failures.append(f"foreign PC {pc:#x} in declared call frame at event {i}"); mode = None; stack.clear()
            continue
        if mode == "selected":
            child_at = _frame_at({"activeCalleeFrames": boundary.active_frames}, pair)
            if child_at is not None:
                child, site = child_at
                stack.append((child, site["returnPc"])); continue
            if pair in handoffs: mode = "parent"; seen["handoffs"].append(list(pair))
            elif pc in parent_pcs: failures.append(f"parent PC {pc:#x} in selected mode without H at event {i}"); mode = "parent"
            elif pc not in selected: mode = None; continue
        else:
            if pair in reentries: mode = "selected"; seen["reentries"].append(list(pair))
            elif pc in selected: failures.append(f"selected PC {pc:#x} in parent mode without R at event {i}"); mode = "selected"
            elif pc not in parent_pcs: mode = None; continue
    if stack: failures.append("declared call frame was unterminated at trace end")
    return failures, seen


def int_field(value: object, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    return value


def exit_pc(value: object, name: str) -> int:
    if isinstance(value, dict):
        value = value.get("pc", value.get("sourcePc", value.get("source")))
    return int_field(value, name)


def load_inventory(path: Path) -> tuple[Boundary, ...]:
    """Load only the stable reviewed-inventory boundary schema.

    The hierarchy producer may retain additional JSON fields.  This reader intentionally ignores
    them, so a hierarchy/UI change cannot silently alter the evidence semantics.
    """
    document = json.loads(path.read_text())
    if not isinstance(document, dict):
        raise ValueError("Level 4 inventory must be a JSON object")
    rows = document.get("boundaries")
    if not isinstance(rows, list):
        raise ValueError("Level 4 inventory lacks a boundaries list")
    boundaries: list[Boundary] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"boundary {index} is not an object")
        try:
            identifier = row["id"]
            kind = row["kind"]
            qualified = row["qualified"]
            parent = row["parent"]
            entry = int_field(row["entryPc"], f"boundary {index} entryPc")
            pcs = tuple(int_field(pc, f"boundary {index} instructionPcs") for pc in row["instructionPcs"])
            # Several static alternatives can leave from one source PC.  The trace-visible clause
            # is that source instruction, so retain its stable set rather than rejecting alternatives.
            exits = tuple(sorted({exit_pc(pc, f"boundary {index} exits") for pc in row["exits"]}))
        except KeyError as error:
            raise ValueError(f"boundary {index} lacks {error.args[0]}") from error
        if not all(isinstance(value, str) and value for value in (identifier, kind, qualified, parent)):
            raise ValueError(f"boundary {index} has an empty id, kind, qualified, or parent")
        if not pcs or entry not in pcs:
            raise ValueError(f"boundary {identifier} must include its entry in instructionPcs")
        if len(set(pcs)) != len(pcs):
            raise ValueError(f"boundary {identifier} repeats an instruction PC")
        identity = row.get("functionInstanceIdentity")
        if identity is not None and not isinstance(identity, dict):
            raise ValueError(f"boundary {identifier} has an invalid functionInstanceIdentity")
        if identity is not None:
            if identity.get("qualified") != qualified or not isinstance(identity.get("sourceFile"), str):
                raise ValueError(f"boundary {identifier} identity does not bind its qualified source function")
            if not isinstance(identity.get("specialization"), list) or not isinstance(identity.get("inlineStack"), list):
                raise ValueError(f"boundary {identifier} identity lacks specialization or inlineStack")
        calls_list: list[tuple[int, int]] = []
        untraceable_calls: list[dict[str, Any]] = []
        for call in row.get("calls") or []:
            if not isinstance(call, dict):
                raise ValueError(f"boundary {identifier} call is not an object")
            target = int_field(call.get("targetPc"), f"boundary {identifier} call targetPc")
            source = call.get("sourcePc")
            if source is None:
                identity_ = call.get("targetIdentity")
                extent = call.get("activeCalleeExecutionPcs")
                # Older non-dynamic rows can expose a declared target PC without a generated
                # target identity.  Preserve that limitation.  Dynamic rows which do provide
                # either identity or extent must provide both, so their metadata cannot be half
                # erased and reinterpreted as a traceable edge.
                if ((identity_ is None) != (extent is None)
                        or (identity_ is not None and
                            (not isinstance(identity_, dict) or not isinstance(identity_.get("qualified"), str)
                             or not isinstance(extent, list) or not extent
                             or any(not isinstance(pc, int) for pc in extent)))):
                    raise ValueError(f"boundary {identifier} source-less call lacks target identity and extent")
                untraceable_calls.append({
                    "kind": call.get("kind"), "targetPc": target,
                    **({"targetIdentity": identity_, "activeCalleeExecutionPcs": extent}
                       if identity_ is not None else {}),
                })
            else:
                source = int_field(source, f"boundary {identifier} call sourcePc")
                # Recursive frame declarations may be sourced by a selected subtree descendant;
                # only a physical source owned by this boundary's displayed instruction region is
                # an independently observable boundary call clause.
                if source in pcs:
                    calls_list.append((source, target))
                else:
                    untraceable_calls.append({"kind": call.get("kind"), "sourcePc": source,
                                              "targetPc": target, "state": "subtree-frame-only"})
        calls = tuple(calls_list)
        if any(source not in pcs for source, _target in calls):
            raise ValueError(f"boundary {identifier} declares a call outside instructionPcs")
        stores = tuple(row.get("stores") or [])
        for store in stores:
            if not isinstance(store, dict) or not {"pc", "address", "width", "value"} <= store.keys():
                raise ValueError(f"boundary {identifier} store needs pc, address, width, and value")
            if int_field(store["pc"], f"boundary {identifier} store pc") not in pcs:
                raise ValueError(f"boundary {identifier} declares a store outside instructionPcs")
            for field in ("address", "width", "value"):
                int_field(store[field], f"boundary {identifier} store {field}")
        carrier_routes: list[dict[str, Any]] = []
        for route in row.get("carrierRoutes") or []:
            if not isinstance(route, dict) or not isinstance(route.get("handoff"), dict):
                raise ValueError(f"boundary {identifier} carrier route is malformed")
            handoff = route["handoff"]
            source = int_field(handoff.get("sourcePc"), f"boundary {identifier} carrier handoff sourcePc")
            target = int_field(handoff.get("targetPc"), f"boundary {identifier} carrier handoff targetPc")
            route_identity = route.get("sourceIdentity")
            classification = route.get("classification")
            carrier_pcs = route.get("carrierPcs")
            carrier_paths = route.get("carrierPaths")
            if (source not in pcs or not isinstance(route_identity, dict)
                    or route_identity.get("qualified") != qualified
                    or classification not in {"intermediate", "unclassified", "sourceReviewedOutcomePath"}
                    or not isinstance(carrier_pcs, list)
                    or not isinstance(carrier_paths, list)
                    or any(not isinstance(pc, int) for pc in carrier_pcs)):
                raise ValueError(f"boundary {identifier} carrier route has invalid identity or PCs")
            if classification in {"intermediate", "unclassified"} and (carrier_pcs or carrier_paths):
                raise ValueError(f"boundary {identifier} non-outcome carrier route claims a carrier")
            if classification == "sourceReviewedOutcomePath" and (not carrier_pcs or not carrier_paths):
                raise ValueError(f"boundary {identifier} outcome carrier route lacks parent continuation PCs")
            carrier_routes.append({
                "sourceIdentity": route_identity,
                "handoff": {"sourcePc": source, "targetPc": target},
                "classification": classification,
                "carrierPcs": carrier_pcs,
                "carrierPaths": carrier_paths,
                "registers": route.get("registers", []),
                "stackDescriptors": route.get("stackDescriptors", []),
                "statusTag": route.get("statusTag", {"state": "unmeasured"}),
                "allocation": route.get("allocation", {"state": "unmeasured"}),
                "heapArrayRep": route.get("heapArrayRep", {"state": "unmeasured"}),
            })
        handoffs = tuple((int_field(edge["sourcePc"], "handoff source"), int_field(edge["targetPc"], "handoff target"))
                         for edge in row.get("fragmentHandoffs", []))
        reentries = tuple((int_field(edge["sourcePc"], "reentry source"), int_field(edge["targetPc"], "reentry target"))
                          for edge in row.get("parentReentryEdges", []))
        subtree = tuple(int_field(pc, "subtree PC") for pc in row.get("subtreeOwnedExecutionPcs", []))
        frames = tuple(call for call in row.get("calls", []) if isinstance(call, dict) and "activeCalleeFrames" in call)
        if handoffs or reentries:
            if not subtree or not handoffs or not reentries or not frames:
                raise ValueError(f"boundary {identifier} lacks exact H/R/frame state-machine data")
        tails = tuple(dependency for dependency in row.get("tailDependencies", []) if isinstance(dependency, dict))
        boundaries.append(Boundary(identifier, kind, qualified, entry, pcs, exits, parent, identity,
                                   calls, stores, tuple(untraceable_calls), tuple(carrier_routes),
                                   subtree, handoffs, reentries, frames, tails))

    if len(boundaries) != EXPECTED_BOUNDARIES:
        raise ValueError(f"Level 4 inventory has {len(boundaries)} boundaries, expected {EXPECTED_BOUNDARIES}")
    if len({boundary.identifier for boundary in boundaries}) != EXPECTED_BOUNDARIES:
        raise ValueError("Level 4 inventory repeats a boundary id")
    if len({boundary.qualified for boundary in boundaries}) != EXPECTED_FAMILIES:
        raise ValueError(
            f"Level 4 inventory has {len({boundary.qualified for boundary in boundaries})} function families, "
            f"expected {EXPECTED_FAMILIES}"
        )
    return tuple(boundaries)


def parse_trace(path: Path) -> tuple[list[int], list[dict[str, int]]]:
    pcs: list[int] = []
    stores: list[dict[str, int]] = []
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields:
            continue
        if fields[0] == "E" and len(fields) == 2:
            pcs.append(int(fields[1], 0))
        elif fields[0] == "S" and len(fields) == 6:
            pc, address, width, value, sp = (int(field, 0) for field in fields[1:])
            stores.append({"pc": pc, "address": address, "width": width, "value": value, "sp": sp})
    return pcs, stores


def observation(
    boundary: Boundary,
    pcs: list[int],
    stores: list[dict[str, int]],
    *,
    edges: set[tuple[int, int]] | None = None,
) -> dict[str, Any]:
    owned = set(boundary.instruction_pcs)
    edges = set(zip(pcs, pcs[1:])) if edges is None else edges
    declared_stores = [
        store for store in boundary.stores
        if any(all(observed[field] == store[field] for field in store) for observed in stores)
    ]
    return {
        "entryReached": boundary.entry_pc in pcs,
        "exitReached": sorted(set(boundary.exits).intersection(pcs)),
        "instructionEvents": sum(pc in owned for pc in pcs),
        "declaredCallsReached": [
            {"sourcePc": source, "targetPc": target}
            for source, target in boundary.calls if (source, target) in edges
        ],
        "declaredStoresReached": declared_stores,
        "observedStores": [store for store in stores if store["pc"] in owned],
        "observedCarrierRoutes": [carrier_route_observation(route, pcs, boundary.entry_pc) for route in boundary.carrier_routes],
    }


def carrier_route_observation(route: dict[str, Any], pcs: list[int], entry_pc: int = -1) -> dict[str, Any]:
    """Record a carrier only after its exact handoff in this one trace invocation.

    A carrier PC alone is deliberately not evidence: the same instruction can occur in another
    vector or another decoder invocation.  This observation retains the handoff event indices and
    searches only the suffix following each such event in the same trace.
    """
    handoff = (route["handoff"]["sourcePc"], route["handoff"]["targetPc"])
    handoff_events = [
        index for index, edge in enumerate(zip(pcs, pcs[1:])) if edge == handoff
    ]
    observed_carriers = sorted({
        pc for index in handoff_events
        for pc in pcs[index + 1: next((later for later in range(index + 1, len(pcs))
                                      if pcs[later] == entry_pc), len(pcs))]
        if pc in set(route["carrierPcs"])
    })
    return {
        "sourceIdentity": route["sourceIdentity"],
        "handoff": route["handoff"],
        "classification": route["classification"],
        "carrierPcs": route["carrierPcs"],
        "handoffEvents": len(handoff_events),
        "observedCarrierPcs": observed_carriers,
        "evidenceScope": "one-production-vector-one-process-invocation",
        # Static instruction/DWARF/source review admits the route; this finite trace only says
        # which continuation PCs followed an exact handoff, never their register or heap meaning.
        "staticEvidence": "production-ELF instruction plus validated raw-DWARF source identity",
        "statusTag": route["statusTag"],
        "allocation": route["allocation"],
        "heapArrayRep": route["heapArrayRep"],
    }


def merge_observations(boundary: Boundary, observations: list[dict[str, Any]]) -> dict[str, Any]:
    """Merge trace-local observations without manufacturing a cross-vector route."""
    if not observations:
        raise ValueError("cannot merge no production observations")
    route_observations: dict[tuple[str, int, int], list[dict[str, Any]]] = {}
    for record in observations:
        for route in record["observedCarrierRoutes"]:
            key = (route["sourceIdentity"]["qualified"], route["handoff"]["sourcePc"],
                   route["handoff"]["targetPc"])
            route_observations.setdefault(key, []).append(route)
    merged_routes = []
    for route in boundary.carrier_routes:
        key = (route["sourceIdentity"]["qualified"], route["handoff"]["sourcePc"],
               route["handoff"]["targetPc"])
        local = route_observations.get(key, [])
        # Each local record already required its own handoff event.  Unioning these checked
        # observations cannot pair a handoff from one vector with a carrier from another.
        template = carrier_route_observation(route, [], boundary.entry_pc)
        merged_routes.append({
            **template,
            "handoffEvents": sum(record["handoffEvents"] for record in local),
            "observedCarrierPcs": sorted({
                pc for record in local for pc in record["observedCarrierPcs"]
            }),
        })
    return {
        "entryReached": any(record["entryReached"] for record in observations),
        "exitReached": sorted({pc for record in observations for pc in record["exitReached"]}),
        "instructionEvents": sum(record["instructionEvents"] for record in observations),
        "declaredCallsReached": [
            {"sourcePc": source, "targetPc": target}
            for source, target in boundary.calls
            if any({(call["sourcePc"], call["targetPc"]) for call in record["declaredCallsReached"]}
                   >= {(source, target)} for record in observations)
        ],
        "declaredStoresReached": [
            store for store in boundary.stores
            if any(any(all(observed[field] == store[field] for field in store)
                       for observed in record["declaredStoresReached"])
                   for record in observations)
        ],
        "observedStores": [store for record in observations for store in record["observedStores"]],
        "observedCarrierRoutes": merged_routes,
    }


def validate_merged_observation(
    boundary: Boundary, record: dict[str, Any], local_observations: list[dict[str, Any]]
) -> list[str]:
    """Reject an aggregate record that was not derived from its individual vector invocations."""
    if record != merge_observations(boundary, local_observations):
        return ["merged production observations were changed or cross-vector forged"]
    return []


def statically_unreachable_call(boundary: Boundary, call: tuple[int, int]) -> str | None:
    if (
        (boundary.qualified, *call) == PUBLIC_KEYS_CLEANUP
        and boundary.identity is not None
        and boundary.identity.get("qualified") == "ssz_raw.decodePublicKeys"
        and boundary.identity.get("sourceFile") == "src/stateless/stateless/ssz_raw.zig"
    ):
        return "decodePublicKeys errdefer cleanup: validated 65-byte lanes make its post-allocation readArray total"
    return None


def required_calls(boundary: Boundary) -> tuple[tuple[int, int], ...]:
    return tuple(call for call in boundary.calls if statically_unreachable_call(boundary, call) is None)


def validate_observation(boundary: Boundary, record: dict[str, Any], *, strict_calls: bool = True) -> list[str]:
    failures: list[str] = []
    if not record["entryReached"]:
        failures.append("entry was not observed")
    if boundary.exits and not record["exitReached"]:
        failures.append("no declared exit was observed")
    if record["instructionEvents"] <= 0:
        failures.append("no owned instruction was observed")
    observed_calls = {(call["sourcePc"], call["targetPc"]) for call in record["declaredCallsReached"]}
    missing_calls = set(required_calls(boundary)) - observed_calls
    if strict_calls and missing_calls:
        failures.append(f"declared call targets were not observed: {sorted(missing_calls)}")
    return failures


def validate_observed_claims(record: dict[str, Any], calls: list[dict[str, int]], stores: list[dict[str, int]]) -> list[str]:
    """Check the trace-backed call/store claims selected from this finite observation."""
    failures: list[str] = []
    observed_calls = {(call["sourcePc"], call["targetPc"]) for call in record["declaredCallsReached"]}
    if any((call["sourcePc"], call["targetPc"]) not in observed_calls for call in calls):
        failures.append("an observed declared call target disappeared")
    observed_stores = {
        (store["pc"], store["address"], store["width"], store["value"])
        for store in record["declaredStoresReached"]
    }
    if any((store["pc"], store["address"], store["width"], store["value"]) not in observed_stores for store in stores):
        failures.append("an observed declared store changed")
    return failures


def validate_observed_carrier_claims(record: dict[str, Any], claims: list[dict[str, Any]]) -> list[str]:
    """A claimed carrier needs its exact same-invocation handoff evidence."""
    observed = {
        (route["sourceIdentity"]["qualified"], route["handoff"]["sourcePc"], route["handoff"]["targetPc"]): route
        for route in record["observedCarrierRoutes"]
    }
    for claim in claims:
        key = (claim["sourceIdentity"]["qualified"], claim["handoff"]["sourcePc"], claim["handoff"]["targetPc"])
        route = observed.get(key)
        if (route is None or route["classification"] != "sourceReviewedOutcomePath"
                or route["handoffEvents"] <= 0
                or not set(claim["observedCarrierPcs"]) <= set(route["observedCarrierPcs"])):
            return ["an observed outcome carrier PC disappeared"]
    return []


def mutation_checks(boundary: Boundary, record: dict[str, Any]) -> dict[str, bool]:
    """Show the checker rejects corruption of every currently measurable clause."""
    mutations = {
        "entry": {**record, "entryReached": False},
        "instruction-count": {**record, "instructionEvents": 0},
    }
    if boundary.exits:
        mutations["exit"] = {**record, "exitReached": []}
    if record["declaredCallsReached"]:
        mutations["call-edge"] = {**record, "declaredCallsReached": []}
    if record["declaredStoresReached"]:
        mutations["store-address-width-value"] = {**record, "declaredStoresReached": []}
    observed_carriers = [route for route in record["observedCarrierRoutes"] if route["observedCarrierPcs"]]
    if observed_carriers:
        mutations["outcome-carrier-pc"] = {
            **record,
            "observedCarrierRoutes": [
                {**route, "observedCarrierPcs": []} if route["observedCarrierPcs"] else route
                for route in record["observedCarrierRoutes"]
            ],
        }
    call_claims = [
        {"sourcePc": source, "targetPc": target}
        for source, target in required_calls(boundary)
    ]
    store_claims = record["declaredStoresReached"]
    return {
        name: bool(validate_observation(boundary, mutated)
                   or validate_observed_claims(mutated, call_claims, store_claims)
                   or validate_observed_carrier_claims(mutated, observed_carriers))
        for name, mutated in mutations.items()
    }


def run(command: list[str], data: bytes) -> fixtures.Outcome:
    return fixtures.run(command, data)


def run_oracles(args: argparse.Namespace, name: str, data: bytes, accepted: bool) -> dict[str, Any]:
    outcomes = {
        "executionSpecs": run([str(args.reference_python), str(args.reference_program)], data),
        "leanSsz": fixtures.run_lean(args.lean_binary, data),
        "sourceProbe": run([str(args.zesu_value_binary)], data),
    }
    failures: list[str] = []
    if accepted:
        for oracle, outcome in outcomes.items():
            if outcome.returncode != 0:
                failures.append(f"{oracle} rejected accepted vector")
            elif not fixtures.valid_protocol(outcome.stdout):
                failures.append(f"{oracle} emitted malformed ssz-value-v1")
        if len({outcome.stdout for outcome in outcomes.values()}) != 1:
            failures.append("execution-specs, Lean SSZ, and source probe disagree")
    elif any(outcome.returncode == 0 for outcome in outcomes.values()):
        failures.append("an oracle accepted rejected vector")
    return {
        "name": name,
        "accepted": accepted,
        "outcomes": {
            oracle: {"returncode": result.returncode, "sha256": hashlib.sha256(result.stdout).hexdigest()}
            for oracle, result in outcomes.items()
        },
        "failures": failures,
    }


def run_production_trace(args: argparse.Namespace, data: bytes, trace: Path) -> fixtures.Outcome:
    return run(
        ["setarch", "-R", str(args.qemu), "-plugin", f"{args.plugin},out={trace}", str(args.rv64_binary)],
        data,
    )


def default_vectors() -> tuple[tuple[str, bytes, bool], ...]:
    """Focused PR #77 vectors, retained as data rather than its obsolete contract surface."""
    rich = fixtures.make_rich_v4()
    layout = fixtures.layout(rich)
    return (
        ("new-payload-rich", rich, True),
        ("new-payload-noncanonical-offset", fixtures.make_v4(npr_padding=1), False),
        ("new-payload-malformed-deposits", fixtures.make_v4(
            requests=fixtures.execution_requests(deposits=b"X")), False),
        ("execution-witness-rich", rich, True),
        ("execution-witness-empty", fixtures.make_v4(witness_bytes=fixtures.witness((), (), ())), True),
        ("execution-witness-noncanonical-offset", fixtures.set_u32(rich, layout["witness"], 0), False),
        ("chain-config-rich", rich, True),
        ("chain-config-absent-blob-schedule", fixtures.make_v4(
            chain_bytes=fixtures.chain_config(blob_schedule=None)), True),
        ("chain-config-unknown-fork", fixtures.make_v4(chain_bytes=fixtures.chain_config(fork=21)), False),
        ("chain-config-noncanonical-offset", fixtures.set_u32(rich, layout["chain"] + 8, 0), False),
        ("public-keys-rich", rich, True),
        ("public-keys-empty", fixtures.make_v4(public_keys=b""), True),
        ("public-keys-one", fixtures.make_v4(public_keys=b"\x04" + bytes(range(64))), True),
        ("public-keys-nondivisible", fixtures.make_v4(public_keys=bytes(64)), False),
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--reference-program", type=Path, required=True)
    parser.add_argument("--lean-binary", type=Path, required=True)
    parser.add_argument("--zesu-value-binary", type=Path, required=True)
    parser.add_argument("--qemu", type=Path, required=True)
    parser.add_argument("--plugin", type=Path, required=True)
    parser.add_argument("--rv64-binary", type=Path, required=True)
    parser.add_argument("--out-json", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    boundaries = load_inventory(args.inventory)
    machine = json.loads((args.inventory.parent / "machine-regions.json").read_text())
    fi6 = next(owner for owner in machine["callGraph"]["owners"] if owner["id"] == "fi:6")
    parent_pcs = set(fi6["instructions"])
    indirect_transfers = {instruction["address"] for instruction in machine["instructions"]
                          if instruction["transfer"] in {"indirectTransfer", "indirectCall"}}
    tails = {(tail["transfer"]["sourcePc"], tail["transfer"]["targetPc"]):
             (set(tail["combinedInstructionPcs"]), set(tail["completionSourcePcs"]))
             for boundary in boundaries for tail in boundary.tail_dependencies}
    tails.update({(None, boundary.entry_pc): (set(tail["combinedInstructionPcs"]), set(tail["completionSourcePcs"]))
                  for boundary in boundaries for tail in boundary.tail_dependencies})
    vectors = default_vectors()
    oracle_records = [run_oracles(args, *vector) for vector in vectors]
    failures = [failure for record in oracle_records for failure in record["failures"]]
    vector_observations: list[dict[str, Any]] = []
    all_pcs: list[int] = []
    all_stores: list[dict[str, int]] = []
    observations_by_boundary: dict[str, list[dict[str, Any]]] = {
        boundary.identifier: [] for boundary in boundaries
    }
    with tempfile.TemporaryDirectory(prefix="level4-evidence-") as temporary:
        for name, data, accepted in vectors:
            trace = Path(temporary) / f"{name}.trace"
            production = run_production_trace(args, data, trace)
            expected_return = 0 if accepted else 1
            if production.returncode != expected_return:
                failures.append(f"production ELF returned {production.returncode} for {name}, expected {expected_return}")
            if accepted and not production.stdout.startswith(b"ok "):
                failures.append(f"production ELF accepted {name} without an ok checksum")
            if not accepted and production.stdout != b"invalid\n":
                failures.append(f"production ELF rejected {name} with unexpected output")
            pcs, stores = parse_trace(trace)
            all_pcs.extend(pcs)
            all_stores.extend(stores)
            local_observations = {}
            for boundary in boundaries:
                record = observation(boundary, pcs, stores)
                if boundary.handoffs:
                    state_failures, state = attribution_state_failures(
                        boundary, pcs, parent_pcs, tails, indirect_transfers)
                    record["attributionStateMachine"] = state
                    record["attributionStateFailures"] = state_failures
                    failures.extend(f"{boundary.identifier}: {name}: {failure}" for failure in state_failures)
                local_observations[boundary.identifier] = record
            for identifier, record in local_observations.items():
                observations_by_boundary[identifier].append(record)
            vector_observations.append({
                "name": name,
                "accepted": accepted,
                "returncode": production.returncode,
                "traceEvents": len(pcs),
                "stores": len(stores),
                "boundaries": local_observations,
            })
    records = []
    for boundary in boundaries:
        # Merge trace-local facts only.  In particular, a handoff in one vector may not justify a
        # carrier PC observed in another vector.
        record = merge_observations(boundary, observations_by_boundary[boundary.identifier])
        clause_failures = validate_observation(boundary, record, strict_calls=False) + validate_observed_claims(
        record, record["declaredCallsReached"], record["declaredStoresReached"]
        ) + validate_observed_carrier_claims(record, [
            route for route in record["observedCarrierRoutes"] if route["observedCarrierPcs"]
        ]) + validate_merged_observation(
            boundary, record, observations_by_boundary[boundary.identifier]
        )
        mutations = mutation_checks(boundary, record)
        if not all(mutations.values()):
            clause_failures.append("a measurable-clause mutation was accepted")
        failures.extend(f"{boundary.identifier}: {failure}" for failure in clause_failures)
        records.append({
            "boundary": asdict(boundary),
            "observation": record,
            "measuredClauses": [
                "entry", "owned instruction execution",
                *( ["exit"] if boundary.exits else [] ),
                *( ["observed declared call targets"] if record["declaredCallsReached"] else [] ),
                *( ["observed declared store address, width, and value"] if record["declaredStoresReached"] else [] ),
                *( ["observed outcome carrier PCs"]
                   if any(route["observedCarrierPcs"] for route in record["observedCarrierRoutes"])
                   else [] ),
            ],
            "unmeasuredClauses": [
                *UNMEASURED_CLAUSES,
                *( ["declared exits"] if not boundary.exits else [] ),
                *(
                    ["unobserved declared store address, width, and value"]
                    if len(record["declaredStoresReached"]) != len(boundary.stores) else []
                ),
                *( ["source-less dynamic call-frame edge"] if boundary.untraceable_calls else [] ),
                *(
                    ["declared direct call targets not reached by the finite production vectors"]
                    if set(required_calls(boundary)) - {
                        (call["sourcePc"], call["targetPc"]) for call in record["declaredCallsReached"]
                    } else []
                ),
                *( ["outcome carrier register values, stack contents, status meaning, allocation, and HeapArrayRep"]
                   if boundary.carrier_routes else [] ),
            ],
            "untraceableDynamicCallFrames": list(boundary.untraceable_calls),
            "attributionStateMachine": [record.get("attributionStateMachine", {})
                                        for record in observations_by_boundary[boundary.identifier]],
            "outcomeCarrierRoutes": record["observedCarrierRoutes"],
            "staticallyUnreachableClauses": [
                {"sourcePc": source, "targetPc": target, "reason": reason}
                for source, target in boundary.calls
                if (reason := statically_unreachable_call(boundary, (source, target))) is not None
            ],
            "mutationRejected": mutations,
            "failures": clause_failures,
        })
    report = {
        "schemaVersion": 1,
        "claim": "finite production-ELF evidence; not a proof premise",
        "inventory": {"boundaries": len(boundaries), "functionFamilies": len({b.qualified for b in boundaries})},
        "vectors": oracle_records,
        "productionVectors": vector_observations,
        "production": {"traceEvents": len(all_pcs), "stores": len(all_stores)},
        "boundaries": records,
        "unmeasuredClauses": list(UNMEASURED_CLAUSES),
        "passed": not failures,
        "failures": failures,
    }
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if failures:
        print("Level 4 contract evidence failed:", file=sys.stderr)
        print("\n".join(f"- {failure}" for failure in failures), file=sys.stderr)
        return 1
    print("Level 4 contract evidence: 18 boundary observations, 15 families, mutations rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
