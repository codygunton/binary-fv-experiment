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
    tail_dependencies: tuple["TailDependency", ...] = ()
    cfg_edges: tuple[tuple[int, int], ...] = ()
    full_execution_pcs: tuple[int, ...] = ()
    fragment_handoffs: tuple[tuple[int, int], ...] = ()
    parent_reentry_edges: tuple[tuple[int, int], ...] = ()
    active_callee_extents: tuple[ChildCall, ...] = ()


@dataclass(frozen=True)
class TailDependency:
    source_pc: int
    target_pc: int
    callee_instruction_pcs: tuple[int, ...]
    completion_source_pcs: tuple[int, ...]
    combined_instruction_pcs: tuple[int, ...]


@dataclass(frozen=True)
class ChildCall:
    source_pc: int | None
    target_pc: int
    instruction_pcs: tuple[int, ...]
    selected_boundary_id: str | None = None
    # ``(physical call source, callee target, RA fall-through)`` for source-less declarations.
    return_pcs: tuple[tuple[int, int, int], ...] = ()


@dataclass(frozen=True)
class Bound:
    """A numeric sampled ceiling; it intentionally has no executable formula language."""

    identifier: str
    family: str
    kind: str
    constant: int
    coefficient: int = 0
    metric: str | None = None
    divisor: int = 1
    increment: int = 0
    exit_source_pcs: tuple[int, ...] = ()
    reader_fragment_edges: tuple[tuple[int, int], ...] = ()

    def ceiling(self, root_size: int) -> int:
        if self.kind == "constant":
            return self.constant
        if self.metric != "rootSize":
            raise ValueError(f"bound {self.identifier} has unsupported metric {self.metric!r}")
        return self.constant + self.coefficient * (root_size // self.divisor + self.increment)


@dataclass(frozen=True)
class BoundSpec:
    claim: str
    metrics: dict[str, str]
    bounds: tuple[Bound, ...]


@dataclass(frozen=True)
class Invocation:
    entry_event: int
    exit_event: int
    instruction_events: int
    completion_return: tuple[int, int, int] | None = None


@dataclass(frozen=True)
class AttributionObservation:
    handoffs: tuple[tuple[int, int], ...] = ()
    reentries: tuple[tuple[int, int], ...] = ()
    source_less_returns: tuple[tuple[int, int, int], ...] = ()


def attribution_check(boundary: Boundary, pcs: list[int], parent_pcs: set[int]) -> tuple[list[str], AttributionObservation]:
    """Check one vector's exact selected/fi:6/callee state machine.

    H and R are mode switches, not decoder terminals.  This intentionally has no broad executable
    address range: selected mode is ``subtreeOwnedExecutionPcs``, parent mode is fi:6's decoded
    ownership, and call mode is the generated callee extent.  A trace may leave fi:6 after the
    monitored decoder route; that ends this monitor only after no known selected/parent/call PC
    remains active.  Each vector is checked independently, so no cross-vector edge is invented.
    """
    selected = set(boundary.full_execution_pcs)
    parent = parent_pcs
    handoffs = set(boundary.fragment_handoffs)
    reentries = set(boundary.parent_reentry_edges)
    direct_frames = {
        (call.source_pc, call.target_pc): (call, call.source_pc + 4)
        for call in boundary.active_callee_extents if call.source_pc is not None
    }
    source_less_frames = {
        (site_source, call.target_pc): (call, return_pc)
        for call in boundary.active_callee_extents if call.source_pc is None
        for site_source, target, return_pc in call.return_pcs
        if target == call.target_pc
    }
    frame_entries = {**direct_frames, **source_less_frames}
    mode: str | None = None
    frame: tuple[ChildCall, int, tuple[int, int] | None] | None = None
    failures: list[str] = []
    seen_handoffs: list[tuple[int, int]] = []
    seen_reentries: list[tuple[int, int]] = []
    seen_returns: list[tuple[int, int, int]] = []

    for event, pc in enumerate(pcs):
        prev = pcs[event - 1] if event else None
        pair = (prev, pc) if prev is not None else None
        if mode is None:
            if pc == boundary.entry_pc:
                mode = "selected"
            continue

        if frame is not None:
            active, return_pc, call_edge = frame
            if pc == return_pc and prev in active.instruction_pcs:
                if call_edge in source_less_frames:
                    assert call_edge is not None
                    seen_returns.append((call_edge[0], call_edge[1], return_pc))
                frame = None
                mode = "selected"
            else:
                if pair in frame_entries:
                    failures.append(f"malformed nested call at event {event} while call frame is active")
                if pc not in active.instruction_pcs:
                    failures.append(f"foreign PC {pc:#x} in declared call frame at event {event}")
                    frame = None
                    mode = None
                continue

        assert mode in {"selected", "parent"}
        if mode == "selected":
            if pair in frame_entries:
                call, return_pc = frame_entries[pair]
                frame = (call, return_pc, pair)
                continue
            if pair in handoffs:
                seen_handoffs.append(pair)
                mode = "parent"
            elif pc in parent:
                failures.append(f"parent PC {pc:#x} in selected mode without fragment handoff at event {event}")
                mode = "parent"
            elif pc not in selected:
                # The selected invocation has returned to its caller or another decodeRaw child.
                # A known child PC is still a forged/omitted H transition and must not be hidden.
                mode = None
                continue
        else:
            if pair in reentries:
                seen_reentries.append(pair)
                mode = "selected"
            elif pc in selected:
                failures.append(f"selected PC {pc:#x} in parent mode without re-entry at event {event}")
                mode = "selected"
            elif pc not in parent:
                mode = None
                continue

        if mode == "selected":
            if pc not in selected:
                failures.append(f"foreign PC {pc:#x} in selected mode at event {event}")
                continue
        elif pc not in parent:
            failures.append(f"foreign PC {pc:#x} in parent mode at event {event}")

    if frame is not None:
        _call, return_pc, _edge = frame
        failures.append(f"declared call frame was unterminated at trace end (expected RA return {return_pc:#x})")
    return failures, AttributionObservation(tuple(seen_handoffs), tuple(seen_reentries), tuple(seen_returns))


def attribution_mutation_checks(boundary: Boundary, pcs: list[int], parent_pcs: set[int]) -> dict[str, bool]:
    """Mutation witnesses for H/R/call-frame state transitions in one vector."""
    starts = [index for index, pc in enumerate(pcs) if pc == boundary.entry_pc]
    if not starts:
        return {}
    trace = pcs[starts[0]:]
    result: dict[str, bool] = {}
    selected, parent = set(boundary.full_execution_pcs), parent_pcs
    _baseline_failures, baseline = attribution_check(boundary, trace, parent)

    def rejected(mutated: list[int]) -> bool:
        return bool(attribution_check(boundary, mutated, parent)[0])

    for index, pair in enumerate(zip(trace, trace[1:])):
        if pair in boundary.fragment_handoffs:
            # Deleting H makes its source jump directly to the following parent instruction;
            # forging it uses a real fi:6 PC but one not declared by H.
            result["skipped-handoff"] = rejected(trace[:index + 1] + trace[index + 2:])
            forged = next((pc for pc in parent if (pair[0], pc) not in boundary.fragment_handoffs), None)
            if forged is not None:
                changed = trace[:]
                changed[index + 1] = forged
                result["invented-handoff"] = rejected(changed)
            break
    for index, pair in enumerate(zip(trace, trace[1:])):
        if pair in boundary.parent_reentry_edges:
            result["missing-reentry"] = rejected(trace[:index + 1] + trace[index + 2:])
            forged = next((pc for pc in selected if (pair[0], pc) not in boundary.parent_reentry_edges), None)
            if forged is not None:
                changed = trace[:]
                changed[index + 1] = forged
                result["wrong-reentry"] = rejected(changed)
            break
    source_less = {
        (source, target, return_pc, call.instruction_pcs)
        for call in boundary.active_callee_extents if call.source_pc is None
        for source, target, return_pc in call.return_pcs
    }
    for index, pair in enumerate(zip(trace, trace[1:])):
        for source, target, return_pc, active_pcs in source_less:
            if (source, target, return_pc) not in baseline.source_less_returns:
                continue
            if pair != (source, target):
                continue
            try:
                returned = next(event for event in range(index + 2, len(trace))
                                if trace[event] == return_pc and trace[event - 1] in active_pcs)
            except StopIteration:
                continue
            result["return-deletion"] = rejected(trace[:returned] + trace[returned + 1:])
            forged = next((pc for pc in selected if pc != return_pc), None)
            if forged is not None:
                changed = trace[:]
                changed[returned] = forged
                result["return-forgery"] = rejected(changed)
            return result
    return result


def int_field(value: object, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    return value


def exit_pc(value: object, name: str) -> int:
    if isinstance(value, dict):
        value = value.get("pc", value.get("sourcePc", value.get("source")))
    return int_field(value, name)


def pc_list(value: object, name: str) -> tuple[int, ...]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    pcs = tuple(int_field(pc, name) for pc in value)
    if not pcs or tuple(sorted(set(pcs))) != pcs:
        raise ValueError(f"{name} must be a non-empty sorted unique PC list")
    return pcs


def pc_pairs(value: object, name: str) -> tuple[tuple[int, int], ...]:
    if not isinstance(value, list) or any(not isinstance(pair, list) or len(pair) != 2 for pair in value):
        raise ValueError(f"{name} must be source/target pairs")
    return tuple((int_field(pair[0], f"{name} source"), int_field(pair[1], f"{name} target"))
                 for pair in value)


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
        calls = tuple(
            (int_field(call["sourcePc"], f"boundary {identifier} call sourcePc"),
             int_field(call["targetPc"], f"boundary {identifier} call targetPc"))
            for call in (row.get("calls") or []) if isinstance(call.get("sourcePc"), int)
        )
        active_callee_extents = tuple(
            ChildCall((int_field(call["sourcePc"], f"boundary {identifier} active call sourcePc")
                       if call.get("sourcePc") is not None else None),
                      int_field(call["targetPc"], f"boundary {identifier} active call targetPc"),
                      pc_list(call["activeCalleeExecutionPcs"], f"boundary {identifier} active callee PCs"),
                      None,
                      tuple((int_field(site["sourcePc"], f"boundary {identifier} return source PC"),
                             int_field(site["targetPc"], f"boundary {identifier} return target PC"),
                             int_field(site["returnPc"], f"boundary {identifier} return PC"))
                            for site in call.get("returnSites", [])))
            for call in (row.get("calls") or []) if "activeCalleeExecutionPcs" in call
        )
        for call in (row.get("calls") or []):
            if "activeCalleeExecutionPcs" not in call:
                continue
            sites = call.get("returnSites")
            if call.get("sourcePc") is None:
                if not isinstance(sites, list) or not sites:
                    raise ValueError(f"boundary {identifier} source-less call lacks RA return sites")
                if any(not isinstance(site, dict) or site.get("linkRegister") != "ra"
                       for site in sites):
                    raise ValueError(f"boundary {identifier} source-less return does not bind ra")
            elif sites is not None:
                raise ValueError(f"boundary {identifier} resolved call falsely declares RA return sites")
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
        cfg_edges = tuple(
            (exit_pc(exit_row, f"boundary {identifier} exits"),
             int_field(exit_row["target"], f"boundary {identifier} exit target"))
            for exit_row in row["exits"] if isinstance(exit_row, dict) and "target" in exit_row
        )
        tail_dependencies: list[TailDependency] = []
        for dependency in row.get("tailDependencies") or []:
            if not isinstance(dependency, dict) or not isinstance(dependency.get("transfer"), dict):
                raise ValueError(f"boundary {identifier} has an invalid tail dependency")
            transfer = dependency["transfer"]
            source = int_field(transfer.get("sourcePc"), f"boundary {identifier} tail sourcePc")
            target = int_field(transfer.get("targetPc"), f"boundary {identifier} tail targetPc")
            callee_pcs = pc_list(dependency.get("calleeInstructionPcs"),
                                  f"boundary {identifier} tail calleeInstructionPcs")
            completion_pcs = pc_list(dependency.get("completionSourcePcs"),
                                      f"boundary {identifier} tail completionSourcePcs")
            combined_pcs = pc_list(dependency.get("combinedInstructionPcs"),
                                    f"boundary {identifier} tail combinedInstructionPcs")
            if source not in pcs or target not in callee_pcs or not set(completion_pcs) <= set(callee_pcs):
                raise ValueError(f"boundary {identifier} tail dependency has invalid transfer geometry")
            if set(combined_pcs) != set(pcs) | set(callee_pcs):
                raise ValueError(f"boundary {identifier} tail dependency has an inexact combined region")
            tail_dependencies.append(TailDependency(source, target, callee_pcs, completion_pcs, combined_pcs))
        # The Level-4 H/R geometry records the whole selected subtree, not just this source
        # instance's direct PCs.  Dynamic attribution must not reject an inline descendant merely
        # because its DWARF owner is below the selected child.
        full_execution = pc_list(row["subtreeOwnedExecutionPcs"],
                                 f"boundary {identifier} subtreeOwnedExecutionPcs") \
            if "subtreeOwnedExecutionPcs" in row else (
                pc_list(row["fullExecutionPcs"], f"boundary {identifier} fullExecutionPcs")
                if "fullExecutionPcs" in row else pcs)
        handoffs = pc_pairs([[edge["sourcePc"], edge["targetPc"]]
                             for edge in row.get("fragmentHandoffs", [])], f"boundary {identifier} fragmentHandoffs")
        reentries = pc_pairs([[edge["sourcePc"], edge["targetPc"]]
                              for edge in row.get("parentReentryEdges", [])], f"boundary {identifier} parentReentryEdges")
        if handoffs or reentries:
            if not handoffs or not reentries or "subtreeOwnedExecutionPcs" not in row:
                raise ValueError(f"boundary {identifier} attribution requires exact subtree, H, and R")
            if tuple(sorted(set(handoffs))) != handoffs or tuple(sorted(set(reentries))) != reentries:
                raise ValueError(f"boundary {identifier} attribution transitions are not sorted unique")
        boundaries.append(Boundary(identifier, kind, qualified, entry, pcs, exits, parent, identity,
                                   calls, stores, tuple(tail_dependencies), cfg_edges, full_execution,
                                   handoffs, reentries, active_callee_extents))

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


def load_bound_spec(path: Path, boundaries: tuple[Boundary, ...]) -> BoundSpec:
    """Load numeric sampled ceilings matched exactly to the reviewed inventory.

    `rootSize` is a deliberately conservative observable for a child slice/copy/offset count when
    the QEMU trace does not expose the optimized carrier register.  It is evidence metadata, not a
    reconstruction of that register and never establishes a universal trace bound.
    """
    document = json.loads(path.read_text())
    if not isinstance(document, dict) or document.get("schemaVersion") != 2:
        raise ValueError("Level 4 bound spec must use schemaVersion 2")
    claim = document.get("claim")
    metrics = document.get("metrics")
    rows = document.get("bounds")
    if not isinstance(claim, str) or not claim:
        raise ValueError("Level 4 bound spec needs a non-empty claim")
    if not isinstance(metrics, dict) or not isinstance(metrics.get("rootSize"), str):
        raise ValueError("Level 4 bound spec needs a rootSize metric description")
    if not isinstance(rows, list):
        raise ValueError("Level 4 bound spec lacks a bounds list")

    parsed: list[Bound] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"bound {index} is not an object")
        identifier, family, kind = row.get("id"), row.get("family"), row.get("kind")
        if not all(isinstance(value, str) and value for value in (identifier, family, kind)):
            raise ValueError(f"bound {index} needs non-empty id, family, and kind")
        exit_sources = row.get("exitSourcePcs", [])
        fragment_edges = row.get("readerFragmentEdges", [])
        if not isinstance(exit_sources, list):
            raise ValueError(f"bound {identifier} exitSourcePcs must be a list")
        parsed_exit_sources = tuple(sorted({int_field(pc, f"bound {identifier} exitSourcePcs") for pc in exit_sources}))
        if not isinstance(fragment_edges, list) or any(not isinstance(edge, list) or len(edge) != 2 for edge in fragment_edges):
            raise ValueError(f"bound {identifier} readerFragmentEdges must be source/successor pairs")
        parsed_edges = tuple((int_field(edge[0], f"bound {identifier} reader edge source"),
                              int_field(edge[1], f"bound {identifier} reader edge successor")) for edge in fragment_edges)
        if kind == "constant":
            if not set(row) <= {"id", "family", "kind", "constant", "exitSourcePcs",
                                "readerFragmentEdges"}:
                raise ValueError(f"constant bound {identifier} has unsupported fields")
            parsed.append(Bound(identifier, family, kind, int_field(row["constant"], f"bound {identifier} constant"),
                                exit_source_pcs=parsed_exit_sources,
                                reader_fragment_edges=parsed_edges))
        elif kind == "affineFloor":
            required = {"id", "family", "kind", "constant", "coefficient", "metric", "divisor", "increment"}
            if not set(row) <= required | {"exitSourcePcs", "readerFragmentEdges"} or not required <= set(row):
                raise ValueError(f"affine bound {identifier} has unsupported fields")
            metric = row["metric"]
            if metric != "rootSize":
                raise ValueError(f"affine bound {identifier} must use rootSize")
            divisor = int_field(row["divisor"], f"bound {identifier} divisor")
            if divisor == 0:
                raise ValueError(f"affine bound {identifier} divisor must be positive")
            parsed.append(Bound(
                identifier, family, kind,
                int_field(row["constant"], f"bound {identifier} constant"),
                int_field(row["coefficient"], f"bound {identifier} coefficient"), metric, divisor,
                int_field(row["increment"], f"bound {identifier} increment"), parsed_exit_sources,
                parsed_edges,
            ))
        else:
            raise ValueError(f"bound {identifier} has unsupported kind {kind!r}")

    expected = {boundary.identifier: boundary.qualified for boundary in boundaries}
    actual = {bound.identifier: bound.family for bound in parsed}
    if len(actual) != len(parsed):
        raise ValueError("Level 4 bound spec repeats a boundary id")
    if set(actual) != set(expected):
        missing, extra = sorted(set(expected) - set(actual)), sorted(set(actual) - set(expected))
        raise ValueError(f"Level 4 bound spec ids differ from inventory: missing={missing}, extra={extra}")
    mismatched = sorted(identifier for identifier, family in actual.items() if expected[identifier] != family)
    if mismatched:
        raise ValueError(f"Level 4 bound spec family differs from inventory: {mismatched}")
    resolved: list[Bound] = []
    by_id = {boundary.identifier: boundary for boundary in boundaries}
    for bound in parsed:
        boundary = by_id[bound.identifier]
        exit_sources = bound.exit_source_pcs or by_id[bound.identifier].exits
        if not exit_sources:
            raise ValueError(f"bound {bound.identifier} lacks declared exit-source PCs")
        # fi136's reviewed semantic endpoint is the generated `zesu_raw_alloc` tail callee;
        # its source-derived combined region is recorded by Level4BoundaryInventory.
        if any(pc not in by_id[bound.identifier].instruction_pcs and bound.identifier != "fi:136"
               for pc in exit_sources):
            raise ValueError(f"bound {bound.identifier} exit-source PC is outside its instruction PCs")
        resolved.append(Bound(
            bound.identifier, bound.family, bound.kind, bound.constant, bound.coefficient, bound.metric,
            bound.divisor, bound.increment, exit_sources,
            bound.reader_fragment_edges,
        ))
    return BoundSpec(claim, dict(metrics), tuple(resolved))


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
    }


def segment_invocations(boundary: Boundary, exit_source_pcs: tuple[int, ...], pcs: list[int]) -> tuple[list[Invocation], list[str]]:
    """Segment one production trace at this boundary's entry and declared exit-source PCs."""
    if not exit_source_pcs:
        return [], ["boundary has no declared exit-source PC"]
    owned = set(boundary.instruction_pcs).union(exit_source_pcs)
    invocations: list[Invocation] = []
    failures: list[str] = []
    active: tuple[int, int] | None = None  # (entry event index, owned instruction count)
    for event, pc in enumerate(pcs):
        if pc == boundary.entry_pc:
            if active is not None:
                failures.append(f"invocation entered at event {active[0]} was unterminated before event {event}")
            active = (event, 0)
        if active is not None and pc in owned:
            active = (active[0], active[1] + 1)
        if active is not None and pc in exit_source_pcs:
            invocations.append(Invocation(active[0], event, active[1]))
            active = None
    if active is not None:
        failures.append(f"invocation entered at event {active[0]} was unterminated at trace end")
    return invocations, failures


def validate_sampled_bound(bound: Bound, root_size: int, invocations: list[Invocation]) -> list[str]:
    ceiling = bound.ceiling(root_size)
    return [
        f"invocation {index} has {invocation.instruction_events} owned instruction events, ceiling {ceiling}"
        for index, invocation in enumerate(invocations)
        if invocation.instruction_events > ceiling
    ]

def validate_reader_fragments(bound: Bound, pcs: list[int]) -> list[str]:
    edges = set(zip(pcs, pcs[1:]))
    return [f"reader fragment edge {source:#x}->{successor:#x} was not observed"
            for source, successor in bound.reader_fragment_edges if (source, successor) not in edges]


def bound_report(bound: Bound, root_size: int | None, *, unmeasured: bool = False) -> dict[str, Any]:
    return {
        "kind": bound.kind,
        "constant": bound.constant,
        "coefficient": bound.coefficient,
        "metric": bound.metric,
        "divisor": bound.divisor,
        "increment": bound.increment,
        "exitSourcePcs": list(bound.exit_source_pcs),
        "metricValue": root_size if bound.metric is not None else None,
        "ceiling": None if unmeasured or root_size is None else bound.ceiling(root_size),
        "universalValidity": "unmeasured: optimized dynamic carrier schema not admitted" if unmeasured else "assumption",
    }


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


def validate_observation(boundary: Boundary, record: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if not record["entryReached"]:
        failures.append("entry was not observed")
    if boundary.exits and not record["exitReached"]:
        failures.append("no declared exit was observed")
    if record["instructionEvents"] <= 0:
        failures.append("no owned instruction was observed")
    observed_calls = {(call["sourcePc"], call["targetPc"]) for call in record["declaredCallsReached"]}
    missing_calls = set(required_calls(boundary)) - observed_calls
    if missing_calls:
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
    call_claims = [
        {"sourcePc": source, "targetPc": target}
        for source, target in required_calls(boundary)
    ]
    store_claims = record["declaredStoresReached"]
    return {
        name: bool(validate_observation(boundary, mutated) or validate_observed_claims(mutated, call_claims, store_claims))
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
    parser.add_argument("--bound-spec", type=Path, required=True)
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
    bound_spec = load_bound_spec(args.bound_spec, boundaries)
    machine = json.loads((args.inventory.parent / "machine-regions.json").read_text())
    owner = next(item for item in machine["callGraph"]["owners"] if item.get("id") == "fi:6")
    parent_pcs = {int_field(pc, "fi:6 instruction") for pc in owner["instructions"]}
    bounds_by_id = {bound.identifier: bound for bound in bound_spec.bounds}
    vectors = default_vectors()
    oracle_records = [run_oracles(args, *vector) for vector in vectors]
    failures = [failure for record in oracle_records for failure in record["failures"]]
    vector_observations: list[dict[str, Any]] = []
    all_pcs: list[int] = []
    all_stores: list[dict[str, int]] = []
    all_edges: set[tuple[int, int]] = set()
    sampled_failures: dict[str, list[str]] = {boundary.identifier: [] for boundary in boundaries}
    sampled_invocations: dict[str, list[Invocation]] = {boundary.identifier: [] for boundary in boundaries}
    sampled_ceilings: dict[str, list[int]] = {boundary.identifier: [] for boundary in boundaries}
    sampled_mutations: dict[str, list[dict[str, bool]]] = {boundary.identifier: [] for boundary in boundaries}
    attribution_observations: dict[str, list[AttributionObservation]] = {boundary.identifier: [] for boundary in boundaries}
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
            all_edges.update(zip(pcs, pcs[1:]))
            vector_boundaries: dict[str, dict[str, Any]] = {}
            for boundary in boundaries:
                bound = bounds_by_id[boundary.identifier]
                attributed = bool(boundary.fragment_handoffs or boundary.parent_reentry_edges)
                if attributed:
                    segmentation_failures, attribution = attribution_check(boundary, pcs, parent_pcs)
                    # A malformed generated call extent is itself the admission failure.  Its
                    # follow-on mutation results are unmeasured, rather than falsely reported as
                    # a checker acceptance after the monitor has already stopped at the bad frame.
                    segmentation_mutations = (attribution_mutation_checks(boundary, pcs, parent_pcs)
                                              if not segmentation_failures else {})
                    attribution_observations[boundary.identifier].append(attribution)
                    invocations: list[Invocation] = []
                    bound_failures = segmentation_failures
                else:
                    invocations, segmentation_failures = segment_invocations(boundary, bound.exit_source_pcs, pcs)
                    segmentation_mutations = {}
                    bound_failures = segmentation_failures + validate_sampled_bound(bound, len(data), invocations)
                bound_failures += validate_reader_fragments(bound, pcs)
                sampled_invocations[boundary.identifier].extend(invocations)
                if not attributed:
                    sampled_ceilings[boundary.identifier].append(bound.ceiling(len(data)))
                if segmentation_mutations:
                    sampled_mutations[boundary.identifier].append(segmentation_mutations)
                    if not all(segmentation_mutations.values()):
                        bound_failures.append("an attribution-state-machine mutation was accepted")
                sampled_failures[boundary.identifier].extend(
                    f"{name}: {failure}" for failure in bound_failures
                )
                vector_boundaries[boundary.identifier] = {
                    "observation": observation(boundary, pcs, stores),
                    "sampledBound": {
                        **bound_report(bound, len(data), unmeasured=attributed),
                        "segmentation": "attribution-state-machine" if attributed else "entry-exit-source",
                        "mutationRejected": segmentation_mutations,
                        "attribution": ({
                            "fragmentHandoffs": [list(pair) for pair in attribution.handoffs],
                            "parentReentries": [list(pair) for pair in attribution.reentries],
                            "sourceLessRaReturns": [list(item) for item in attribution.source_less_returns],
                        } if attributed else {}),
                        "invocations": [asdict(invocation) for invocation in invocations],
                        "failures": bound_failures,
                    },
                }
            vector_observations.append({
                "name": name,
                "accepted": accepted,
                "returncode": production.returncode,
                "traceEvents": len(pcs),
                "stores": len(stores),
                "boundaries": vector_boundaries,
            })
    records = []
    for boundary in boundaries:
        # Do not concatenate traces to derive edges: the last PC of one vector and the first PC
        # of another are not one production transfer.
        record = observation(boundary, all_pcs, all_stores, edges=all_edges)
        clause_failures = validate_observation(boundary, record) + validate_observed_claims(
            record, record["declaredCallsReached"], record["declaredStoresReached"]
        )
        clause_failures.extend(sampled_failures[boundary.identifier])
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
            ],
            "unmeasuredClauses": [
                *UNMEASURED_CLAUSES,
                *( ["declared exits"] if not boundary.exits else [] ),
                *(
                    ["unobserved declared store address, width, and value"]
                    if len(record["declaredStoresReached"]) != len(boundary.stores) else []
                ),
            ],
            "staticallyUnreachableClauses": [
                {"sourcePc": source, "targetPc": target, "reason": reason}
                for source, target in boundary.calls
                if (reason := statically_unreachable_call(boundary, (source, target))) is not None
            ],
            "mutationRejected": mutations,
            "sampledBound": {
                **bound_report(bounds_by_id[boundary.identifier], None,
                                unmeasured=bool(boundary.fragment_handoffs or boundary.parent_reentry_edges)),
                "metricDescription": bound_spec.metrics["rootSize"] if bounds_by_id[boundary.identifier].metric else None,
                "observedInvocations": len(sampled_invocations[boundary.identifier]),
                "maximumInstructionEvents": max(
                    (invocation.instruction_events for invocation in sampled_invocations[boundary.identifier]), default=None
                ),
                "sampledCeilings": sorted(set(sampled_ceilings[boundary.identifier])),
                "segmentationMutationRejected": {
                    name: all(mutation.get(name, False) for mutation in sampled_mutations[boundary.identifier]
                              if name in mutation)
                    for name in sorted({name for mutation in sampled_mutations[boundary.identifier]
                                        for name in mutation})
                },
                "attribution": {
                    "fragmentHandoffs": [list(pair) for pair in sorted({pair for observation in attribution_observations[boundary.identifier]
                                                                          for pair in observation.handoffs})],
                    "parentReentries": [list(pair) for pair in sorted({pair for observation in attribution_observations[boundary.identifier]
                                                                         for pair in observation.reentries})],
                    "sourceLessRaReturns": [list(item) for item in sorted({item for observation in attribution_observations[boundary.identifier]
                                                                             for item in observation.source_less_returns})],
                },
            },
            "failures": clause_failures,
        })
    report = {
        "schemaVersion": 2,
        "claim": "finite production-ELF evidence; not a proof premise; dynamic optimized-carrier bounds are unmeasured",
        "inventory": {"boundaries": len(boundaries), "functionFamilies": len({b.qualified for b in boundaries})},
        "vectors": oracle_records,
        "productionVectors": vector_observations,
        "production": {"traceEvents": len(all_pcs), "stores": len(all_stores)},
        "sampledBounds": {
            "claim": bound_spec.claim,
            "metricDescriptions": bound_spec.metrics,
            "universalValidity": "dynamic optimized-carrier bounds unmeasured until their carrier schema is admitted",
        },
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
