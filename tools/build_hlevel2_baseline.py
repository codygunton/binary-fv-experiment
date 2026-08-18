#!/usr/bin/env python3
"""Build an honest baseline for the proof below ``root_compliance hLevel2``."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

PROVED_LEVEL2_ENTRIES = {0x14E00, 0x14E7C}
PROVED_LEVEL2_NAMES = {"memcpy"}
PROVED_LEVEL1_NAMES = {"read_input", "zkvm_exit", "alt_fl_alloc.get"}
EXPECTED_DIRECT_PC_COUNT = 157
DECLARATION = re.compile(
    r"^(?:private\s+)?(?:theorem|def|abbrev|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE)
EXACT_PC = re.compile(r"/--(?:(?!-/).)*?`0x([0-9a-fA-F]+):", re.DOTALL)


def rewrite_disposition(module: str, source: str) -> dict[str, str | bool]:
    """Classify every root dependency by its role in this fixed rewrite experiment."""
    if not module.startswith("BinaryFv.Zesu"):
        return {"kind": "existing_generic_library", "rewriteCandidate": False,
                "reason": "Shared Binary/RISC-V proof API; consumers are audited instead."}
    if ".Specs." in module or ".Contracts." in module:
        return {"kind": "preserved_statement", "rewriteCandidate": False,
                "reason": "Specification or contract statement; theorem types may not change."}
    if ".Artifacts." in module or ".Elflings." in module:
        return {"kind": "generated_evidence", "rewriteCandidate": False,
                "reason": "Pinned or generated artifact evidence, not handwritten proof text."}
    if ".DecodedValue." in module:
        return {"kind": "semantic_bridge", "rewriteCandidate": False,
                "reason": "Decoded-value semantics are preserved by the experiment."}
    if ".MachineExecution." in module:
        if "Seg." in source or "Seg " in source:
            return {"kind": "seg_composition", "rewriteCandidate": False,
                    "reason": "Already uses existential Seg composition."}
        if any(name in source for name in (
                "configuredRegisterWriteStep", "configuredAuipcStep", "configuredJalrCallStep",
                "configuredDwordStoreStep", "configuredDwordLoadStep", "configuredRetStep",
                "configuredJStep")):
            return {"kind": "instruction_class_consumer", "rewriteCandidate": False,
                    "reason": "Already instantiates a shared instruction-class theorem."}
        if "try_step" in source:
            return {"kind": "retained_exact_machine_step", "rewriteCandidate": False,
                    "reason": "Exact-site API or lower instruction helper; final census found no paying shared body."}
        return {"kind": "retained_machine_proof_support", "rewriteCandidate": False,
                "reason": "Frame, representation, or composition support retained after the final pattern audit."}
    if ".Entrypoints." in module or module == "BinaryFv.Zesu.Root":
        return {"kind": "retained_refinement_composition", "rewriteCandidate": False,
                "reason": "Reviewed conditional edge, contract surface, or transfer composition."}
    return {"kind": "retained_zesu_support", "rewriteCandidate": False,
            "reason": "Zesu-specific support reviewed with no paying rewrite candidate."}


def read_dependencies(path: Path) -> tuple[list[dict], list[dict]]:
    declarations, edges = [], []
    for line in path.read_text().splitlines():
        fields = line.split("\t")
        kind, left, right = fields[:3]
        if kind == "declaration":
            if len(fields) != 5:
                raise ValueError("declaration row lacks a source range")
            declarations.append({"name": left, "module": right,
                                 "startLine": int(fields[3]), "endLine": int(fields[4])})
        elif kind == "edge":
            edges.append({"declaration": left, "dependency": right})
        else:
            raise ValueError(f"unknown dependency row {kind!r}")
    names = {row["name"] for row in declarations}
    if "BinaryFv.Zesu.root_compliance" not in names:
        raise ValueError("dependency graph does not contain root_compliance")
    if any(edge["declaration"] not in names or edge["dependency"] not in names
           for edge in edges):
        raise ValueError("dependency edge escapes the declaration closure")
    return declarations, edges


def module_path(source_root: Path, module: str) -> Path:
    return source_root / (module.replace(".", "/") + ".lean")


def expand_private_sources(source_root: Path, declarations: list[dict]) -> list[dict]:
    """Recover source dependencies hidden inside opaque private theorem constants."""
    by_module: dict[str, list[dict]] = {}
    for row in declarations:
        if row["name"].startswith("_private."):
            by_module.setdefault(row["module"], []).append(row)
    expanded = list(declarations)
    known = {(row["module"], row["startLine"], row["endLine"]) for row in declarations}
    for module, anchors in by_module.items():
        path = module_path(source_root, module)
        if not path.exists():
            continue
        text = path.read_text()
        lines = text.splitlines()
        matches = list(DECLARATION.finditer(text))
        source_rows = []
        for index, match in enumerate(matches):
            start = text.count("\n", 0, match.start()) + 1
            end_offset = matches[index + 1].start() if index + 1 < len(matches) else len(text)
            end = text.count("\n", 0, end_offset) + 1
            source_rows.append({"name": match.group(1), "module": module,
                                "startLine": start, "endLine": end,
                                "text": "\n".join(lines[start - 1:end])})
        selected = set()
        for anchor in anchors:
            selected.update(row["name"] for row in source_rows
                            if row["startLine"] <= anchor["startLine"] <= row["endLine"])
        changed = True
        while changed:
            changed = False
            bodies = "\n".join(row["text"] for row in source_rows if row["name"] in selected)
            for row in source_rows:
                if row["name"] not in selected and re.search(
                        rf"\b{re.escape(row['name'])}\b", bodies):
                    selected.add(row["name"])
                    changed = True
        for row in source_rows:
            key = (module, row["startLine"], row["endLine"])
            if row["name"] in selected and key not in known:
                expanded.append({key: value for key, value in row.items() if key != "text"} |
                                {"name": f"{module}.{row['name']}",
                                 "recoveredFromPrivateSource": True})
                known.add(key)
    return expanded


def non_comment_lines(text: str) -> int:
    count, depth = 0, 0
    for line in text.splitlines():
        visible, index = [], 0
        while index < len(line):
            if depth and line.startswith("-/", index):
                depth -= 1; index += 2
            elif line.startswith("/-", index):
                depth += 1; index += 2
            elif not depth and line.startswith("--", index):
                break
            elif not depth:
                visible.append(line[index]); index += 1
            else:
                index += 1
        if "".join(visible).strip():
            count += 1
    return count


def validate_direct_pcs(pcs: set[int], elf_pcs: set[int]) -> None:
    if len(pcs) != EXPECTED_DIRECT_PC_COUNT:
        raise ValueError(
            f"direct proof attribution omitted PCs: expected {EXPECTED_DIRECT_PC_COUNT}, got {len(pcs)}")
    if missing := pcs - elf_pcs:
        raise ValueError(f"direct proof attribution contains forged PCs: {sorted(missing)}")


def build(dependency_path: Path, source_root: Path, cfg: dict, flame: dict,
          level1: dict, level2: dict) -> dict:
    artifacts = [cfg["artifact"], level1["artifact"], level2["artifact"]]
    if any(artifact != artifacts[0] for artifact in artifacts[1:]):
        raise ValueError("CFG and contract manifests describe different artifacts")
    declarations, edges = read_dependencies(dependency_path)
    kernel_source_declarations = len(declarations)
    declarations = expand_private_sources(source_root, declarations)
    for declaration in declarations:
        path = module_path(source_root, declaration["module"])
        lines = path.read_text().splitlines() if path.exists() else []
        source = "\n".join(lines[max(0, declaration["startLine"] - 1):
                                  declaration["endLine"]])
        declaration["rewriteDisposition"] = rewrite_disposition(declaration["module"], source)
    root_entry = int(flame["tree"]["name"].rsplit("[fn:", 1)[1].rstrip("]"), 16)
    main = next(row for row in cfg["functionInstances"]
                if row["kind"] == "concrete" and row["entryPc"] == root_entry)
    l1_by_id = {row["id"]: row for row in level1["instances"]}
    l2_by_parent: dict[str, set[int]] = {}
    for row in level2["instances"]:
        for parent in row["parentInstanceIds"]:
            l2_by_parent.setdefault(parent, set()).update(row["executionPcs"])

    l1_extent = {pc for row in level1["instances"] for pc in row["executionPcs"]}
    level0_direct = set(main["pcs"]) - l1_extent
    level1_direct: dict[str, list[int]] = {}
    for row in level1["instances"]:
        level1_direct[row["id"]] = sorted(set(row["executionPcs"]) -
                                           l2_by_parent.get(row["id"], set()))
    proved_l2 = [row for row in level2["instances"]
                 if row["qualified"] in PROVED_LEVEL2_NAMES or
                 row["entryPc"] in PROVED_LEVEL2_ENTRIES]
    direct_regions = {
        "level0Parent": sorted(level0_direct),
        "provedLevel1": sorted({pc for row in level1["instances"]
                                if row["qualified"] in PROVED_LEVEL1_NAMES
                                for pc in row["executionPcs"]}),
        "conditionalLevel1Parent": sorted({pc for ident, pcs in level1_direct.items()
                                           if l1_by_id[ident]["qualified"] not in
                                           PROVED_LEVEL1_NAMES for pc in pcs}),
        "provedLevel2": sorted({pc for row in proved_l2 for pc in row["executionPcs"]}),
    }
    boundary_union = sorted({pc for pcs in direct_regions.values() for pc in pcs})
    elf_pcs = {instruction["pc"] for function in cfg["functions"]
               for block in function["blocks"] for instruction in block["instructions"]}
    if missing := set(boundary_union) - elf_pcs:
        raise ValueError(f"baseline contains PCs absent from the ELF: {sorted(missing)}")

    unresolved = [row for row in level2["instances"] if row not in proved_l2]
    conditional_pcs = sorted({pc for row in unresolved for pc in row["executionPcs"]})
    source_lines: dict[str, set[int]] = {}
    direct_attribution: dict[int, list[str]] = {}
    for declaration in declarations:
        path = module_path(source_root, declaration["module"])
        if not path.exists() or declaration["startLine"] == 0:
            continue
        lines = path.read_text().splitlines()
        start, end = declaration["startLine"], declaration["endLine"]
        source_lines.setdefault(declaration["module"], set()).update(range(start, end + 1))
        snippet = "\n".join(lines[max(0, start - 3):end])
        for match in EXACT_PC.finditer(snippet):
            pc = int(match.group(1), 16)
            if pc in boundary_union:
                direct_attribution.setdefault(pc, []).append(declaration["name"])
    non_comment_loc = 0
    for module, selected_lines in source_lines.items():
        lines = module_path(source_root, module).read_text().splitlines()
        non_comment_loc += non_comment_lines("\n".join(
            line for number, line in enumerate(lines, 1) if number in selected_lines))
    direct_pcs = sorted(direct_attribution)
    validate_direct_pcs(set(direct_pcs), elf_pcs)
    return {
        "schemaVersion": 1,
        "artifact": artifacts[0],
        "root": "BinaryFv.Zesu.root_compliance",
        "declarations": declarations,
        "dependencyEdges": edges,
        "counts": {
            "kernelSourceDeclarations": kernel_source_declarations,
            "dependencyEdges": len(edges),
            "sourceDeclarations": len(declarations),
            "rewriteCandidates": sum(
                row["rewriteDisposition"]["rewriteCandidate"] for row in declarations),
            "nonCommentLeanLoc": non_comment_loc,
            "level0DirectRegionPcs": len(direct_regions["level0Parent"]),
            "conditionalLevel1DirectRegionPcs": len(direct_regions["conditionalLevel1Parent"]),
            "boundaryRegionUniquePcs": len(boundary_union),
            "unresolvedLevel2Contracts": len(unresolved),
            "conditionalContractUniquePcs": len(conditional_pcs),
        },
        "coverage": {
            "meaning": "Region geometry; this is not an executed-step count.",
            "regions": direct_regions,
            "boundaryUnion": boundary_union,
            "directlyDischargedStepPcs": direct_pcs,
            "directStepAttribution": [
                {"pc": pc, "declarations": sorted(set(direct_attribution[pc]))}
                for pc in direct_pcs],
            "directStepStatus": "exact-PC docstrings in source declarations used by the root proof",
            "conditionalContractRegions": [
                {"id": row["id"], "qualified": row["qualified"],
                 "pcs": row["executionPcs"]} for row in unresolved
            ], "conditionalContractUniquePcs": conditional_pcs,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dependencies", required=True, type=Path)
    parser.add_argument("--source-root", required=True, type=Path)
    for name in ("cfg", "flame", "level1", "level2", "output"):
        parser.add_argument(f"--{name}", required=True, type=Path)
    args = parser.parse_args()
    result = build(args.dependencies, args.source_root, *(
        json.loads(getattr(args, name).read_text()) for name in
        ("cfg", "flame", "level1", "level2")))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
