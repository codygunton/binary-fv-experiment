#!/usr/bin/env python3
"""Generate typed, non-production Lean staging for the hLevel3 refinement."""

from __future__ import annotations

import argparse
import json
import os
import textwrap
from pathlib import Path

DIRECT_PROOF_PATH = Path(os.environ.get(
    "HLEVEL3_DIRECT_PROOFS", Path(__file__).with_name("hlevel3_direct_proofs.json")))
DIRECT_PROOF_DOCUMENT = json.loads(DIRECT_PROOF_PATH.read_text())
DIRECT_PROOF_ROWS = DIRECT_PROOF_DOCUMENT["proofs"]
DIRECT_PROOFS = {row["field"]: row["theorem"] for row in DIRECT_PROOF_ROWS}
DIRECT_CONTRACTS = {row["field"]: row["contract"] for row in DIRECT_PROOF_ROWS}
RESOLVED_PARENT_PROOFS = {
    row["field"]: row["theorem"]
    for row in DIRECT_PROOF_DOCUMENT.get("resolvedParents", [])
}
DESIGNED_CONTRACTS = {
    "ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b":
        "BinaryFv.Zesu.Staging."
        "Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract",
    "ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94":
        "BinaryFv.Zesu.Staging."
        "Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract",
}


def contract_name(field: str) -> str:
    return f"Proposed_{field}_Contract"


def parent_type(field: str) -> str:
    if field == "sszDecode":
        return "SszDecodeLevel2InstanceContract"
    return field[0].upper() + field[1:] + "InstanceContract"


def lean_list(values: list[str]) -> str:
    return ", ".join(f"`{value}`" for value in values) if values else "none"


def unique(values: list[str]) -> list[str]:
    return list(dict.fromkeys(values))


def comments(*values: str) -> list[str]:
    result = []
    for value in values:
        result.extend(textwrap.wrap(value, width=96, break_long_words=False,
                                    break_on_hyphens=False) or [""])
    return result


def contract_body(field: str) -> list[str]:
    if field in DIRECT_PROOFS:
        return [f"  exact {DIRECT_CONTRACTS[field]}"]
    if field in DESIGNED_CONTRACTS:
        return [f"  exact {DESIGNED_CONTRACTS[field]}"]
    return ["  sorry"]


def generate(inventory: dict, guidance: dict, admission: dict, catalogue: dict) -> str:
    if guidance["artifact"] != inventory["artifact"] or admission["artifact"] != inventory["artifact"]:
        raise ValueError("hLevel3 staging inputs describe different ELFs")
    admitted = {row["instanceId"]: row for row in admission["instances"]}
    hints = {row["id"]: row for row in guidance["obligations"]}
    contracts_by_qualified = {}
    for row in inventory["proposedLevel3Contracts"]:
        contracts_by_qualified.setdefault(row["qualified"], []).append(row["field"])
    lines = [
        "import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts",
        "import BinaryFv.Zesu.MachineExecution.InstructionClassSteps",
        "import BinaryFv.Zesu.MachineExecution.MemcpyProof",
        "import BinaryFv.Zesu.MachineExecution.Level0MainSteps",
        "import BinaryFv.RiscV.Elfling.Seg",
        "import BinaryFv.Zesu.Staging.MemWriteInt",
        "import BinaryFv.Zesu.Staging.MemReadInt",
        "import BinaryFv.Zesu.Staging.ReadU32",
        "import BinaryFv.Zesu.Staging.ForkName",
        "import BinaryFv.Zesu.Staging.CheckedSlice",
        "import BinaryFv.Zesu.Staging.WriteOutput",
        "import BinaryFv.Zesu.Staging.RawEncoder",
        "import BinaryFv.Zesu.Staging.IntegerEncoder",
        "import BinaryFv.Zesu.Staging.BooleanEncoder",
        "import BinaryFv.Zesu.Staging.WriteSuccessInt",
        "import BinaryFv.Zesu.Staging.OptionalEncoder",
        "",
        "/-!",
        "# Generated hLevel3 staging",
        "",
        "This file is not in the production import tree. Each contract definition is a reviewed",
        "design hole. Each refinement theorem is a machine-proof hole with generated guidance.",
        "-/",
        "",
        "namespace BinaryFv.Zesu.Staging.HLevel3",
        "",
        "open PreSail LeanRV64DExecutable.Functions Register",
        "open BinaryFv.RiscV",
        "",
    ]
    for row in inventory["proposedLevel3Contracts"]:
        review = admitted[row["instanceId"]]
        bindings = [
            f"{binding['name']}=x{binding['machineRegister']}"
            for binding in review["boundaryBindings"]
            if binding["machineRegister"] is not None
        ]
        siblings = [field for field in contracts_by_qualified[row["qualified"]]
                    if field != row["field"]]
        lines.extend([
            "/--",
            *comments(
                f"Contract design hole for `{row['instanceId']}` at `0x{row['entryPc']:x}`.",
                f"Source operation: {review['semanticReview']['operation']}",
                f"Source reference: `{review['semanticReview']['reference']}`.",
                f"Family: `{review['contractFamily']}`.",
                f"Boundary bindings: {lean_list(bindings)}.",
                f"Same-source contract candidates: {lean_list(siblings)}.",
                "Evidence source: `hlevel3-admission.json` records observed entries, exits, and access.",
                "Required design: bind semantic values to the recorded DWARF registers or memory.",
                "Required design: state configured-machine, access, termination, and exact frame facts.",
                "Do not replace this hole with a PC-only or unbound semantic contract."),
            "-/",
            f"def {contract_name(row['field'])} : Prop := by",
            *contract_body(row["field"]),
            "",
        ])
    lines.extend([
        f"/-- The {len(inventory['proposedLevel3Contracts'])} proposed Level 3 contracts selected "
        "below the 17 unresolved Level 2 fields. -/",
        "structure Level3ContractAssumptions : Prop where",
    ])
    for row in inventory["proposedLevel3Contracts"]:
        if row["field"] in DIRECT_PROOFS:
            continue
        lines.extend([f"  {row['field']} :", f"    {contract_name(row['field'])}"])
    lines.append("")

    parents = {row["field"]: row for row in inventory["parents"]}
    for field in inventory["level2ResolutionOrder"]:
        parent = parents[field]
        all_child_fields = unique([child["level3Field"] for child in parent["children"]
                                   if child["disposition"] == "level3-assumption"])
        child_fields = [field for field in all_child_fields if field not in DIRECT_PROOFS]
        siblings = unique([child["level2Field"] for child in parent["children"]
                           if child["disposition"] == "level2-sibling-dependency"])
        closed = unique([child["theorem"] for child in parent["children"]
                         if child["disposition"] == "unconditional-child-proof"] +
                        [DIRECT_PROOFS[field] for field in all_child_fields
                         if field in DIRECT_PROOFS])
        parent_composed = parent.get("parentComposedInlineInstances", [])
        lines.extend([
            "/--",
            *comments(
                f"Resolve Level 2 field `{field}` for `{parent['instanceId']}`.",
                f"Level 3 contracts: {lean_list(child_fields)}.",
                f"Earlier Level 2 results: {lean_list(siblings)}.",
                f"Unconditional child proofs: {lean_list(closed)}.",
                "Parent-composed inline instances: " + lean_list(
                    [row["instanceId"] for row in parent_composed]) + ".",
                f"Parent glue: {len(parent['gluePcs'])} instructions in "
                f"{len(parent['glueObligations'])} block fragments."),
        ])
        for row in parent_composed:
            lines.extend(comments(
                f"Inline `{row['instanceId']}` (`{row['qualified']}`) contributes "
                f"{len(row['executionPcs'])} scheduled instructions from "
                f"0x{row['executionPcs'][0]:x}. It is not a standalone machine region. "
                "Compose these instructions with the parent and reuse the shared integer-reader "
                "load, shift, OR, and `Seg` fragments."))
        for obligation in parent["glueObligations"]:
            guide = hints[obligation["id"]]
            strategy = guide["preferredStrategy"]
            composition = [row["api"]["name"] for row in strategy["composition"]]
            steps = [row["api"]["name"] for row in strategy["instructionSteps"]]
            closest = [theorem for row in guide["closestProvedCorridors"][:2]
                       for theorem in row["composingTheorems"]]
            lines.extend(comments(
                f"Fragment `0x{obligation['entryPc']:x}` ({obligation['instructionCount']} steps): "
                f"compose with {lean_list(composition)}. Step APIs: {lean_list(steps)}.",
                f"Motifs: {lean_list(guide['motifIds'])}. Closest proofs: "
                f"{lean_list(closest)}."))
        lines.extend([
            "Frame rule: choose the complete register and memory write regions before `Seg` starts.",
            "Frame rule: use `Seg.forget` before a later write replaces a recorded register value.",
            "-/",
            f"private theorem resolve_{field}",
        ])
        for child_field in child_fields:
            lines.append(
                f"    ({child_field} : {contract_name(child_field)})")
        for sibling in siblings:
            lines.append(f"    ({sibling} : {parent_type(sibling)})")
        if field in RESOLVED_PARENT_PROOFS:
            if child_fields or siblings:
                raise ValueError(f"resolved parent {field} still requires contract arguments")
            lines.extend([
                f"    : {parent_type(field)} :=",
                f"  {RESOLVED_PARENT_PROOFS[field]}",
                "",
            ])
        else:
            lines.extend([
                f"    : {parent_type(field)} := by",
                "  sorry",
                "",
            ])

    lines.extend([
        "/-- The staged Level 3 to Level 2 refinement edge. Production code does not import it. -/",
        "theorem level2Contracts_of_level3_staged",
        "    (hLevel3 : Level3ContractAssumptions) : Level2ContractAssumptions := by",
    ])
    available = {}
    for field in inventory["level2ResolutionOrder"]:
        parent = parents[field]
        siblings = unique([child["level2Field"] for child in parent["children"]
                           if child["disposition"] == "level2-sibling-dependency"])
        child_fields = unique([child["level3Field"] for child in parent["children"]
                               if child["disposition"] == "level3-assumption" and
                               child["level3Field"] not in DIRECT_PROOFS])
        args = [*(f"hLevel3.{child}" for child in child_fields),
                *(available[sibling] for sibling in siblings)]
        local = f"resolved_{field}"
        lines.extend([
            f"  have {local} : {parent_type(field)} :=",
            f"    resolve_{field}",
            *(f"      {arg}" for arg in args),
        ])
        available[field] = local
    lines.append("  exact {")
    for target in inventory["parents"]:
        lines.append(f"    {target['field']} := {available[target['field']]}")
    lines.extend(["  }", "", "end BinaryFv.Zesu.Staging.HLevel3", ""])
    return "\n".join(lines)


def idiom_checks(catalogue: dict) -> str:
    declarations = []
    for row in catalogue["idioms"]:
        if "declaration" not in row:
            continue
        if row["declaration"] not in declarations:
            declarations.append(row["declaration"])
    return "\n".join([
        "import BinaryFv.Zesu.MachineExecution.InstructionClassSteps",
        "import BinaryFv.Zesu.MachineExecution.MemcpyProof",
        "import BinaryFv.Zesu.MachineExecution.Level0MainSteps",
        "import BinaryFv.RiscV.Elfling.Seg",
        "import BinaryFv.Zesu.DecodedValue.Representation",
        "import BinaryFv.Option",
        "",
        "/-! Compile-time checks for declarations named by the hLevel3 guidance catalogue. -/",
        "",
        *[f"#check {name}" for name in declarations],
        "",
    ])


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("inventory", "guidance", "admission", "catalogue", "output", "idiom-output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    documents = [json.loads(getattr(args, name).read_text())
                 for name in ("inventory", "guidance", "admission", "catalogue")]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(generate(*documents))
    args.idiom_output.parent.mkdir(parents=True, exist_ok=True)
    args.idiom_output.write_text(idiom_checks(documents[-1]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
