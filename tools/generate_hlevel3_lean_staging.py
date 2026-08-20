#!/usr/bin/env python3
"""Generate typed, non-production Lean staging for the hLevel3 refinement."""

from __future__ import annotations

import argparse
import json
import textwrap
from pathlib import Path

DIRECT_PROOFS = {
    "mem_readInt_fi_1_2fa7":
        "BinaryFv.Zesu.Staging.proposed_memReadInt_proved",
}

DIRECT_CONTRACTS = {
    "mem_readInt_fi_1_2fa7":
        "BinaryFv.Zesu.Staging.Proposed_mem_readInt_fi_1_2fa7_Contract",
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


def read_u32_schema() -> list[str]:
    return [
        "/-- Arguments bound to one inlined `ssz.readU32` byte window. -/",
        "structure SszReadU32Args where",
        "  sourceAddress : Nat",
        "  sourceBytes : Array UInt8",
        "",
        "/-- The byte selected by an inlined `ssz.readU32` load. -/",
        "def sszReadU32Byte (bytes : Array UInt8) (index : Nat) : UInt8 :=",
        "  (bytes[index]?).getD 0",
        "",
        "/-- The four-byte little-endian result of `ssz.readU32`. -/",
        "def sszReadU32Value (bytes : Array UInt8) : Nat :=",
        "  (sszReadU32Byte bytes 0).toNat + 256 * (sszReadU32Byte bytes 1).toNat +",
        "    65536 * (sszReadU32Byte bytes 2).toNat +",
        "    16777216 * (sszReadU32Byte bytes 3).toNat",
        "",
        "/-- Registers unchanged by the four `lbu` instructions in `fi:1:3335`. -/",
        "def sszReadU32Preserved3335 (register : Register) : Prop :=",
        "  instructionPreserved register ∧ register ≠ x10 ∧ register ≠ x15 ∧",
        "    register ≠ x13 ∧ register ≠ x14",
        "",
        "/-- Registers unchanged by the four `lbu` instructions in `fi:1:33a1`. -/",
        "def sszReadU32Preserved33a1 (register : Register) : Prop :=",
        "  instructionPreserved register ∧ register ≠ x16 ∧ register ≠ x6 ∧",
        "    register ≠ x17 ∧ register ≠ x5",
        "",
        "/-- Entry bindings for the four production loads at one inlined `ssz.readU32`. -/",
        "def sszReadU32Entry (entry sourceOffset : Nat) (args : SszReadU32Args)",
        "    (state : EndpointState) : Prop :=",
        "  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧",
        "  state.machine.regs.get? x18 = some (BitVec.ofNat 64 args.sourceAddress) ∧",
        "  args.sourceBytes.size = 4 ∧",
        "  args.sourceAddress + sourceOffset + 4 ≤ 2 ^ 64 ∧",
        "  BytesRep state.machine.mem (args.sourceAddress + sourceOffset) args.sourceBytes ∧",
        "  (∀ index, index < 4 →",
        "    LoadPmaAllows state.machine",
        "      (BitVec.ofNat 64 (args.sourceAddress + sourceOffset + index)) 1) ∧",
        "  (∀ index, index < 4 →",
        "    LoadMMIOAddressExcluded",
        "      (BitVec.ofNat 64 (args.sourceAddress + sourceOffset + index)) 1) ∧",
        "  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧",
        "  ConfiguredMachinePre (fun pc => pcInList [entry, entry + 4, entry + 8, entry + 12] pc)",
        "    state.machine",
        "",
        "/-- Result and exact frame bindings after the final `lbu` at one inlined `ssz.readU32`. -/",
        "def sszReadU32Exit (bindBytes : Array UInt8 → EndpointState → Prop)",
        "    (preserved : Register → Prop) (args : SszReadU32Args) (result : Nat)",
        "    (before after : EndpointState) : Prop :=",
        "  result = sszReadU32Value args.sourceBytes ∧",
        "  bindBytes args.sourceBytes after ∧",
        "  Agree preserved before.machine after.machine ∧",
        "  RetiredCounterPresent after.machine ∧",
        "  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧",
        "  after.machine.mem = before.machine.mem ∧",
        "  EndpointMachineAuxAgree before.machine after.machine ∧",
        "  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧",
        "  after.stdout = before.stdout ∧ after.exitCode = before.exitCode",
        "",
        "/-- Shared relational contract schema for all reviewed inlined `ssz.readU32` instances. -/",
        "def sszReadU32Contract (entry sourceOffset : Nat)",
        "    (bindBytes : Array UInt8 → EndpointState → Prop) (preserved : Register → Prop)",
        "    (stepBound : SszReadU32Args → Nat) :",
        "    RelationalMachineContract EndpointState SszReadU32Args Nat :=",
        "  { allows := fun args result => args.sourceBytes.size = 4 ∧",
        "      result = sszReadU32Value args.sourceBytes",
        "    entry := sszReadU32Entry entry sourceOffset",
        "    exit := sszReadU32Exit bindBytes preserved",
        "    stepBound := stepBound }",
        "",
        "/-- Concrete result registers for `fi:1:3335`. -/",
        "def sszReadU32Bindings3335 (bytes : Array UInt8) (state : EndpointState) : Prop :=",
        "  state.machine.regs.get? x10 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 0).toNat) ∧",
        "  state.machine.regs.get? x15 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 1).toNat) ∧",
        "  state.machine.regs.get? x13 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 2).toNat) ∧",
        "  state.machine.regs.get? x14 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 3).toNat)",
        "",
        "/-- Concrete result registers for `fi:1:33a1`. -/",
        "def sszReadU32Bindings33a1 (bytes : Array UInt8) (state : EndpointState) : Prop :=",
        "  state.machine.regs.get? x16 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 0).toNat) ∧",
        "  state.machine.regs.get? x6 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 1).toNat) ∧",
        "  state.machine.regs.get? x17 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 2).toNat) ∧",
        "  state.machine.regs.get? x5 = some (BitVec.ofNat 64 (sszReadU32Byte bytes 3).toNat)",
        "",
    ]


def contract_body(field: str) -> list[str]:
    if field in DIRECT_PROOFS:
        return [f"  exact {DIRECT_CONTRACTS[field]}"]
    if field == "mem_writeInt_fi_1_45b2":
        return ["  exact BinaryFv.Zesu.Staging.Proposed_mem_writeInt_fi_1_45b2_Contract"]
    if field not in {"ssz_readU32_fi_1_3335", "ssz_readU32_fi_1_33a1"}:
        return ["  sorry"]
    if field == "ssz_readU32_fi_1_3335":
        return [
            "  exact ∃ stepBound : SszReadU32Args → Nat,",
            "    (∀ args, stepBound args < level2ContractFuel) ∧",
            "    (sszReadU32Contract 0x12c18 22 sszReadU32Bindings3335",
            "      sszReadU32Preserved3335 stepBound).Implements EndpointStep EndpointPc",
            "      (fun pc => pcInList [0x12c18, 0x12c1c, 0x12c20, 0x12c24] pc)",
            "      (fun pc => pcInList [0x12c28] pc)",
        ]
    return [
        "  exact ∃ stepBound : SszReadU32Args → Nat,",
        "    (∀ args, stepBound args < level2ContractFuel) ∧",
        "    (sszReadU32Contract 0x12ca4 58 sszReadU32Bindings33a1",
        "      sszReadU32Preserved33a1 stepBound).Implements EndpointStep EndpointPc",
        "      (fun pc => pcInList [0x12ca4, 0x12ca8, 0x12cac, 0x12cb0] pc)",
        "      (fun pc => pcInList [0x12cb4] pc)",
    ]


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
        *read_u32_schema(),
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
        "/-- The 58 proposed Level 3 contracts selected below the 17 unresolved Level 2 fields. -/",
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
        lines.extend([
            "/--",
            *comments(
                f"Resolve Level 2 field `{field}` for `{parent['instanceId']}`.",
                f"Level 3 contracts: {lean_list(child_fields)}.",
                f"Earlier Level 2 results: {lean_list(siblings)}.",
                f"Unconditional child proofs: {lean_list(closed)}.",
                f"Parent glue: {len(parent['gluePcs'])} instructions in "
                f"{len(parent['glueObligations'])} block fragments."),
        ])
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
