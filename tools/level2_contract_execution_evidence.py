"""Evaluate measurable contract entry/exit clauses over complete production occurrences."""

from __future__ import annotations


def _region(spec: dict, registers: list[int], constants: dict, parameters: dict) -> dict:
    if "baseRegister" in spec:
        base = registers[spec["baseRegister"]]
    else:
        base = constants[spec["constant"]]
    offset = spec.get("offset", 0)
    if "negativeWidthParameter" in spec:
        offset -= parameters[spec["negativeWidthParameter"]]
    width = spec.get("width")
    if "widthRegister" in spec:
        width = registers[spec["widthRegister"]]
    if "widthParameter" in spec:
        width = parameters[spec["widthParameter"]]
    if width is None or width < 0 or base + offset < 0 or base + offset + width > 2 ** 64:
        raise ValueError(f"invalid observed region {spec.get('name', '<unnamed>')}")
    return {"name": spec.get("name", "region"), "start": base + offset, "width": width}


def _inside(region: dict, address: int, width: int) -> bool:
    return region["start"] <= address and address + width <= region["start"] + region["width"]


def evaluate_instance(name: str, schema: str, occurrences: list[dict], profiles: dict) -> dict:
    profile = profiles["schemas"][schema]
    parameters = profiles.get("instances", {}).get(name, {})
    constants = profiles["constants"]
    if not occurrences:
        raise ValueError(f"{name} has no complete entry-to-exit occurrence")
    reports = []
    for number, occurrence in enumerate(occurrences):
        before = occurrence["entryRegisters"]["values"]
        after_snapshot = occurrence.get("afterRegisters")
        if after_snapshot is None:
            raise ValueError(f"{name} occurrence {number} has no exit register snapshot")
        after = after_snapshot["values"]
        if occurrence.get("executedInstructionCount", 0) <= 0:
            raise ValueError(f"{name} occurrence {number} has an empty execution")

        alignment = profile.get("stackAlignment")
        if alignment is not None and before[2] % alignment:
            raise ValueError(f"{name} occurrence {number} has misaligned entry stack")
        frame_size = parameters.get("frameSize")
        if frame_size is not None and frame_size > before[2]:
            raise ValueError(f"{name} occurrence {number} child frame underflows")

        changed_preserved = [register for register in profile["preservedIntegerRegisters"]
                             if before[register] != after[register]]
        if changed_preserved:
            raise ValueError(
                f"{name} occurrence {number} changed preserved registers {changed_preserved}")

        region_specs = profile.get("allowedStoreRegions")
        regions = None if region_specs is None else [
            _region(spec, before, constants, parameters) for spec in region_specs
        ]
        stores = occurrence["memoryWrites"]
        if regions is not None:
            outside = [store for store in stores
                       if not any(_inside(region, store["address"], store["width"])
                                  for region in regions)]
            if outside:
                raise ValueError(
                    f"{name} occurrence {number} stores outside its declared frame: {outside[0]}")

        if profile.get("requireHostWrite") and not occurrence["hostWrites"]:
            raise ValueError(f"{name} occurrence {number} emitted no host write")
        if profile.get("requireStackRegionOutsideOutputContext"):
            stack_region = regions[0]
            output_regions = regions[1:]
            if any(not (stack_region["start"] + stack_region["width"] <= region["start"] or
                       region["start"] + region["width"] <= stack_region["start"])
                   for region in output_regions):
                raise ValueError(f"{name} occurrence {number} stack overlaps output context")

        source_spec = profile.get("sourceRegion")
        source = _region(source_spec, before, constants, parameters) if source_spec else None
        if source is not None and profile.get("requireSourceOutsideStores"):
            overlap = [store for store in stores if
                       not (store["address"] + store["width"] <= source["start"] or
                            source["start"] + source["width"] <= store["address"])]
            if overlap:
                raise ValueError(f"{name} occurrence {number} source overlaps a machine store")

        reports.append({
            "afterPc": occurrence["afterPc"],
            "executedInstructionCount": occurrence["executedInstructionCount"],
            "storeCount": len(stores),
            "preservedIntegerRegisters": profile["preservedIntegerRegisters"],
            "allowedStoreRegions": regions,
            "sourceRegion": source,
            "entryStackAlignment": alignment,
            "entryFrameSize": frame_size,
        })
    return {
        "status": "measured-compatible",
        "occurrenceCount": len(reports),
        "occurrences": reports,
        "unmeasured": profile.get("unmeasured", []) + [
            "universal path coverage", "universal step bound",
            "Sail platform-register and auxiliary-state frame",
        ],
    }


def evaluate_all(rows: list[dict], profiles: dict) -> dict[str, dict]:
    required = set(profiles["schemas"])
    actual = {row["contractSchema"] for row in rows}
    if actual != required:
        raise ValueError(f"execution profiles do not cover exact schemas: {actual} != {required}")
    reports = {}
    failures = []
    for row in rows:
        try:
            reports[row["leanName"]] = evaluate_instance(
                row["leanName"], row["contractSchema"], row["measured"]["occurrences"], profiles)
        except ValueError as error:
            failures.append(str(error))
    if failures:
        raise ValueError("incompatible Level 2 contract observations:\n" + "\n".join(failures))
    return reports
