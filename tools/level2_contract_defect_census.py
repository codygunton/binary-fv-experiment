#!/usr/bin/env python3
"""Measure proposed Level 2 contract defects against complete production occurrences."""

from __future__ import annotations

import argparse
import copy
import json
from collections import Counter
from pathlib import Path

from level2_contract_execution_evidence import evaluate_instance


def _selected(row: dict, audit: dict) -> bool:
    return (not audit.get("schemas") or row["contractSchema"] in audit["schemas"]) and \
        (not audit.get("instances") or row["leanName"] in audit["instances"])


def _mutated_profiles(base: dict, audit: dict, instance: str) -> dict:
    profiles = copy.deepcopy(base)
    keep = set(audit.get("keepAllowedStoreRegions", []))
    if keep:
        for schema in audit["schemas"]:
            regions = profiles["schemas"][schema]["allowedStoreRegions"]
            profiles["schemas"][schema]["allowedStoreRegions"] = [
                region for region in regions if region["name"] in keep]
    if audit.get("parameterOverrides"):
        profiles.setdefault("instances", {}).setdefault(instance, {}).update(
            audit["parameterOverrides"])
    return profiles


def build_census(admission: dict, profiles: dict, audit_config: dict) -> dict:
    rows = admission["instances"]
    results = []
    defect_count = Counter()
    for audit in audit_config["audits"]:
        affected = []
        caller_sites = set()
        for row in rows:
            if not _selected(row, audit):
                continue
            try:
                evaluate_instance(
                    row["leanName"], row["contractSchema"], row["measured"]["occurrences"],
                    _mutated_profiles(profiles, audit, row["leanName"]))
            except ValueError as error:
                message = str(error).splitlines()[0]
                if audit["expectedFailureContains"] not in message:
                    raise ValueError(f"{audit['id']} failed for an unexpected reason: {message}")
                affected.append({"leanName": row["leanName"],
                                 "contractSchema": row["contractSchema"]})
                defect_count[row["leanName"]] += 1
                identity = profiles["schemas"][row["contractSchema"]].get(
                    "callerSiteIdentity")
                if identity == "return-register-x1":
                    caller_sites.update(
                        f"return-pc:{occurrence['entryRegisters']['values'][1]:#x}"
                        for occurrence in row["measured"]["occurrences"])
                elif identity == "instance":
                    caller_sites.add(f"inline-instance:{row['leanName']}")
                else:
                    raise ValueError(
                        f"{row['contractSchema']} has no caller-site identity rule")
        if not affected:
            raise ValueError(f"{audit['id']} did not fail on production evidence")
        results.append({
            "id": audit["id"],
            "affectedInstanceCount": len(affected),
            "affectedInstances": affected,
            "observedCallerSiteCount": len(caller_sites),
            "observedCallerSites": sorted(caller_sites),
            "leanDeclarationCount": len(audit["leanDeclarations"]),
            "leanDeclarations": audit["leanDeclarations"],
        })
    failing = sorted(defect_count)
    return {
        "schemaVersion": 1,
        "totalInstanceCount": len(rows),
        "failingInstanceCount": len(failing),
        "failingInstances": failing,
        "defects": results,
        "instancesWithMultipleDefects": [
            {"leanName": name, "defectCount": count}
            for name, count in sorted(defect_count.items()) if count > 1
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("admission", type=Path)
    parser.add_argument("--profiles", type=Path, required=True)
    parser.add_argument("--audits", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    census = build_census(json.loads(args.admission.read_text()),
                          json.loads(args.profiles.read_text()),
                          json.loads(args.audits.read_text()))
    rendered = json.dumps(census, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
