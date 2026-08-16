"""Validate and expand the Level 2 contract-clause registry."""

from __future__ import annotations

from collections import Counter


SUPPORT_FIELDS = {
    "entry": {"declaration"},
    "proof": {"theorem"},
    "empirical": {"checker", "mutationTest"},
    "partial": {"checker", "mutationTest", "remaining"},
    "missing": {"remaining"},
    "contradiction": {"remaining"},
}


def expand(registry: dict, instance_names: set[str]) -> dict:
    if registry.get("schemaVersion") != 1 or not isinstance(registry.get("schemas"), dict):
        raise ValueError("invalid Level 2 clause registry schema")

    mapped: list[str] = []
    matrix: list[dict] = []
    schemas: list[dict] = []
    work: list[dict] = []
    for schema_name, schema in registry["schemas"].items():
        names = schema.get("instanceNames")
        clauses = schema.get("clauses")
        if not isinstance(names, list) or not names or not isinstance(clauses, list) or not clauses:
            raise ValueError(f"schema {schema_name} has no instances or clauses")
        mapped.extend(names)
        clause_ids = [clause.get("id") for clause in clauses]
        if None in clause_ids or len(clause_ids) != len(set(clause_ids)):
            raise ValueError(f"schema {schema_name} has missing or duplicate clause ids")

        kinds = []
        for clause in clauses:
            support = clause.get("support", {})
            kind = support.get("kind")
            required = SUPPORT_FIELDS.get(kind)
            if required is None or not required <= support.keys():
                raise ValueError(f"schema {schema_name} clause {clause['id']} has malformed support")
            kinds.append(kind)
            for instance in names:
                matrix.append({
                    "schema": schema_name,
                    "instance": instance,
                    "id": clause["id"],
                    "requirement": clause.get("requirement"),
                    "support": support,
                })
            if kind in {"partial", "missing", "contradiction"}:
                work.append({
                    "schema": schema_name, "clause": clause["id"],
                    "status": kind, "task": support["remaining"],
                })

        representative = schema.get("representativeProof")
        if representative is None:
            task = schema.get("representativeProofWork")
            if not task:
                raise ValueError(f"schema {schema_name} lacks representative proof work")
            work.append({"schema": schema_name, "clause": "representative-proof",
                         "status": "missing", "task": task})
        blocked = any(kind in {"missing", "contradiction"} for kind in kinds)
        schemas.append({
            "name": schema_name,
            "contractDeclaration": schema.get("contractDeclaration"),
            "instanceNames": names,
            "representativeProof": representative,
            "entryAndExecutionReady": not blocked,
            "evidenceComplete": all(kind not in {"partial", "missing", "contradiction"}
                                    for kind in kinds),
            "contractStatus": "not-admitted",
        })

    counts = Counter(mapped)
    duplicates = sorted(name for name, count in counts.items() if count != 1)
    missing = sorted(instance_names - set(mapped))
    extra = sorted(set(mapped) - instance_names)
    if duplicates or missing or extra:
        raise ValueError(
            f"clause registry does not cover exact inventory: duplicates={duplicates} "
            f"missing={missing} extra={extra}")
    support_counts = Counter(row["support"]["kind"] for row in matrix)
    return {
        "contractSchemas": schemas,
        "clauseMatrix": matrix,
        "workItems": work,
        "summary": {
            "instanceCount": len(instance_names),
            "schemaCount": len(schemas),
            "clauseCount": len(matrix),
            "supportCounts": dict(sorted(support_counts.items())),
            "admittedContractCount": 0,
        },
    }
