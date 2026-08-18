#!/usr/bin/env python3
import copy
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

INPUTS = sys.argv[1:]
sys.argv[:] = sys.argv[:1]


class BaselineTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if len(INPUTS) != 6:
            raise RuntimeError("expected DEPENDENCIES SOURCE_ROOT CFG FLAME LEVEL1 LEVEL2")
        module_path = Path(__file__).with_name("build_hlevel2_baseline.py")
        spec = importlib.util.spec_from_file_location("baseline", module_path)
        cls.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.module)
        cls.dependencies = Path(INPUTS[0])
        cls.source_root = Path(INPUTS[1])
        cls.documents = [json.loads(Path(path).read_text()) for path in INPUTS[2:]]

    def test_measured_boundary_geometry(self):
        result = self.module.build(self.dependencies, self.source_root, *self.documents)
        self.assertGreater(result["counts"]["kernelSourceDeclarations"], 1000)
        self.assertEqual(result["counts"]["level0DirectRegionPcs"], 24)
        self.assertEqual(result["counts"]["conditionalLevel1DirectRegionPcs"], 209)
        self.assertEqual(result["counts"]["boundaryRegionUniquePcs"], 295)
        self.assertEqual(result["counts"]["unresolvedLevel2Contracts"], 17)
        self.assertEqual(len(result["coverage"]["directlyDischargedStepPcs"]), 157)
        self.assertEqual(result["counts"]["conditionalContractUniquePcs"], 6668)

    def test_every_dependency_has_a_rewrite_disposition(self):
        result = self.module.build(self.dependencies, self.source_root, *self.documents)
        self.assertEqual(result["counts"]["sourceDeclarations"],
                         len(result["declarations"]))
        self.assertGreater(result["counts"]["rewriteCandidates"], 0)
        self.assertTrue(all(row["rewriteDisposition"]["kind"] and
                            row["rewriteDisposition"]["reason"]
                            for row in result["declarations"]))
        memcpy = [row for row in result["declarations"]
                  if row["module"].endswith(".MemcpyProof")]
        self.assertTrue(memcpy)
        self.assertTrue(any(row["rewriteDisposition"]["rewriteCandidate"] for row in memcpy))

    def test_disposition_distinguishes_statements_classes_and_explicit_steps(self):
        classify = self.module.rewrite_disposition
        self.assertEqual(classify("BinaryFv.Zesu.Contracts.Machine", "structure C")["kind"],
                         "preserved_statement")
        self.assertEqual(classify("BinaryFv.Zesu.MachineExecution.Steps",
                                  "exact configuredRetStep")["kind"],
                         "instruction_class_consumer")
        self.assertEqual(classify("BinaryFv.Zesu.MachineExecution.Steps",
                                  "Runs (try_step n false) s t false")["kind"],
                         "unreviewed_exact_machine_step")

    def test_rejects_artifact_mismatch(self):
        documents = copy.deepcopy(self.documents)
        documents[3]["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "different artifacts"):
            self.module.build(self.dependencies, self.source_root, *documents)

    def test_rejects_forged_pc(self):
        documents = copy.deepcopy(self.documents)
        documents[2]["instances"][0]["executionPcs"].append(0xDEADBEEF)
        with self.assertRaisesRegex(ValueError, "absent from the ELF"):
            self.module.build(self.dependencies, self.source_root, *documents)

    def test_rejects_incomplete_dependency_closure(self):
        lines = self.dependencies.read_text().splitlines()
        root = next(line for line in lines if line.startswith(
            "declaration\tBinaryFv.Zesu.root_compliance\t"))
        memcpy = next(line for line in lines if line.startswith(
            "declaration\tBinaryFv.Zesu.MachineExecution.memcpyInstanceContract\t"))
        escaping = next(line for line in lines if line.startswith("edge\t") and
                        "BinaryFv.Zesu.root_compliance" not in line and
                        "BinaryFv.Zesu.MachineExecution.memcpyInstanceContract" not in line)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "dependencies.tsv"
            path.write_text(root + "\n" + memcpy + "\n" + escaping + "\n")
            with self.assertRaisesRegex(ValueError, "escapes the declaration closure"):
                self.module.read_dependencies(path)

    def test_rejects_private_anchor_hiding_memcpy_proof(self):
        lines = [line for line in self.dependencies.read_text().splitlines()
                 if "BinaryFv.Zesu.MachineExecution.memcpyInstanceContract" not in line]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "dependencies.tsv"
            path.write_text("\n".join(lines) + "\n")
            with self.assertRaisesRegex(ValueError, "omits required proof dependencies"):
                self.module.read_dependencies(path)

    def test_rejects_omitted_and_forged_direct_pcs(self):
        elf_pcs = {instruction["pc"] for function in self.documents[0]["functions"]
                   for block in function["blocks"] for instruction in block["instructions"]}
        with self.assertRaisesRegex(ValueError, "omitted PCs"):
            self.module.validate_direct_pcs(set(range(156)), elf_pcs)
        forged = set(range(156)) | {0xDEADBEEF}
        with self.assertRaisesRegex(ValueError, "forged PCs"):
            self.module.validate_direct_pcs(forged, elf_pcs)


if __name__ == "__main__":
    unittest.main()
