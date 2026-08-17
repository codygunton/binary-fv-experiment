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
        if len(INPUTS) != 5:
            raise RuntimeError("expected DEPENDENCIES CFG FLAME LEVEL1 LEVEL2")
        module_path = Path(__file__).with_name("build_hlevel2_baseline.py")
        spec = importlib.util.spec_from_file_location("baseline", module_path)
        cls.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.module)
        cls.dependencies = Path(INPUTS[0])
        cls.documents = [json.loads(Path(path).read_text()) for path in INPUTS[1:]]

    def test_measured_boundary_geometry(self):
        result = self.module.build(self.dependencies, *self.documents)
        self.assertEqual(result["counts"]["transitiveProjectDeclarations"], 2223)
        self.assertEqual(result["counts"]["level0DirectRegionPcs"], 24)
        self.assertEqual(result["counts"]["conditionalLevel1DirectRegionPcs"], 209)
        self.assertEqual(result["counts"]["boundaryRegionUniquePcs"], 295)
        self.assertEqual(result["counts"]["unresolvedLevel2Contracts"], 17)
        self.assertEqual(result["coverage"]["directlyDischargedStepPcs"], [])

    def test_rejects_artifact_mismatch(self):
        documents = copy.deepcopy(self.documents)
        documents[3]["artifact"]["sha256"] = "forged"
        with self.assertRaisesRegex(ValueError, "different artifacts"):
            self.module.build(self.dependencies, *documents)

    def test_rejects_forged_pc(self):
        documents = copy.deepcopy(self.documents)
        documents[2]["instances"][0]["executionPcs"].append(0xDEADBEEF)
        with self.assertRaisesRegex(ValueError, "absent from the ELF"):
            self.module.build(self.dependencies, *documents)

    def test_rejects_incomplete_dependency_closure(self):
        lines = self.dependencies.read_text().splitlines()
        root = next(line for line in lines if line.startswith(
            "declaration\tBinaryFv.Zesu.root_compliance\t"))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "dependencies.tsv"
            path.write_text(root + "\n" + next(
                line for line in lines if line.startswith("edge\t")) + "\n")
            with self.assertRaisesRegex(ValueError, "escapes the declaration closure"):
                self.module.read_dependencies(path)


if __name__ == "__main__":
    unittest.main()
