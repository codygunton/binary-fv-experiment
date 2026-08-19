#!/usr/bin/env python3

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import parallel_lean_build


class ParallelLeanBuildTest(unittest.TestCase):
    def test_reads_internal_dependencies(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("def a := 1\n")
            (root / "B.lean").write_text("import A\ndef b := a\n")
            manifest = root / "modules.tsv"
            manifest.write_text(
                f"A\t{root / 'A.lean'}\t{root / 'A.olean'}\n"
                f"B\t{root / 'B.lean'}\t{root / 'B.olean'}\t--tstack=1000\n"
            )
            modules = parallel_lean_build.read_manifest(manifest)
            self.assertEqual(parallel_lean_build.direct_imports(modules["B"][0]), {"A"})
            self.assertEqual(modules["B"][2], ("--tstack=1000",))

    def test_rejects_duplicate_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "modules.tsv"
            manifest.write_text("A\ta\tao\nA\tb\tbo\n")
            with self.assertRaisesRegex(ValueError, "duplicate module A"):
                parallel_lean_build.read_manifest(manifest)

    def test_reports_a_cycle(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("import B\n")
            (root / "B.lean").write_text("import A\n")
            manifest = root / "modules.tsv"
            manifest.write_text(
                f"A\t{root / 'A.lean'}\t{root / 'A.olean'}\n"
                f"B\t{root / 'B.lean'}\t{root / 'B.olean'}\n"
            )
            with self.assertRaisesRegex(RuntimeError, "dependency cycle"):
                parallel_lean_build.build(manifest, 2, "lean", root / "logs")


if __name__ == "__main__":
    unittest.main()
