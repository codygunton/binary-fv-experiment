#!/usr/bin/env python3

from pathlib import Path
import sys
import tempfile
import time
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

    def test_orders_a_transitive_manifest_dependency(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("def a := 1\n")
            (root / "Bridge.lean").write_text("import A\n")
            (root / "C.lean").write_text("import Bridge\ndef c := a\n")
            manifest = root / "modules.tsv"
            manifest.write_text(
                f"A\t{root / 'A.lean'}\t{root / 'A.olean'}\n"
                f"C\t{root / 'C.lean'}\t{root / 'C.olean'}\n"
            )
            recorder = root / "recording-lean"
            recorder.write_text(
                "#!/usr/bin/env python3\n"
                "import pathlib, sys, time\n"
                "output = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])\n"
                "source = pathlib.Path(sys.argv[-1])\n"
                "events = output.parent / 'events'\n"
                "with events.open('a') as stream: stream.write(f'start {source.stem}\\n')\n"
                "if source.stem == 'A': time.sleep(0.1)\n"
                "if source.stem == 'C' and not (output.parent / 'A.olean').exists(): sys.exit(2)\n"
                "output.touch()\n"
                "with events.open('a') as stream: stream.write(f'end {source.stem}\\n')\n"
            )
            recorder.chmod(0o755)
            parallel_lean_build.build(
                manifest, 2, str(recorder), root / "logs", source_root=root
            )
            events = (root / "events").read_text().splitlines()
            self.assertLess(events.index("end A"), events.index("start C"))

    def test_stops_other_processes_after_a_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("def a := 1\n")
            (root / "B.lean").write_text("def b := 2\n")
            manifest = root / "modules.tsv"
            manifest.write_text(
                f"A\t{root / 'A.lean'}\t{root / 'A.olean'}\n"
                f"B\t{root / 'B.lean'}\t{root / 'B.olean'}\n"
            )
            recorder = root / "failing-lean"
            recorder.write_text(
                "#!/usr/bin/env python3\n"
                "import pathlib, sys, time\n"
                "source = pathlib.Path(sys.argv[-1])\n"
                "if source.stem == 'A': sys.exit(2)\n"
                "time.sleep(3)\n"
            )
            recorder.chmod(0o755)
            started = time.monotonic()
            with self.assertRaisesRegex(RuntimeError, "A failed"):
                parallel_lean_build.build(manifest, 2, str(recorder), root / "logs")
            self.assertLess(time.monotonic() - started, 1.0)


if __name__ == "__main__":
    unittest.main()
