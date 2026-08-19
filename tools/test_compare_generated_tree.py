import tempfile
import unittest
from pathlib import Path

from compare_generated_tree import differences


class CompareGeneratedTreeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        root = Path(self.temporary.name)
        self.expected = root / "expected"
        self.actual = root / "actual"
        self.expected.mkdir()
        self.actual.mkdir()
        (self.expected / "Model.lean").write_text("def value := 1\n")
        (self.actual / "Model.lean").write_text("def value := 1\n")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_equal_trees_pass(self) -> None:
        self.assertEqual(differences(self.expected, self.actual), [])

    def test_missing_file_fails(self) -> None:
        (self.actual / "Model.lean").unlink()
        self.assertEqual(differences(self.expected, self.actual), ["missing: Model.lean"])

    def test_changed_file_fails(self) -> None:
        (self.actual / "Model.lean").write_text("def value := 2\n")
        self.assertEqual(differences(self.expected, self.actual), ["changed: Model.lean"])

    def test_extra_file_fails(self) -> None:
        (self.actual / "Extra.lean").write_text("def extra := true\n")
        self.assertEqual(differences(self.expected, self.actual), ["extra: Extra.lean"])

    def test_build_outputs_are_ignored(self) -> None:
        build = self.actual / ".lake" / "build"
        build.mkdir(parents=True)
        (build / "Model.olean").write_bytes(b"compiled")
        self.assertEqual(differences(self.expected, self.actual), [])

    def test_requested_existential_normalization_accepts_renaming(self) -> None:
        (self.expected / "Model.lean").write_text("fun (k_ex611634_ : Nat) => k_ex611634_\n")
        (self.actual / "Model.lean").write_text("fun (k_ex611624_ : Nat) => k_ex611624_\n")
        self.assertNotEqual(differences(self.expected, self.actual), [])
        self.assertEqual(differences(self.expected, self.actual, True), [])

    def test_existential_normalization_keeps_semantic_changes(self) -> None:
        (self.expected / "Model.lean").write_text("fun (k_ex1_ : Nat) => k_ex1_ + 1\n")
        (self.actual / "Model.lean").write_text("fun (k_ex9_ : Nat) => k_ex9_ + 2\n")
        self.assertNotEqual(differences(self.expected, self.actual, True), [])


if __name__ == "__main__":
    unittest.main()
