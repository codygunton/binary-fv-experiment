import unittest

from generate_zesu_cfg import normalize_source


class SourcePathNormalizationTests(unittest.TestCase):
    def test_sandbox_build_path(self) -> None:
        self.assertEqual(
            normalize_source("/build/source/src/stateless/stateless/ssz.zig"),
            "deps/zesu/src/stateless/stateless/ssz.zig",
        )

    def test_nonsandbox_build_path(self) -> None:
        self.assertEqual(
            normalize_source(
                "/tmp/nix-build-zesu-rv64im-object.drv-0/source/src/stateless/stateless/ssz.zig"
            ),
            "deps/zesu/src/stateless/stateless/ssz.zig",
        )

    def test_unrelated_source_path_is_unchanged(self) -> None:
        source = "/tmp/project/source/src/model.sail"
        self.assertEqual(normalize_source(source), source)


if __name__ == "__main__":
    unittest.main()
