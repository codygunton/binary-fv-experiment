import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parents[3] / "tools"))
from generate_elfling_program import function_instance_lean_name, function_instance_lean_names


def instance(qualified, *, specialization=(), inline_stack=()):
    return {
        "qualified": qualified,
        "specialization": list(specialization),
        "inlineStack": list(inline_stack),
    }


def frame(caller, line, column):
    return {"callerQualified": caller, "line": line, "column": column}


class FunctionInstanceLeanNameTests(unittest.TestCase):
    def test_emitted_name_uses_qualified_source_name(self):
        self.assertEqual(
            function_instance_lean_name(instance("raw_decoder_root.zesu_decode_raw")),
            "functionInstance_raw_decoder_root_zesu_decode_raw",
        )

    def test_inline_name_records_complete_call_path(self):
        value = instance(
            "ssz_raw.readU32",
            inline_stack=(
                frame("ssz_raw.decodeRaw", 199, 23),
                frame("ssz_raw.readOffset", 554, 32),
            ),
        )
        self.assertEqual(
            function_instance_lean_name(value),
            "functionInstance_ssz_raw_readU32_in_ssz_raw_decodeRaw_at_199_23_"
            "in_ssz_raw_readOffset_at_554_32",
        )

    def test_specialization_is_part_of_name(self):
        self.assertEqual(
            function_instance_lean_name(instance("ssz_raw.readArray", specialization=("32",))),
            "functionInstance_ssz_raw_readArray_specialized_32",
        )

    def test_collisions_fail_generation(self):
        duplicate = instance("ssz_raw.readU64")
        with self.assertRaisesRegex(SystemExit, "LEAN NAME COLLISION"):
            function_instance_lean_names([duplicate, duplicate])


if __name__ == "__main__":
    unittest.main()
