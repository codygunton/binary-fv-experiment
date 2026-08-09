import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parents[3] / "tools"))
from generate_elfling_program import (
    excluded_function_instance_lean_name,
    excluded_function_instance_lean_names,
    function_instance_lean_name,
    function_instance_lean_names,
    select_entry_formal_binding_witnesses,
    select_paramless_entry_local_witnesses,
)


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


class ExcludedFunctionInstanceLeanNameTests(unittest.TestCase):
    def test_name_uses_excluded_source_identity(self):
        self.assertEqual(
            excluded_function_instance_lean_name({"qualified": "ssz_raw.RawExecutionWitness.deinit"}),
            "excludedFunctionInstance_ssz_raw_RawExecutionWitness_deinit",
        )

    def test_collisions_fail_generation(self):
        duplicate = {"qualified": "ssz_raw.RawExecutionWitness.deinit"}
        with self.assertRaisesRegex(SystemExit, "EXCLUDED LEAN NAME COLLISION"):
            excluded_function_instance_lean_names([duplicate, duplicate])


class ParamlessEntryLocalWitnessTests(unittest.TestCase):
    def target(self, *, bindings=(), locals=(("result", "fbreg", 8, 2320),)):
        return {
            **instance(
                "ssz_raw.decodeNewPayloadRequest",
                inline_stack=(frame("ssz_raw.decodeRaw", 207, 61),),
            ),
            "bindings": list(bindings),
            "entryLocals": list(locals),
            "entryPc": 67084,
        }

    def test_selects_result_by_complete_source_identity(self):
        [witness] = select_paramless_entry_local_witnesses([self.target()])
        self.assertEqual((witness["name"], witness["kind"], witness["reg"], witness["offset"]),
                         ("result", "fbreg", 8, 2320))

    def test_rejects_a_source_abi_substitute(self):
        with self.assertRaisesRegex(SystemExit, "formal bindings"):
            select_paramless_entry_local_witnesses([
                self.target(bindings=(("data", "reg", 10, 0),)),
            ])

    def test_rejects_an_unlocated_result(self):
        with self.assertRaisesRegex(SystemExit, "exactly one entry location"):
            select_paramless_entry_local_witnesses([self.target(locals=())])


class EntryFormalBindingWitnessTests(unittest.TestCase):
    def target(self, *, bindings=(("alloc", "breg", 11, 0),)):
        return {
            **instance("ssz_raw.decodeRaw"),
            "bindings": list(bindings),
            "entryPc": 66628,
        }

    def test_selects_alloc_by_emitted_source_identity(self):
        [witness] = select_entry_formal_binding_witnesses([self.target()])
        self.assertEqual((witness["name"], witness["kind"], witness["reg"], witness["offset"]),
                         ("alloc", "breg", 11, 0))

    def test_rejects_a_recovered_or_missing_raw_binding(self):
        with self.assertRaisesRegex(SystemExit, "raw DWARF binding"):
            select_entry_formal_binding_witnesses([self.target(bindings=())])

    def test_rejects_an_unlocated_raw_binding(self):
        with self.assertRaisesRegex(SystemExit, "no machine location"):
            select_entry_formal_binding_witnesses([
                self.target(bindings=(("alloc", "callerProvided", -1, 0),)),
            ])


if __name__ == "__main__":
    unittest.main()
