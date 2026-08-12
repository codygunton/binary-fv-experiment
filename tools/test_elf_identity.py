#!/usr/bin/env python3

import shutil
import sys
import tempfile
import unittest
from pathlib import Path

from elftools.elf.elffile import ELFFile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from elf_identity import load_image_sha256


class LoadImageIdentityTest(unittest.TestCase):
    def test_ignores_non_loadable_metadata_but_rejects_loaded_byte_change(self) -> None:
        source = Path(sys.executable)
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "executable"
            shutil.copyfile(source, copied)
            original = load_image_sha256(copied)
            with copied.open("rb") as stream:
                elf = ELFFile(stream)
                segments = [segment for segment in elf.iter_segments()
                            if segment["p_type"] == "PT_LOAD"]
                loaded_offsets = {
                    offset
                    for segment in segments
                    for offset in range(int(segment["p_offset"]),
                                        int(segment["p_offset"] + segment["p_filesz"]))
                }
            raw = bytearray(copied.read_bytes())
            metadata_offset = next(offset for offset in range(len(raw) - 1, -1, -1)
                                   if offset not in loaded_offsets)
            raw[metadata_offset] ^= 1
            copied.write_bytes(raw)
            self.assertEqual(load_image_sha256(copied), original)

            loaded_offset = max(loaded_offsets)
            raw[loaded_offset] ^= 1
            copied.write_bytes(raw)
            self.assertNotEqual(load_image_sha256(copied), original)


if __name__ == "__main__":
    unittest.main()
