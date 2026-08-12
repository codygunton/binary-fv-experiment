#!/usr/bin/env python3
"""Canonical identity of the memory image represented by an ELF file."""

from __future__ import annotations

import hashlib
import struct
from pathlib import Path

from elftools.elf.elffile import ELFFile


def load_image_sha256(path: Path) -> str:
    """Hash ordered PT_LOAD metadata and bytes, excluding non-runtime ELF metadata."""
    digest = hashlib.sha256()
    count = 0
    with path.open("rb") as stream:
        elf = ELFFile(stream)
        for segment in elf.iter_segments():
            if segment["p_type"] != "PT_LOAD":
                continue
            count += 1
            data = segment.data()
            if len(data) != segment["p_filesz"]:
                raise ValueError(f"load segment {count - 1} data length disagrees with p_filesz")
            digest.update(struct.pack(
                ">QQQQ",
                int(segment["p_vaddr"]),
                int(segment["p_filesz"]),
                int(segment["p_memsz"]),
                int(segment["p_flags"]),
            ))
            digest.update(data)
    if count == 0:
        raise ValueError("ELF has no loadable segments")
    return digest.hexdigest()
