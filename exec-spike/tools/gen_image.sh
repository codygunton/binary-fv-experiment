#!/bin/sh
# Regenerates ZesuExec/Image/{Gen,Cfg,Expected}.lean.
cd "$(dirname "$0")/.." && exec python3 tools/gen_image.py --elf /home/cody/zesislar/build/stock-zisk/zesu-zisk.elf \
  --sha256 e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95 --cfg /home/cody/zesislar/build/stock-zisk/cfg.json \
  --functions alt_fl_alloc.remap 'array_list.Aligned([32]u8,null).ensureTotalCapacity' rlp.decodeItem \
    rlp_decode.nextUint64 'array_list.Aligned([32]u8,null).toOwnedSlice' \
    'array_list.Aligned(input.AccessListEntry,null).toOwnedSlice' rlp_decode.decodeParentHeader \
    rlp_decode.txAccessList rlp_decode.decodeTxFields alt_fl_alloc.alloc alt_fl_alloc.free memcpy \
    memmove memset zkvm_sha256 ssz_output.sparseRoot ssz_output.progressiveRootAt \
  --rodata 0x801136d8:32 0x80114fb8:80 0x801152b0:16 0x80110050:40 0x8010fe00:8 0x801153e0:32 \
    0x801154c0:32 \
    0x80113728:32 0x80113748:32 0x80113768:32 0x80113788:32 0x801137a8:32 0x801137c8:32 \
    0x801137e8:32 0x80113808:32 0x80113828:32 0x80113848:32 0x80113868:32 0x80113888:32 \
    0x801138a8:32 0x801138c8:32 0x801138e8:32 0x80113908:32 0x80113928:32 0x80113948:32 \
    0x80113968:32 0x80113988:32 0x801139a8:32 0x801139c8:32 0x801139e8:32 0x80113a08:32 \
    0x80113a28:32 0x80113a48:32 --out ZesuExec/Image/Gen.lean
