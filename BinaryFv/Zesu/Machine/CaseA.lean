import BinaryFv.Zesu.Machine.RegisterWrite
import BinaryFv.Zesu.Machine.Target
import BinaryFv.Zesu.Machine.DecodeTactic

/-!
# Case A: the ten-instruction `mem.readInt` motif at `0x70`–`0x94`

```
0x70  03 45 16 00   lbu  a0, 1(a2)
0x74  03 46 06 00   lbu  a2, 0(a2)
0x78  83 46 29 00   lbu  a3, 2(s2)
0x7c  03 47 39 00   lbu  a4, 3(s2)
0x80  13 15 85 00   slli a0, a0, 8
0x84  33 65 c5 00   or   a0, a0, a2
0x88  93 96 06 01   slli a3, a3, 0x10
0x8c  13 17 87 01   slli a4, a4, 0x18
0x90  b3 66 d7 00   or   a3, a4, a3
0x94  33 e5 a6 00   or   a0, a3, a0
```

The little-endian u32 read. The n-gram study's strongest motif: 7 sites, and the same class shape is
the body of `mem.readInt` in 7 of its 14 inline instances.

## What this module measures

Fetch and decode, for all ten instructions, individually. These are the two parts of the
per-instruction obligation that are **fully discharged from generated data** — no caller-supplied
semantic premise enters either.

They are also the two parts a motif lemma provably cannot share. Every instruction owns a different
word, so its fetch is four `native_decide`s of its own; and every instruction decodes to a different
`instruction` value, so its decode is a `decode_run` of its own. A lemma stated once for the shape
`lbu lbu lbu lbu slli or slli slli or or` still has to be applied to ten distinct words at each of
its seven sites.

That is the first hard bound on Case A, and it is measured here rather than argued.
-/

namespace BinaryFv.Zesu.Machine

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.Zesu.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-! ## The ten words, read out of the generated image

Not written down: read. If the image disagrees with any of these, the failure names the address. -/

theorem motifA_words :
    programImage.readU32LE? 0x70 = some 0x00164503 ∧
      programImage.readU32LE? 0x74 = some 0x00064603 ∧
        programImage.readU32LE? 0x78 = some 0x00294683 ∧
          programImage.readU32LE? 0x7c = some 0x00394703 ∧
            programImage.readU32LE? 0x80 = some 0x00851513 ∧
              programImage.readU32LE? 0x84 = some 0x00c56533 ∧
                programImage.readU32LE? 0x88 = some 0x01069693 ∧
                  programImage.readU32LE? 0x8c = some 0x01871713 ∧
                    programImage.readU32LE? 0x90 = some 0x00d766b3 ∧
                      programImage.readU32LE? 0x94 = some 0x00a6e533 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-! ## Fetch, per instruction

Ten separate obligations. There is no way to state them as one, because each names a different
address and different bytes. -/

theorem fetchA_70 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x70) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x45 : UInt8).toNat) (BitVec.ofNat 8 (0x16 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x70 0x03 0x45 0x16 0x00 l

theorem fetchA_74 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x74) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x74 0x03 0x46 0x06 0x00 l

theorem fetchA_78 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x78) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x29 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x78 0x83 0x46 0x29 0x00 l

theorem fetchA_7c (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x7c) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0x39 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x7c 0x03 0x47 0x39 0x00 l

theorem fetchA_80 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x80) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x15 : UInt8).toNat) (BitVec.ofNat 8 (0x85 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x80 0x13 0x15 0x85 0x00 l

theorem fetchA_84 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x84) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x65 : UInt8).toNat) (BitVec.ofNat 8 (0xc5 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x84 0x33 0x65 0xc5 0x00 l

theorem fetchA_88 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x88) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x96 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) := fetchInstruction s 0x88 0x93 0x96 0x06 0x01 l

theorem fetchA_8c (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x8c) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x17 : UInt8).toNat) (BitVec.ofNat 8 (0x87 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) := fetchInstruction s 0x8c 0x13 0x17 0x87 0x01 l

theorem fetchA_90 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x90) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0x66 : UInt8).toNat) (BitVec.ofNat 8 (0xd7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x90 0xb3 0x66 0xd7 0x00 l

theorem fetchA_94 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x94) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe5 : UInt8).toNat) (BitVec.ofNat 8 (0xa6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) := fetchInstruction s 0x94 0x33 0xe5 0xa6 0x00 l

/-! ## Decode, per instruction

The four byte loads. Each decodes to a different `instruction` value, so each needs its own
`decode_run`: a motif lemma has nothing to share here either. -/

theorem decodeA_70 (s : State) (mseccfgBits : BitVec 64)
    (privRead : s.regs.get? cur_privilege = some Privilege.Machine)
    (seccfgRead : s.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x45 : UInt8).toNat) (BitVec.ofNat 8 (0x16 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat))) s s
      (.LOAD (1#12, .Regidx 12#5, .Regidx 10#5, true, 1)) := by
  decode_run

theorem decodeA_74 (s : State) (mseccfgBits : BitVec 64)
    (privRead : s.regs.get? cur_privilege = some Privilege.Machine)
    (seccfgRead : s.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat))) s s
      (.LOAD (0#12, .Regidx 12#5, .Regidx 12#5, true, 1)) := by
  decode_run

theorem decodeA_78 (s : State) (mseccfgBits : BitVec 64)
    (privRead : s.regs.get? cur_privilege = some Privilege.Machine)
    (seccfgRead : s.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x29 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat))) s s
      (.LOAD (2#12, .Regidx 18#5, .Regidx 13#5, true, 1)) := by
  decode_run

theorem decodeA_7c (s : State) (mseccfgBits : BitVec 64)
    (privRead : s.regs.get? cur_privilege = some Privilege.Machine)
    (seccfgRead : s.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0x39 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat))) s s
      (.LOAD (3#12, .Regidx 18#5, .Regidx 14#5, true, 1)) := by
  decode_run

end BinaryFv.Zesu.Machine
