import BinaryFv.Zesu.Machine.Target

/-! # Generated fetch layer for Case F (rawAlloc/rawRemap prefix, n=4, 6 sites): 6 sites x 4 instructions

Emitted by `scratchpad/genfetch.py` for timing. Each instruction needs its own four
`native_decide`s, so this file is the unshareable cost of the motif at every one of its sites. -/

namespace BinaryFv.Zesu.Machine
open BinaryFv BinaryFv.Binary BinaryFv.RiscV BinaryFv.Zesu.Generated
open PreSail LeanRV64DExecutable.Functions Register

theorem f_0_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x358c) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x37 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x358c 0x83 0x37 0x06 0x00 l

theorem f_0_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3590) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x06 : UInt8).toNat) (BitVec.ofNat 8 (0x30 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3590 0x13 0x06 0x30 0x00 l

theorem f_0_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3594) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x05 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3594 0x93 0x05 0x07 0x00 l

theorem f_0_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3598) (BitVec.ofNat 8 (0xe7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x80 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3598 0xe7 0x80 0x07 0x00 l

theorem f_1_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3778) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x37 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3778 0x83 0x37 0x06 0x00 l

theorem f_1_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x377c) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x06 : UInt8).toNat) (BitVec.ofNat 8 (0x40 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x377c 0x13 0x06 0x40 0x00 l

theorem f_1_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3780) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x05 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3780 0x93 0x05 0x07 0x00 l

theorem f_1_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3784) (BitVec.ofNat 8 (0xe7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x80 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3784 0xe7 0x80 0x07 0x00 l

theorem f_2_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3c3c) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x37 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3c3c 0x03 0x37 0x07 0x00 l

theorem f_2_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3c40) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x05 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3c40 0x93 0x05 0x06 0x00 l

theorem f_2_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3c44) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x06 : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3c44 0x13 0x06 0x00 0x00 l

theorem f_2_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3c48) (BitVec.ofNat 8 (0xe7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3c48 0xe7 0x00 0x07 0x00 l

theorem f_3_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x36e8) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x38 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x36e8 0x03 0x38 0x07 0x01 l

theorem f_3_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x36ec) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0x84 : UInt8).toNat) (BitVec.ofNat 8 (0xb6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x02 : UInt8).toNat) :=
  fetchInstruction s 0x36ec 0xb3 0x84 0xb6 0x02 l

theorem f_3_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x36f0) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x06 : UInt8).toNat) (BitVec.ofNat 8 (0xb6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x02 : UInt8).toNat) :=
  fetchInstruction s 0x36f0 0x33 0x06 0xb6 0x02 l

theorem f_3_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x36f4) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x06 : UInt8).toNat) (BitVec.ofNat 8 (0x40 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x36f4 0x93 0x06 0x40 0x00 l

theorem f_4_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x38d4) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x38 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x38d4 0x03 0x38 0x07 0x01 l

theorem f_4_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x38d8) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0x84 : UInt8).toNat) (BitVec.ofNat 8 (0xb6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x02 : UInt8).toNat) :=
  fetchInstruction s 0x38d8 0xb3 0x84 0xb6 0x02 l

theorem f_4_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x38dc) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x06 : UInt8).toNat) (BitVec.ofNat 8 (0xb6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x02 : UInt8).toNat) :=
  fetchInstruction s 0x38dc 0x33 0x06 0xb6 0x02 l

theorem f_4_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x38e0) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x06 : UInt8).toNat) (BitVec.ofNat 8 (0x30 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x38e0 0x93 0x06 0x30 0x00 l

theorem f_5_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3b40) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x38 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x3b40 0x03 0x38 0x07 0x01 l

theorem f_5_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3b44) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x94 : UInt8).toNat) (BitVec.ofNat 8 (0x56 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3b44 0x93 0x94 0x56 0x00 l

theorem f_5_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3b48) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x16 : UInt8).toNat) (BitVec.ofNat 8 (0x56 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3b48 0x13 0x16 0x56 0x00 l

theorem f_5_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x3b4c) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x05 : UInt8).toNat) (BitVec.ofNat 8 (0x04 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x3b4c 0x93 0x05 0x04 0x00 l

end BinaryFv.Zesu.Machine
