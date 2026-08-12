import BinaryFv.Zesu.Machine.Target

/-! # Generated fetch layer for Case A (mem.readInt, n=10, 7 sites): 7 sites x 10 instructions

Emitted by `scratchpad/genfetch.py` for timing. Each instruction needs its own four
`native_decide`s, so this file is the unshareable cost of the motif at every one of its sites. -/

namespace BinaryFv.Zesu.Machine
open BinaryFv BinaryFv.Binary BinaryFv.RiscV BinaryFv.Zesu.Generated
open PreSail LeanRV64DExecutable.Functions Register

theorem f_0_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x70) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x45 : UInt8).toNat) (BitVec.ofNat 8 (0x16 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x70 0x03 0x45 0x16 0x00 l

theorem f_0_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x74) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x74 0x03 0x46 0x06 0x00 l

theorem f_0_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x78) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x29 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x78 0x83 0x46 0x29 0x00 l

theorem f_0_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x7c) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0x39 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x7c 0x03 0x47 0x39 0x00 l

theorem f_0_4 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x80) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x15 : UInt8).toNat) (BitVec.ofNat 8 (0x85 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x80 0x13 0x15 0x85 0x00 l

theorem f_0_5 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x84) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x65 : UInt8).toNat) (BitVec.ofNat 8 (0xc5 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x84 0x33 0x65 0xc5 0x00 l

theorem f_0_6 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x88) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x96 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x88 0x93 0x96 0x06 0x01 l

theorem f_0_7 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x8c) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x17 : UInt8).toNat) (BitVec.ofNat 8 (0x87 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x8c 0x13 0x17 0x87 0x01 l

theorem f_0_8 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x90) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0x66 : UInt8).toNat) (BitVec.ofNat 8 (0xd7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x90 0xb3 0x66 0xd7 0x00 l

theorem f_0_9 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x94) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe5 : UInt8).toNat) (BitVec.ofNat 8 (0xa6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x94 0x33 0xe5 0xa6 0x00 l

theorem f_1_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0xfc) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x48 : UInt8).toNat) (BitVec.ofNat 8 (0x16 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0xfc 0x03 0x48 0x16 0x00 l

theorem f_1_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x100) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x48 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x100 0x83 0x48 0x06 0x00 l

theorem f_1_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x104) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x42 : UInt8).toNat) (BitVec.ofNat 8 (0x26 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x104 0x83 0x42 0x26 0x00 l

theorem f_1_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x108) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x43 : UInt8).toNat) (BitVec.ofNat 8 (0x36 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x108 0x03 0x43 0x36 0x00 l

theorem f_1_4 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x10c) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x18 : UInt8).toNat) (BitVec.ofNat 8 (0x88 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x10c 0x13 0x18 0x88 0x00 l

theorem f_1_5 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x110) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x68 : UInt8).toNat) (BitVec.ofNat 8 (0x18 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x110 0x33 0x68 0x18 0x01 l

theorem f_1_6 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x114) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x92 : UInt8).toNat) (BitVec.ofNat 8 (0x02 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x114 0x93 0x92 0x02 0x01 l

theorem f_1_7 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x118) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x13 : UInt8).toNat) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x118 0x13 0x13 0x83 0x01 l

theorem f_1_8 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x11c) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0x68 : UInt8).toNat) (BitVec.ofNat 8 (0x53 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x11c 0xb3 0x68 0x53 0x00 l

theorem f_1_9 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x120) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe8 : UInt8).toNat) (BitVec.ofNat 8 (0x08 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x120 0x33 0xe8 0x08 0x01 l

theorem f_2_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fcc) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x45 : UInt8).toNat) (BitVec.ofNat 8 (0x1a : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1fcc 0x03 0x45 0x1a 0x00 l

theorem f_2_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fd0) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x45 : UInt8).toNat) (BitVec.ofNat 8 (0x0a : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1fd0 0x83 0x45 0x0a 0x00 l

theorem f_2_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fd4) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x2a : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1fd4 0x03 0x46 0x2a 0x00 l

theorem f_2_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fd8) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x3a : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1fd8 0x83 0x46 0x3a 0x00 l

theorem f_2_4 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fdc) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x15 : UInt8).toNat) (BitVec.ofNat 8 (0x85 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1fdc 0x13 0x15 0x85 0x00 l

theorem f_2_5 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fe0) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x65 : UInt8).toNat) (BitVec.ofNat 8 (0xb5 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1fe0 0x33 0x65 0xb5 0x00 l

theorem f_2_6 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fe4) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x16 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x1fe4 0x13 0x16 0x06 0x01 l

theorem f_2_7 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fe8) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x96 : UInt8).toNat) (BitVec.ofNat 8 (0x86 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x1fe8 0x93 0x96 0x86 0x01 l

theorem f_2_8 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1fec) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe6 : UInt8).toNat) (BitVec.ofNat 8 (0xc6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1fec 0x33 0xe6 0xc6 0x00 l

theorem f_2_9 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x1ff0) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x66 : UInt8).toNat) (BitVec.ofNat 8 (0xa6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x1ff0 0x33 0x66 0xa6 0x00 l

theorem f_3_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2130) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x95 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2130 0x03 0x46 0x95 0x00 l

theorem f_3_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2134) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x85 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2134 0x83 0x46 0x85 0x00 l

theorem f_3_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2138) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0xa5 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2138 0x03 0x47 0xa5 0x00 l

theorem f_3_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x213c) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0xb5 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x213c 0x83 0x47 0xb5 0x00 l

theorem f_3_4 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2140) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x16 : UInt8).toNat) (BitVec.ofNat 8 (0x86 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2140 0x13 0x16 0x86 0x00 l

theorem f_3_5 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2144) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x66 : UInt8).toNat) (BitVec.ofNat 8 (0xd6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2144 0x33 0x66 0xd6 0x00 l

theorem f_3_6 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2148) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x17 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x2148 0x13 0x17 0x07 0x01 l

theorem f_3_7 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x214c) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x97 : UInt8).toNat) (BitVec.ofNat 8 (0x87 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x214c 0x93 0x97 0x87 0x01 l

theorem f_3_8 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2150) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0xe7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2150 0x33 0xe7 0xe7 0x00 l

theorem f_3_9 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2154) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x66 : UInt8).toNat) (BitVec.ofNat 8 (0xc7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2154 0x33 0x66 0xc7 0x00 l

theorem f_4_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2338) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x45 : UInt8).toNat) (BitVec.ofNat 8 (0x1c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2338 0x83 0x45 0x1c 0x00 l

theorem f_4_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x233c) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x0c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x233c 0x03 0x46 0x0c 0x00 l

theorem f_4_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2340) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x2c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2340 0x83 0x46 0x2c 0x00 l

theorem f_4_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2344) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0x3c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2344 0x03 0x47 0x3c 0x00 l

theorem f_4_4 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2348) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x95 : UInt8).toNat) (BitVec.ofNat 8 (0x85 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2348 0x93 0x95 0x85 0x00 l

theorem f_4_5 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x234c) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe5 : UInt8).toNat) (BitVec.ofNat 8 (0xc5 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x234c 0xb3 0xe5 0xc5 0x00 l

theorem f_4_6 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2350) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x96 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x2350 0x93 0x96 0x06 0x01 l

theorem f_4_7 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2354) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x17 : UInt8).toNat) (BitVec.ofNat 8 (0x87 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x2354 0x13 0x17 0x87 0x01 l

theorem f_4_8 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2358) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0x66 : UInt8).toNat) (BitVec.ofNat 8 (0xd7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2358 0xb3 0x66 0xd7 0x00 l

theorem f_4_9 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x235c) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe5 : UInt8).toNat) (BitVec.ofNat 8 (0xb6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x235c 0xb3 0xe5 0xb6 0x00 l

theorem f_5_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x238c) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0x1c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x238c 0x03 0x47 0x1c 0x00 l

theorem f_5_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2390) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0x0c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2390 0x83 0x47 0x0c 0x00 l

theorem f_5_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2394) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x48 : UInt8).toNat) (BitVec.ofNat 8 (0x2c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2394 0x03 0x48 0x2c 0x00 l

theorem f_5_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2398) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x48 : UInt8).toNat) (BitVec.ofNat 8 (0x3c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2398 0x83 0x48 0x3c 0x00 l

theorem f_5_4 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x239c) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x17 : UInt8).toNat) (BitVec.ofNat 8 (0x87 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x239c 0x13 0x17 0x87 0x00 l

theorem f_5_5 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x23a0) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x67 : UInt8).toNat) (BitVec.ofNat 8 (0xf7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x23a0 0x33 0x67 0xf7 0x00 l

theorem f_5_6 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x23a4) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x0c : UInt8).toNat) (BitVec.ofNat 8 (0x4c : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x23a4 0x13 0x0c 0x4c 0x00 l

theorem f_5_7 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x23a8) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x18 : UInt8).toNat) (BitVec.ofNat 8 (0x08 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x23a8 0x13 0x18 0x08 0x01 l

theorem f_5_8 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x23ac) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x98 : UInt8).toNat) (BitVec.ofNat 8 (0x88 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x23ac 0x93 0x98 0x88 0x01 l

theorem f_5_9 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x23b0) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0x08 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x23b0 0xb3 0xe7 0x08 0x01 l

theorem f_6_0 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b24) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x45 : UInt8).toNat) (BitVec.ofNat 8 (0x17 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b24 0x03 0x45 0x17 0x00 l

theorem f_6_1 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b28) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x07 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b28 0x03 0x46 0x07 0x00 l

theorem f_6_2 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b2c) (BitVec.ofNat 8 (0x83 : UInt8).toNat)
      (BitVec.ofNat 8 (0x46 : UInt8).toNat) (BitVec.ofNat 8 (0x27 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b2c 0x83 0x46 0x27 0x00 l

theorem f_6_3 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b30) (BitVec.ofNat 8 (0x03 : UInt8).toNat)
      (BitVec.ofNat 8 (0x47 : UInt8).toNat) (BitVec.ofNat 8 (0x37 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b30 0x03 0x47 0x37 0x00 l

theorem f_6_4 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b34) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x15 : UInt8).toNat) (BitVec.ofNat 8 (0x85 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b34 0x13 0x15 0x85 0x00 l

theorem f_6_5 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b38) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0x65 : UInt8).toNat) (BitVec.ofNat 8 (0xc5 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b38 0x33 0x65 0xc5 0x00 l

theorem f_6_6 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b3c) (BitVec.ofNat 8 (0x93 : UInt8).toNat)
      (BitVec.ofNat 8 (0x96 : UInt8).toNat) (BitVec.ofNat 8 (0x06 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x2b3c 0x93 0x96 0x06 0x01 l

theorem f_6_7 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b40) (BitVec.ofNat 8 (0x13 : UInt8).toNat)
      (BitVec.ofNat 8 (0x17 : UInt8).toNat) (BitVec.ofNat 8 (0x87 : UInt8).toNat)
      (BitVec.ofNat 8 (0x01 : UInt8).toNat) :=
  fetchInstruction s 0x2b40 0x13 0x17 0x87 0x01 l

theorem f_6_8 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b44) (BitVec.ofNat 8 (0xb3 : UInt8).toNat)
      (BitVec.ofNat 8 (0x66 : UInt8).toNat) (BitVec.ofNat 8 (0xd7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b44 0xb3 0x66 0xd7 0x00 l

theorem f_6_9 (s : State) (l : programImage.matchesMemory s.mem) :
    FetchBytesAt s (BitVec.ofNat 64 0x2b48) (BitVec.ofNat 8 (0x33 : UInt8).toNat)
      (BitVec.ofNat 8 (0xe5 : UInt8).toNat) (BitVec.ofNat 8 (0xa6 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction s 0x2b48 0x33 0xe5 0xa6 0x00 l

end BinaryFv.Zesu.Machine
