import BinaryFv.Zesu.MachineExecution.HLevel3ReadU32Steps

/-!
# Shared steps for inlined `ssz.readU64`

The production decoder contains two complete 24-instruction schedules and six split schedules.
This file defines their common value and frame before any concrete `Seg` composition starts.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def readU64MachineValue (v0 v1 v2 v3 v4 v5 v6 v7 : Nat) : BitVec 64 :=
  let z0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v0)
  let z1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v1)
  let z2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v2)
  let z3 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v3)
  let z4 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v4)
  let z5 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v5)
  let z6 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v6)
  let z7 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v7)
  let low :=
    ((Sail.shift_bits_left z3 24#64) ||| (Sail.shift_bits_left z2 16#64)) |||
      ((Sail.shift_bits_left z1 8#64) ||| z0)
  let high :=
    ((Sail.shift_bits_left z7 24#64) ||| (Sail.shift_bits_left z6 16#64)) |||
      ((Sail.shift_bits_left z5 8#64) ||| z4)
  (Sail.shift_bits_left high 32#64) ||| low

def standardReadU64OwnPc (start : Nat) (pc : BitVec 64) : Prop :=
  pcInList (List.range 24 |>.map fun index => start + 4 * index) pc

def standardReadU64ExitPc (start : Nat) (pc : BitVec 64) : Prop :=
  pcInList [start + 96] pc

def standardReadU64Writes (r0 r1 r2 r3 r4 r5 : Register) (register : Register) : Prop :=
  stepBookkeeping register ∨ register = r0 ∨ register = r1 ∨ register = r2 ∨
    register = r3 ∨ register = r4 ∨ register = r5

theorem standardReadU64InstructionDisjoint (r0 r1 r2 r3 r4 r5 : Register)
    (h0 : ¬instructionPreserved r0) (h1 : ¬instructionPreserved r1)
    (h2 : ¬instructionPreserved r2) (h3 : ¬instructionPreserved r3)
    (h4 : ¬instructionPreserved r4) (h5 : ¬instructionPreserved r5) :
    RegSet.Disjoint instructionPreserved (standardReadU64Writes r0 r1 r2 r3 r4 r5) := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 writes
  · exact h0 preserved
  · exact h1 preserved
  · exact h2 preserved
  · exact h3 preserved
  · exact h4 preserved
  · exact h5 preserved

theorem standardReadU64PlatformDisjoint (r0 r1 r2 r3 r4 r5 : Register)
    (h0 : ¬platformPreserved r0) (h1 : ¬platformPreserved r1)
    (h2 : ¬platformPreserved r2) (h3 : ¬platformPreserved r3)
    (h4 : ¬platformPreserved r4) (h5 : ¬platformPreserved r5) :
    RegSet.Disjoint platformPreserved (standardReadU64Writes r0 r1 r2 r3 r4 r5) := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved writes
  · exact h0 preserved
  · exact h1 preserved
  · exact h2 preserved
  · exact h3 preserved
  · exact h4 preserved
  · exact h5 preserved

/-! ## Exact site data for the two complete schedules -/

def readU64_3203OwnPc (pc : BitVec 64) : Prop := standardReadU64OwnPc 0x12a4c pc
def readU64_3203ExitPc (pc : BitVec 64) : Prop := standardReadU64ExitPc 0x12a4c pc
def readU64_3203Writes (register : Register) : Prop :=
  standardReadU64Writes x5 x6 x7 x16 x17 x28 register

private theorem readU64_3203InstructionDisjoint :
    RegSet.Disjoint instructionPreserved readU64_3203Writes :=
  standardReadU64InstructionDisjoint x5 x6 x7 x16 x17 x28
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])

private theorem readU64_3203PlatformDisjoint :
    RegSet.Disjoint platformPreserved readU64_3203Writes :=
  standardReadU64PlatformDisjoint x5 x6 x7 x16 x17 x28
    (by simp [platformPreserved]) (by simp [platformPreserved])
    (by simp [platformPreserved]) (by simp [platformPreserved])
    (by simp [platformPreserved]) (by simp [platformPreserved])

readU32UnsignedLoadSite(readU64_3203Load1; 0x12a50, 1;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 17#5, x17, wX_x17_run;
  0x83, 0x48, 0x18, 0x00)
readU32UnsignedLoadSite(readU64_3203Load2; 0x12a54, 2;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 5#5, x5, wX_x5_run;
  0x83, 0x42, 0x28, 0x00)
readU32UnsignedLoadSite(readU64_3203Load3; 0x12a58, 3;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 6#5, x6, wX_x6_run;
  0x03, 0x43, 0x38, 0x00)
readU32UnsignedLoadSite(readU64_3203Load0; 0x12a5c, 0;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 7#5, x7, wX_x7_run;
  0x83, 0x43, 0x08, 0x00)
readU32SlliSite(readU64_3203Shift1; 0x12a60, 8;
  .Regidx 17#5, x17, rX_x17_run, wX_x17_run; 0x93, 0x98, 0x88, 0x00)
readU32SlliSite(readU64_3203Shift2; 0x12a64, 16;
  .Regidx 5#5, x5, rX_x5_run, wX_x5_run; 0x93, 0x92, 0x02, 0x01)
readU32SlliSite(readU64_3203Shift3; 0x12a68, 24;
  .Regidx 6#5, x6, rX_x6_run, wX_x6_run; 0x13, 0x13, 0x83, 0x01)
readU32OrSite(readU64_3203OrLow0; 0x12a6c;
  .Regidx 17#5, x17, rX_x17_run; .Regidx 7#5, x7, rX_x7_run;
  .Regidx 17#5, x17, wX_x17_run; 0xb3, 0xe8, 0x78, 0x00)
readU32OrSite(readU64_3203OrLow1; 0x12a70;
  .Regidx 6#5, x6, rX_x6_run; .Regidx 5#5, x5, rX_x5_run;
  .Regidx 5#5, x5, wX_x5_run; 0xb3, 0x62, 0x53, 0x00)
readU32UnsignedLoadSite(readU64_3203Load5; 0x12a74, 5;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 6#5, x6, wX_x6_run;
  0x03, 0x43, 0x58, 0x00)
readU32UnsignedLoadSite(readU64_3203Load4; 0x12a78, 4;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 7#5, x7, wX_x7_run;
  0x83, 0x43, 0x48, 0x00)
readU32UnsignedLoadSite(readU64_3203Load6; 0x12a7c, 6;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 28#5, x28, wX_x28_run;
  0x03, 0x4e, 0x68, 0x00)
readU32UnsignedLoadSite(readU64_3203Load7; 0x12a80, 7;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 16#5, x16, wX_x16_run;
  0x03, 0x48, 0x78, 0x00)
readU32SlliSite(readU64_3203Shift5; 0x12a84, 8;
  .Regidx 6#5, x6, rX_x6_run, wX_x6_run; 0x13, 0x13, 0x83, 0x00)
readU32OrSite(readU64_3203OrHigh0; 0x12a88;
  .Regidx 6#5, x6, rX_x6_run; .Regidx 7#5, x7, rX_x7_run;
  .Regidx 6#5, x6, wX_x6_run; 0x33, 0x63, 0x73, 0x00)
readU32SlliSite(readU64_3203Shift6; 0x12a8c, 16;
  .Regidx 28#5, x28, rX_x28_run, wX_x28_run; 0x13, 0x1e, 0x0e, 0x01)
readU32SlliSite(readU64_3203Shift7; 0x12a90, 24;
  .Regidx 16#5, x16, rX_x16_run, wX_x16_run; 0x13, 0x18, 0x88, 0x01)
readU32OrSite(readU64_3203OrHigh1; 0x12a94;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 28#5, x28, rX_x28_run;
  .Regidx 16#5, x16, wX_x16_run; 0x33, 0x68, 0xc8, 0x01)
readU32OrSite(readU64_3203Low; 0x12a98;
  .Regidx 5#5, x5, rX_x5_run; .Regidx 17#5, x17, rX_x17_run;
  .Regidx 17#5, x17, wX_x17_run; 0xb3, 0xe8, 0x12, 0x01)
readU32OrSite(readU64_3203High; 0x12a9c;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 6#5, x6, rX_x6_run;
  .Regidx 16#5, x16, wX_x16_run; 0x33, 0x68, 0x68, 0x00)
readU32SlliSite(readU64_3203ShiftHigh; 0x12aa0, 32;
  .Regidx 16#5, x16, rX_x16_run, wX_x16_run; 0x13, 0x18, 0x08, 0x02)
readU32OrSite(readU64_3203Result; 0x12aa4;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 17#5, x17, rX_x17_run;
  .Regidx 16#5, x16, wX_x16_run; 0x33, 0x68, 0x18, 0x01)
readU32LiSite(readU64_3203Tag; 0x12aa8, 1;
  .Regidx 5#5, x5, wX_x5_run; 0x93, 0x02, 0x10, 0x00)

end BinaryFv.Zesu.MachineExecution
