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

/-- Compose the first four loads and their five low-word assembly instructions. -/
macro "read_u64_low_compose " own:ident "," exit:ident "," writes:ident ","
    instructionDisjoint:ident "," platformDisjoint:ident ";"
    start:term ";" source:term ";" r1:term "," r2:term "," r3:term "," r0:term ";"
    load1:ident "," load2:ident "," load3:ident "," load0:ident ","
    shift1:ident "," shift2:ident "," shift3:ident "," or0:ident "," or1:ident ";"
    fromStep:term "," baseAddress:term "," v0:term "," v1:term "," v2:term "," v3:term ","
    state:term "," configured:term "," atPc:term "," base:term ","
    rep0:term "," rep1:term "," rep2:term "," rep3:term ","
    pma:term "," notMMIO:term "," sourceFits:term "," loaded:term : term =>
  `(by
    let z0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v0)
    let z1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v1)
    let z2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v2)
    let z3 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v3)
    let sh1 := Sail.shift_bits_left z1 8#64
    let sh2 := Sail.shift_bits_left z2 16#64
    let sh3 := Sail.shift_bits_left z3 24#64
    let lo0 := sh1 ||| z0
    let lo1 := sh3 ||| sh2
    obtain ⟨retired, retiredRead⟩ := ($configured).retiredCounter
    have seg0 := (Seg.nil $own $exit (fun _ _ _ _ _ => False) $writes noMemory
      $fromStep ⟨retired, retiredRead⟩ $atPc).know $source
        (BitVec.ofNat 64 $baseAddress) $base
    have configuredOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) :=
      configuredMachinePre_of_readSeg $configured $instructionDisjoint seg
    have pmaOfSeg {kv n cur pc} (offset : Nat)
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc)
        (bound : offset < 4) :
        LoadPmaAllows cur (BitVec.ofNat 64 ($baseAddress + offset)) 1 :=
      loadPmaAllows_of_readSeg seg $platformDisjoint ($pma offset bound)
    have loadedOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) :=
      loadedFaithfully_of_readSeg seg $loaded
    have baseOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc)
        (present : (⟨$source, BitVec.ofNat 64 $baseAddress⟩ : RegVal) ∈ kv) :=
      seg.reg $source (BitVec.ofNat 64 $baseAddress) present
    obtain ⟨m1, seg1⟩ := seg0.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r1 z1 ($start + 4)
      ($load1 $fromStep $state $baseAddress $v1 $configured $atPc
        (baseOfSeg seg0 (by simp)) $rep1 ($pma 1 (by omega)) ($notMMIO 1 (by omega))
        (by have := $sourceFits; omega) $loaded)
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m2, seg2⟩ := seg1.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r2 z2 ($start + 8)
      ($load2 ($fromStep + 1) m1 $baseAddress $v2 (configuredOfSeg seg1) seg1.atPc
        (baseOfSeg seg1 (by simp)) (by simpa using uintRep_of_readSeg seg1 $rep2)
        (pmaOfSeg 2 seg1 (by omega)) ($notMMIO 2 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg1))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m3, seg3⟩ := seg2.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r3 z3 ($start + 12)
      ($load3 ($fromStep + 2) m2 $baseAddress $v3 (configuredOfSeg seg2) seg2.atPc
        (baseOfSeg seg2 (by simp)) (by simpa using uintRep_of_readSeg seg2 $rep3)
        (pmaOfSeg 3 seg2 (by omega)) ($notMMIO 3 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg2))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m4, seg4⟩ := seg3.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r0 z0 ($start + 16)
      ($load0 ($fromStep + 3) m3 $baseAddress $v0 (configuredOfSeg seg3) seg3.atPc
        (baseOfSeg seg3 (by simp)) (by simpa using uintRep_of_readSeg seg3 $rep0)
        (pmaOfSeg 0 seg3 (by omega)) ($notMMIO 0 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg3))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r5, run5⟩ := $shift1 ($fromStep + 4) m4 z1
      (configuredOfSeg seg4) seg4.atPc (seg4.reg $r1 z1 (by simp)) (loadedOfSeg seg4)
    have seg4' := seg4.forget
      (kv' := [⟨$r0, z0⟩, ⟨$r3, z3⟩, ⟨$r2, z2⟩,
        ⟨$source, BitVec.ofNat 64 $baseAddress⟩]) (by simp)
    obtain ⟨m5, seg5⟩ := seg4'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r1 sh1 ($start + 20) ⟨r5, run5⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r6, run6⟩ := $shift2 ($fromStep + 5) m5 z2
      (configuredOfSeg seg5) seg5.atPc (seg5.reg $r2 z2 (by simp)) (loadedOfSeg seg5)
    have seg5' := seg5.forget
      (kv' := [⟨$r1, sh1⟩, ⟨$r0, z0⟩, ⟨$r3, z3⟩,
        ⟨$source, BitVec.ofNat 64 $baseAddress⟩]) (by simp)
    obtain ⟨m6, seg6⟩ := seg5'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r2 sh2 ($start + 24) ⟨r6, run6⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r7, run7⟩ := $shift3 ($fromStep + 6) m6 z3
      (configuredOfSeg seg6) seg6.atPc (seg6.reg $r3 z3 (by simp)) (loadedOfSeg seg6)
    have seg6' := seg6.forget
      (kv' := [⟨$r2, sh2⟩, ⟨$r1, sh1⟩, ⟨$r0, z0⟩,
        ⟨$source, BitVec.ofNat 64 $baseAddress⟩]) (by simp)
    obtain ⟨m7, seg7⟩ := seg6'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r3 sh3 ($start + 28) ⟨r7, run7⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r8, run8⟩ := $or0 ($fromStep + 7) m7 sh1 z0
      (configuredOfSeg seg7) seg7.atPc (seg7.reg $r1 sh1 (by simp))
      (seg7.reg $r0 z0 (by simp)) (loadedOfSeg seg7)
    have seg7' := seg7.forget
      (kv' := [⟨$r3, sh3⟩, ⟨$r2, sh2⟩,
        ⟨$source, BitVec.ofNat 64 $baseAddress⟩]) (by simp)
    obtain ⟨m8, seg8⟩ := seg7'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r1 lo0 ($start + 32) ⟨r8, run8⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r9, run9⟩ := $or1 ($fromStep + 8) m8 sh3 sh2
      (configuredOfSeg seg8) seg8.atPc (seg8.reg $r3 sh3 (by simp))
      (seg8.reg $r2 sh2 (by simp)) (loadedOfSeg seg8)
    have seg8' := seg8.forget
      (kv' := [⟨$r1, lo0⟩, ⟨$source, BitVec.ofNat 64 $baseAddress⟩]) (by simp)
    obtain ⟨after, seg9⟩ := seg8'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r2 lo1 ($start + 36) ⟨r9, run9⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa [z0, z1, z2, z3, sh1, sh2, sh3, lo0, lo1] using seg9⟩)

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

/-- Shared low-word fragment instantiated at `fi:1:3203`. -/
theorem readU64_3203LowRun (fromStep baseAddress v0 v1 v2 v3 : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12a50))
    (base : state.regs.get? x16 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem baseAddress v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 1) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 2) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 3) v3)
    (pma : ∀ offset, offset < 4 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : ∀ offset, offset < 4 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sourceFits : baseAddress + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU64_3203OwnPc readU64_3203ExitPc (fun _ _ _ _ _ => False)
      readU64_3203Writes noMemory
      [⟨x5, (Sail.shift_bits_left
          (zero_extend (m := 64) (BitVec.ofNat 8 v3)) 24#64) |||
        (Sail.shift_bits_left (zero_extend (m := 64) (BitVec.ofNat 8 v2)) 16#64)⟩,
       ⟨x17, (Sail.shift_bits_left
          (zero_extend (m := 64) (BitVec.ofNat 8 v1)) 8#64) |||
        zero_extend (m := 64) (BitVec.ofNat 8 v0)⟩,
       ⟨x16, BitVec.ofNat 64 baseAddress⟩]
      fromStep 9 state after (BitVec.ofNat 64 0x12a74) :=
  read_u64_low_compose readU64_3203OwnPc, readU64_3203ExitPc, readU64_3203Writes,
    readU64_3203InstructionDisjoint, readU64_3203PlatformDisjoint;
    0x12a50; x16; x17, x5, x6, x7;
    readU64_3203Load1, readU64_3203Load2, readU64_3203Load3, readU64_3203Load0,
    readU64_3203Shift1, readU64_3203Shift2, readU64_3203Shift3,
    readU64_3203OrLow0, readU64_3203OrLow1;
    fromStep, baseAddress, v0, v1, v2, v3, state, configured, atPc, base,
    rep0, rep1, rep2, rep3, pma, notMMIO, sourceFits, loaded

end BinaryFv.Zesu.MachineExecution
