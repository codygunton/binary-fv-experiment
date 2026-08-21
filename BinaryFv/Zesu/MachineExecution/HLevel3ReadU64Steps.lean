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

/-- Compose one byte load followed by one stack spill, then forget the temporary load register.
The exact instruction theorems remain site data. This theorem owns the repeated `Seg` shape. -/
theorem readU64LoadSpillPair
    {own exit : BitVec 64 → Prop}
    {childSummary : Binary.Elfling.FunctionInstanceId → Nat → Nat → State → State → Prop}
    {W : RegSet} {M : Region} {kv : List RegVal} {a n : Nat}
    {base cur : State} {pc : BitVec 64}
    (seg : Seg own exit childSummary W M kv a n base cur pc)
    (destination : Register) (value : RegisterType destination) (stored : BitVec 64)
    (loadNext storeNext : BitVec 64) (address : Nat)
    (loadInRegion : own pc) (loadNotExit : ¬exit pc)
    (loadRun : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired destination value) false)
    (loadAdvance : Sail.BitVec.addInt pc 4 = loadNext)
    (bookkeeping : ∀ register, stepBookkeeping register → W register)
    (destinationWrites : W destination)
    (destinationNotPc : destination ≠ PC) (destinationNotRetired : destination ≠ minstret)
    (loadKeeps : RegsOutside (RegSet.union stepBookkeeping (RegSet.only destination)) kv)
    (storeInRegion : own loadNext) (storeNotExit : ¬exit loadNext)
    (storeRun : ∀ retired, ∃ storeRetired, Runs (try_step (a + (n + 1)) false)
      (afterRegisterWrite cur pc retired destination value)
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 8)
          (coreControlFlowNextState
            (tryStepControlFlowAfterIncrement
              (afterRegisterWrite cur pc retired destination value)) loadNext)
          address stored)
        (Sail.BitVec.addInt loadNext 4) storeRetired) false)
    (storeAdvance : Sail.BitVec.addInt loadNext 4 = storeNext)
    (storeInside : ∀ other, address ≤ other → other < address + 8 → M other)
    (storeKeeps : RegsOutside stepBookkeeping (⟨destination, value⟩ :: kv)) :
    ∃ next, Seg own exit childSummary W M kv a (n + 2) base next storeNext := by
  obtain ⟨retired, loaded, loadedEq, loadedSeg⟩ := seg.stepWitness loadInRegion loadNotExit
    destination value loadNext loadRun loadAdvance bookkeeping destinationWrites
    destinationNotPc destinationNotRetired loadKeeps
  subst loaded
  obtain ⟨storedState, storedSeg⟩ := loadedSeg.stepStore address stored storeNext
    storeInRegion storeNotExit (storeRun retired) storeAdvance storeInside bookkeeping storeKeeps
  exact ⟨storedState, by
    simpa [Nat.add_assoc] using storedSeg.forget (kv' := kv)
      (fun _ member => List.mem_cons_of_mem _ member)⟩

/-- Compose four consecutive byte loads while retaining all four loaded register values. -/
theorem readU64FourLiveLoads
    {own exit : BitVec 64 → Prop}
    {childSummary : Binary.Elfling.FunctionInstanceId → Nat → Nat → State → State → Prop}
    {W : RegSet} {M : Region} {kv : List RegVal} {a n : Nat}
    {base cur : State} {pc0 pc1 pc2 pc3 pc4 : BitVec 64}
    (seg : Seg own exit childSummary W M kv a n base cur pc0)
    (d0 d1 d2 d3 : Register)
    (v0 : RegisterType d0) (v1 : RegisterType d1)
    (v2 : RegisterType d2) (v3 : RegisterType d3)
    (run0 : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc0 retired d0 v0) false)
    (run1 : ∀ {next}, Seg own exit childSummary W M (⟨d0, v0⟩ :: kv)
      a (n + 1) base next pc1 →
      ∃ retired, Runs (try_step (a + (n + 1)) false) next
        (afterRegisterWrite next pc1 retired d1 v1) false)
    (run2 : ∀ {next}, Seg own exit childSummary W M (⟨d1, v1⟩ :: ⟨d0, v0⟩ :: kv)
      a (n + 2) base next pc2 →
      ∃ retired, Runs (try_step (a + (n + 2)) false) next
        (afterRegisterWrite next pc2 retired d2 v2) false)
    (run3 : ∀ {next}, Seg own exit childSummary W M
      (⟨d2, v2⟩ :: ⟨d1, v1⟩ :: ⟨d0, v0⟩ :: kv)
      a (n + 3) base next pc3 →
      ∃ retired, Runs (try_step (a + (n + 3)) false) next
        (afterRegisterWrite next pc3 retired d3 v3) false)
    (in0 : own pc0) (in1 : own pc1) (in2 : own pc2) (in3 : own pc3)
    (not0 : ¬exit pc0) (not1 : ¬exit pc1) (not2 : ¬exit pc2) (not3 : ¬exit pc3)
    (advance0 : Sail.BitVec.addInt pc0 4 = pc1)
    (advance1 : Sail.BitVec.addInt pc1 4 = pc2)
    (advance2 : Sail.BitVec.addInt pc2 4 = pc3)
    (advance3 : Sail.BitVec.addInt pc3 4 = pc4)
    (bookkeeping : ∀ register, stepBookkeeping register → W register)
    (writes0 : W d0) (writes1 : W d1) (writes2 : W d2) (writes3 : W d3)
    (notPc0 : d0 ≠ PC) (notPc1 : d1 ≠ PC) (notPc2 : d2 ≠ PC) (notPc3 : d3 ≠ PC)
    (notRetired0 : d0 ≠ minstret) (notRetired1 : d1 ≠ minstret)
    (notRetired2 : d2 ≠ minstret) (notRetired3 : d3 ≠ minstret)
    (keep0 : RegsOutside (RegSet.union stepBookkeeping (RegSet.only d0)) kv)
    (keep1 : RegsOutside (RegSet.union stepBookkeeping (RegSet.only d1)) (⟨d0, v0⟩ :: kv))
    (keep2 : RegsOutside (RegSet.union stepBookkeeping (RegSet.only d2))
      (⟨d1, v1⟩ :: ⟨d0, v0⟩ :: kv))
    (keep3 : RegsOutside (RegSet.union stepBookkeeping (RegSet.only d3))
      (⟨d2, v2⟩ :: ⟨d1, v1⟩ :: ⟨d0, v0⟩ :: kv)) :
    ∃ next, Seg own exit childSummary W M
      (⟨d3, v3⟩ :: ⟨d2, v2⟩ :: ⟨d1, v1⟩ :: ⟨d0, v0⟩ :: kv)
      a (n + 4) base next pc4 := by
  obtain ⟨s1, seg1⟩ := seg.step in0 not0 d0 v0 pc1 run0 advance0 bookkeeping writes0
    notPc0 notRetired0 keep0
  obtain ⟨s2, seg2⟩ := seg1.step in1 not1 d1 v1 pc2 (run1 seg1) advance1
    bookkeeping writes1 notPc1 notRetired1 keep1
  obtain ⟨s3, seg3⟩ := seg2.step in2 not2 d2 v2 pc3 (run2 (by simpa [Nat.add_assoc] using seg2))
    advance2 bookkeeping writes2 notPc2 notRetired2 keep2
  obtain ⟨s4, seg4⟩ := seg3.step in3 not3 d3 v3 pc4 (run3 (by
    simpa [Nat.add_assoc] using seg3)) advance3 bookkeeping writes3 notPc3 notRetired3 keep3
  exact ⟨s4, by simpa [Nat.add_assoc] using seg4⟩

/-- Compose one five-step half-word assembly while handling each overwritten register once. -/
theorem readU64HalfAssemblyFromSteps
    {own exit : BitVec 64 → Prop}
    {childSummary : Binary.Elfling.FunctionInstanceId → Nat → Nat → State → State → Prop}
    {W : RegSet} {M : Region} {kv : List RegVal} {a n : Nat} {base cur : State}
    {pc0 pc1 pc2 pc3 pc4 pc5 : BitVec 64}
    (r0 r1 r2 r3 : Register)
    (z0 : RegisterType r0) (z1 sh1 lo0 : RegisterType r1)
    (z2 sh2 lo1 : RegisterType r2) (z3 sh3 : RegisterType r3)
    (seg : Seg own exit childSummary W M
      (⟨r3, z3⟩ :: ⟨r2, z2⟩ :: ⟨r1, z1⟩ :: ⟨r0, z0⟩ :: kv)
      a n base cur pc0)
    (shift1 : ∀ {current}, Seg own exit childSummary W M
      (⟨r3, z3⟩ :: ⟨r2, z2⟩ :: ⟨r0, z0⟩ :: kv) a n base current pc0 →
      ∃ next, Seg own exit childSummary W M
        (⟨r1, sh1⟩ :: ⟨r3, z3⟩ :: ⟨r2, z2⟩ :: ⟨r0, z0⟩ :: kv)
        a (n + 1) base next pc1)
    (shift2 : ∀ {current}, Seg own exit childSummary W M
      (⟨r1, sh1⟩ :: ⟨r3, z3⟩ :: ⟨r0, z0⟩ :: kv) a (n + 1) base current pc1 →
      ∃ next, Seg own exit childSummary W M
        (⟨r2, sh2⟩ :: ⟨r1, sh1⟩ :: ⟨r3, z3⟩ :: ⟨r0, z0⟩ :: kv)
        a (n + 2) base next pc2)
    (shift3 : ∀ {current}, Seg own exit childSummary W M
      (⟨r2, sh2⟩ :: ⟨r1, sh1⟩ :: ⟨r0, z0⟩ :: kv) a (n + 2) base current pc2 →
      ∃ next, Seg own exit childSummary W M
        (⟨r3, sh3⟩ :: ⟨r2, sh2⟩ :: ⟨r1, sh1⟩ :: ⟨r0, z0⟩ :: kv)
        a (n + 3) base next pc3)
    (or0 : ∀ {current}, Seg own exit childSummary W M
      (⟨r3, sh3⟩ :: ⟨r2, sh2⟩ :: ⟨r0, z0⟩ :: kv) a (n + 3) base current pc3 →
      ∃ next, Seg own exit childSummary W M
        (⟨r1, lo0⟩ :: ⟨r3, sh3⟩ :: ⟨r2, sh2⟩ :: ⟨r0, z0⟩ :: kv)
        a (n + 4) base next pc4)
    (or1 : ∀ {current}, Seg own exit childSummary W M
      (⟨r1, lo0⟩ :: ⟨r3, sh3⟩ :: ⟨r0, z0⟩ :: kv) a (n + 4) base current pc4 →
      ∃ next, Seg own exit childSummary W M
        (⟨r2, lo1⟩ :: ⟨r1, lo0⟩ :: ⟨r3, sh3⟩ :: ⟨r0, z0⟩ :: kv)
        a (n + 5) base next pc5) :
    ∃ next, Seg own exit childSummary W M
      (⟨r2, lo1⟩ :: ⟨r1, lo0⟩ :: kv) a (n + 5) base next pc5 := by
  have before1 := seg.forget
    (kv' := ⟨r3, z3⟩ :: ⟨r2, z2⟩ :: ⟨r0, z0⟩ :: kv) (by
      intro p hp
      simp only [List.mem_cons] at hp ⊢
      grind)
  obtain ⟨s1, seg1⟩ := shift1 before1
  have before2 := seg1.forget
    (kv' := ⟨r1, sh1⟩ :: ⟨r3, z3⟩ :: ⟨r0, z0⟩ :: kv) (by
      intro p hp
      simp only [List.mem_cons] at hp ⊢
      grind)
  obtain ⟨s2, seg2⟩ := shift2 before2
  have before3 := seg2.forget
    (kv' := ⟨r2, sh2⟩ :: ⟨r1, sh1⟩ :: ⟨r0, z0⟩ :: kv) (by
      intro p hp
      simp only [List.mem_cons] at hp ⊢
      grind)
  obtain ⟨s3, seg3⟩ := shift3 before3
  have before4 := seg3.forget
    (kv' := ⟨r3, sh3⟩ :: ⟨r2, sh2⟩ :: ⟨r0, z0⟩ :: kv) (by
      intro p hp
      simp only [List.mem_cons] at hp ⊢
      grind)
  obtain ⟨s4, seg4⟩ := or0 before4
  have before5 := seg4.forget
    (kv' := ⟨r1, lo0⟩ :: ⟨r3, sh3⟩ :: ⟨r0, z0⟩ :: kv) (by
      intro p hp
      simp only [List.mem_cons] at hp ⊢
      grind)
  obtain ⟨s5, seg5⟩ := or1 before5
  exact ⟨s5, seg5.forget (kv' := ⟨r2, lo1⟩ :: ⟨r1, lo0⟩ :: kv) (by
    intro p hp
    simp only [List.mem_cons] at hp ⊢
    grind)⟩

/-- Declare one exact eight-byte spill used by a split `readU64` schedule. -/
macro "readU64SpillSite(" name:ident ";" pc:term "," immediate:term ";"
    baseIndex:term "," sourceIndex:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (state afterWrite : State)
      (configured : ConfiguredMachinePre EndpointMachinePc state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
      (access : ConfiguredDwordStoreAccess state afterWrite (BitVec.ofNat 64 $pc)
        (BitVec.ofNat 12 $immediate) $baseIndex $sourceIndex) :
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepStoreAfterRetired afterWrite (BitVec.ofNat 64 $pc) retired) false := by
      exact configuredDwordStoreStep stepNo $pc state afterWrite (BitVec.ofNat 12 $immediate)
        $baseIndex $sourceIndex $byte0 $byte1 $byte2 $byte3 configured atPc loaded
        (by configured_store_decode configured) access (base := by rfl))

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

/-- Compose the high four loads, both half-word joins, the final join, and the success tag. -/
macro "read_u64_high_compose " own:ident "," exit:ident "," writes:ident ","
    instructionDisjoint:ident "," platformDisjoint:ident ";"
    start:term ";" source:term ";" r1:term "," r2:term "," r3:term "," r0:term "," r6:term ","
    resultReg:term "," tag:term ";"
    load5:ident "," load4:ident "," load6:ident "," load7:ident ","
    shift5:ident "," or0:ident "," shift6:ident "," shift7:ident "," or1:ident ","
    low:ident "," high:ident "," shiftHigh:ident "," result:ident "," tagStep:ident ";"
    fromStep:term "," baseAddress:term ","
    v0:term "," v1:term "," v2:term "," v3:term ","
    v4:term "," v5:term "," v6:term "," v7:term ","
    state:term "," configured:term "," prefixSeg:term ","
    rep4:term "," rep5:term "," rep6:term "," rep7:term ","
    pma:term "," notMMIO:term "," sourceFits:term "," loaded:term : term =>
  `(by
    let z0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v0)
    let z1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v1)
    let z2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v2)
    let z3 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v3)
    let z4 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v4)
    let z5 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v5)
    let z6 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v6)
    let z7 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v7)
    let lo0 := (Sail.shift_bits_left z1 8#64) ||| z0
    let lo1 := (Sail.shift_bits_left z3 24#64) ||| (Sail.shift_bits_left z2 16#64)
    let sh5 := Sail.shift_bits_left z5 8#64
    let hi0 := sh5 ||| z4
    let sh6 := Sail.shift_bits_left z6 16#64
    let sh7 := Sail.shift_bits_left z7 24#64
    let hi1 := sh7 ||| sh6
    let lowWord := lo1 ||| lo0
    let highWord := hi1 ||| hi0
    let shiftedHigh := Sail.shift_bits_left highWord 32#64
    let final := shiftedHigh ||| lowWord
    have configuredOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) :=
      configuredMachinePre_of_readSeg $configured $instructionDisjoint seg
    have pmaOfSeg {kv n cur pc} (offset : Nat)
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) (bound : offset < 8) :
        LoadPmaAllows cur (BitVec.ofNat 64 ($baseAddress + offset)) 1 :=
      loadPmaAllows_of_readSeg seg $platformDisjoint ($pma offset bound)
    have loadedOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) := loadedFaithfully_of_readSeg seg $loaded
    have repOfSeg {kv n cur pc offset value}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) (rep : UIntRep 1 ($state).mem ($baseAddress + offset) value) :
        UIntRep 1 cur.mem ($baseAddress + offset) value := uintRep_of_readSeg seg rep
    have seg9 := $prefixSeg
    obtain ⟨m10, seg10⟩ := seg9.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r3 z5 ($start + 4)
      ($load5 ($fromStep + 9) _ $baseAddress $v5 (configuredOfSeg seg9) seg9.atPc
        (seg9.reg $source (BitVec.ofNat 64 $baseAddress) (by simp [z0, z1, z2, z3, lo0, lo1]))
        (repOfSeg seg9 $rep5) (pmaOfSeg 5 seg9 (by omega)) ($notMMIO 5 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg9))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m11, seg11⟩ := seg10.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r0 z4 ($start + 8)
      ($load4 ($fromStep + 10) _ $baseAddress $v4 (configuredOfSeg seg10) seg10.atPc
        (seg10.reg $source (BitVec.ofNat 64 $baseAddress) (by simp))
        (repOfSeg seg10 $rep4) (pmaOfSeg 4 seg10 (by omega)) ($notMMIO 4 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg10))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m12, seg12⟩ := seg11.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r6 z6 ($start + 12)
      ($load6 ($fromStep + 11) _ $baseAddress $v6 (configuredOfSeg seg11) seg11.atPc
        (seg11.reg $source (BitVec.ofNat 64 $baseAddress) (by simp))
        (repOfSeg seg11 $rep6) (pmaOfSeg 6 seg11 (by omega)) ($notMMIO 6 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg11))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r13, run13⟩ := $load7 ($fromStep + 12) _ $baseAddress $v7
      (configuredOfSeg seg12) seg12.atPc
      (seg12.reg $source (BitVec.ofNat 64 $baseAddress) (by simp))
      (repOfSeg seg12 $rep7) (pmaOfSeg 7 seg12 (by omega)) ($notMMIO 7 (by omega))
      (by have := $sourceFits; omega) (loadedOfSeg seg12)
    have seg12' := seg12.forget
      (kv' := [⟨$r6, z6⟩, ⟨$r0, z4⟩, ⟨$r3, z5⟩,
        ⟨$r2, lo1⟩, ⟨$r1, lo0⟩]) (by simp [z0, z1, z2, z3, lo0, lo1])
    obtain ⟨m13, seg13⟩ := seg12'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $source z7 ($start + 16) ⟨r13, run13⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r14, run14⟩ := $shift5 ($fromStep + 13) _ z5
      (configuredOfSeg seg13) seg13.atPc (seg13.reg $r3 z5 (by simp)) (loadedOfSeg seg13)
    have seg13' := seg13.forget
      (kv' := [⟨$source, z7⟩, ⟨$r6, z6⟩, ⟨$r0, z4⟩,
        ⟨$r2, lo1⟩, ⟨$r1, lo0⟩]) (by simp)
    obtain ⟨m14, seg14⟩ := seg13'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r3 sh5 ($start + 20) ⟨r14, run14⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r15, run15⟩ := $or0 ($fromStep + 14) _ sh5 z4
      (configuredOfSeg seg14) seg14.atPc (seg14.reg $r3 sh5 (by simp))
      (seg14.reg $r0 z4 (by simp)) (loadedOfSeg seg14)
    have seg14' := seg14.forget
      (kv' := [⟨$source, z7⟩, ⟨$r6, z6⟩, ⟨$r2, lo1⟩, ⟨$r1, lo0⟩]) (by simp)
    obtain ⟨m15, seg15⟩ := seg14'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r3 hi0 ($start + 24) ⟨r15, run15⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r16, run16⟩ := $shift6 ($fromStep + 15) _ z6
      (configuredOfSeg seg15) seg15.atPc (seg15.reg $r6 z6 (by simp)) (loadedOfSeg seg15)
    have seg15' := seg15.forget
      (kv' := [⟨$r3, hi0⟩, ⟨$source, z7⟩, ⟨$r2, lo1⟩, ⟨$r1, lo0⟩]) (by simp)
    obtain ⟨m16, seg16⟩ := seg15'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r6 sh6 ($start + 28) ⟨r16, run16⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r17, run17⟩ := $shift7 ($fromStep + 16) _ z7
      (configuredOfSeg seg16) seg16.atPc (seg16.reg $source z7 (by simp)) (loadedOfSeg seg16)
    have seg16' := seg16.forget
      (kv' := [⟨$r6, sh6⟩, ⟨$r3, hi0⟩, ⟨$r2, lo1⟩, ⟨$r1, lo0⟩]) (by simp)
    obtain ⟨m17, seg17⟩ := seg16'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $source sh7 ($start + 32) ⟨r17, run17⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r18, run18⟩ := $or1 ($fromStep + 17) _ sh7 sh6
      (configuredOfSeg seg17) seg17.atPc (seg17.reg $source sh7 (by simp))
      (seg17.reg $r6 sh6 (by simp)) (loadedOfSeg seg17)
    have seg17' := seg17.forget
      (kv' := [⟨$r3, hi0⟩, ⟨$r2, lo1⟩, ⟨$r1, lo0⟩]) (by simp)
    obtain ⟨m18, seg18⟩ := seg17'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $source hi1 ($start + 36) ⟨r18, run18⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r19, run19⟩ := $low ($fromStep + 18) _ lo1 lo0
      (configuredOfSeg seg18) seg18.atPc (seg18.reg $r2 lo1 (by simp))
      (seg18.reg $r1 lo0 (by simp)) (loadedOfSeg seg18)
    have seg18' := seg18.forget (kv' := [⟨$source, hi1⟩, ⟨$r3, hi0⟩]) (by simp)
    obtain ⟨m19, seg19⟩ := seg18'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $r1 lowWord ($start + 40) ⟨r19, run19⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r20, run20⟩ := $high ($fromStep + 19) _ hi1 hi0
      (configuredOfSeg seg19) seg19.atPc (seg19.reg $source hi1 (by simp))
      (seg19.reg $r3 hi0 (by simp)) (loadedOfSeg seg19)
    have seg19' := seg19.forget (kv' := [⟨$r1, lowWord⟩]) (by simp)
    obtain ⟨m20, seg20⟩ := seg19'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $source highWord ($start + 44) ⟨r20, run20⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r21, run21⟩ := $shiftHigh ($fromStep + 20) _ highWord
      (configuredOfSeg seg20) seg20.atPc (seg20.reg $source highWord (by simp))
      (loadedOfSeg seg20)
    have seg20' := seg20.forget (kv' := [⟨$r1, lowWord⟩]) (by simp)
    obtain ⟨m21, seg21⟩ := seg20'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $source shiftedHigh ($start + 48) ⟨r21, run21⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r22, run22⟩ := $result ($fromStep + 21) _ shiftedHigh lowWord
      (configuredOfSeg seg21) seg21.atPc (seg21.reg $source shiftedHigh (by simp))
      (seg21.reg $r1 lowWord (by simp)) (loadedOfSeg seg21)
    have seg21' := seg21.forget (kv' := []) (by simp)
    obtain ⟨m22, seg22⟩ := seg21'.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $resultReg final ($start + 52) ⟨r22, run22⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r23, run23⟩ := $tagStep ($fromStep + 22) _ (configuredOfSeg seg22)
      seg22.atPc (loadedOfSeg seg22)
    obtain ⟨after, seg23⟩ := seg22.step
      (by unfold $own standardReadU64OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU64ExitPc pcInList; native_decide)
      $tag 1 ($start + 56) ⟨r23, run23⟩ (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU64Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa [readU64MachineValue, z0, z1, z2, z3, z4, z5, z6, z7,
      lo0, lo1, sh5, sh6, sh7, hi0, hi1, lowWord, highWord, shiftedHigh, final] using seg23⟩)

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

def readU64_327bOwnPc (pc : BitVec 64) : Prop := standardReadU64OwnPc 0x12df4 pc
def readU64_327bExitPc (pc : BitVec 64) : Prop := standardReadU64ExitPc 0x12df4 pc
def readU64_327bWrites (register : Register) : Prop :=
  standardReadU64Writes x12 x13 x14 x15 x16 x17 register

private theorem readU64_327bInstructionDisjoint :
    RegSet.Disjoint instructionPreserved readU64_327bWrites :=
  standardReadU64InstructionDisjoint x12 x13 x14 x15 x16 x17
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])
    (by simp [instructionPreserved, platformPreserved])

private theorem readU64_327bPlatformDisjoint :
    RegSet.Disjoint platformPreserved readU64_327bWrites :=
  standardReadU64PlatformDisjoint x12 x13 x14 x15 x16 x17
    (by simp [platformPreserved]) (by simp [platformPreserved])
    (by simp [platformPreserved]) (by simp [platformPreserved])
    (by simp [platformPreserved]) (by simp [platformPreserved])

readU32UnsignedLoadSite(readU64_327bLoad1; 0x12df8, 1;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 13#5, x13, wX_x13_run;
  0x83, 0x46, 0x16, 0x00)
readU32UnsignedLoadSite(readU64_327bLoad2; 0x12dfc, 2;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 14#5, x14, wX_x14_run;
  0x03, 0x47, 0x26, 0x00)
readU32UnsignedLoadSite(readU64_327bLoad3; 0x12e00, 3;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 15#5, x15, wX_x15_run;
  0x83, 0x47, 0x36, 0x00)
readU32UnsignedLoadSite(readU64_327bLoad0; 0x12e04, 0;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 16#5, x16, wX_x16_run;
  0x03, 0x48, 0x06, 0x00)
readU32SlliSite(readU64_327bShift1; 0x12e08, 8;
  .Regidx 13#5, x13, rX_x13_run, wX_x13_run; 0x93, 0x96, 0x86, 0x00)
readU32SlliSite(readU64_327bShift2; 0x12e0c, 16;
  .Regidx 14#5, x14, rX_x14_run, wX_x14_run; 0x13, 0x17, 0x07, 0x01)
readU32SlliSite(readU64_327bShift3; 0x12e10, 24;
  .Regidx 15#5, x15, rX_x15_run, wX_x15_run; 0x93, 0x97, 0x87, 0x01)
readU32OrSite(readU64_327bOrLow0; 0x12e14;
  .Regidx 13#5, x13, rX_x13_run; .Regidx 16#5, x16, rX_x16_run;
  .Regidx 13#5, x13, wX_x13_run; 0xb3, 0xe6, 0x06, 0x01)
readU32OrSite(readU64_327bOrLow1; 0x12e18;
  .Regidx 15#5, x15, rX_x15_run; .Regidx 14#5, x14, rX_x14_run;
  .Regidx 14#5, x14, wX_x14_run; 0x33, 0xe7, 0xe7, 0x00)
readU32UnsignedLoadSite(readU64_327bLoad5; 0x12e1c, 5;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 15#5, x15, wX_x15_run;
  0x83, 0x47, 0x56, 0x00)
readU32UnsignedLoadSite(readU64_327bLoad4; 0x12e20, 4;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 16#5, x16, wX_x16_run;
  0x03, 0x48, 0x46, 0x00)
readU32UnsignedLoadSite(readU64_327bLoad6; 0x12e24, 6;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 17#5, x17, wX_x17_run;
  0x83, 0x48, 0x66, 0x00)
readU32UnsignedLoadSite(readU64_327bLoad7; 0x12e28, 7;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 12#5, x12, wX_x12_run;
  0x03, 0x46, 0x76, 0x00)
readU32SlliSite(readU64_327bShift5; 0x12e2c, 8;
  .Regidx 15#5, x15, rX_x15_run, wX_x15_run; 0x93, 0x97, 0x87, 0x00)
readU32OrSite(readU64_327bOrHigh0; 0x12e30;
  .Regidx 15#5, x15, rX_x15_run; .Regidx 16#5, x16, rX_x16_run;
  .Regidx 15#5, x15, wX_x15_run; 0xb3, 0xe7, 0x07, 0x01)
readU32SlliSite(readU64_327bShift6; 0x12e34, 16;
  .Regidx 17#5, x17, rX_x17_run, wX_x17_run; 0x93, 0x98, 0x08, 0x01)
readU32SlliSite(readU64_327bShift7; 0x12e38, 24;
  .Regidx 12#5, x12, rX_x12_run, wX_x12_run; 0x13, 0x16, 0x86, 0x01)
readU32OrSite(readU64_327bOrHigh1; 0x12e3c;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 17#5, x17, rX_x17_run;
  .Regidx 12#5, x12, wX_x12_run; 0x33, 0x66, 0x16, 0x01)
readU32OrSite(readU64_327bLow; 0x12e40;
  .Regidx 14#5, x14, rX_x14_run; .Regidx 13#5, x13, rX_x13_run;
  .Regidx 13#5, x13, wX_x13_run; 0xb3, 0x66, 0xd7, 0x00)
readU32OrSite(readU64_327bHigh; 0x12e44;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 15#5, x15, rX_x15_run;
  .Regidx 12#5, x12, wX_x12_run; 0x33, 0x66, 0xf6, 0x00)
readU32SlliSite(readU64_327bShiftHigh; 0x12e48, 32;
  .Regidx 12#5, x12, rX_x12_run, wX_x12_run; 0x13, 0x16, 0x06, 0x02)
readU32OrSite(readU64_327bResult; 0x12e4c;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 13#5, x13, rX_x13_run;
  .Regidx 17#5, x17, wX_x17_run; 0xb3, 0x68, 0xd6, 0x00)
readU32LiSite(readU64_327bTag; 0x12e50, 1;
  .Regidx 16#5, x16, wX_x16_run; 0x13, 0x08, 0x10, 0x00)

/-! ## Exact site data for split load-spill schedules -/

readU32UnsignedLoadSite(readU64_35abLoad404; 0x138b8, 404;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 27#5, x27, wX_x27_run; 0x83, 0xcd, 0x4b, 0x19)
readU32UnsignedLoadSite(readU64_35abLoad405; 0x138bc, 405;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x5b, 0x19)
readU64SpillSite(readU64_35abSpill405; 0x138c0, 0x230;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x38, 0xa1, 0x22)
readU32UnsignedLoadSite(readU64_35abLoad406; 0x138c4, 406;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x6b, 0x19)
readU64SpillSite(readU64_35abSpill406; 0x138c8, 0x240;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x30, 0xa1, 0x24)
readU32UnsignedLoadSite(readU64_35abLoad407; 0x138cc, 407;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x7b, 0x19)
readU64SpillSite(readU64_35abSpill407; 0x138d0, 0x238;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x3c, 0xa1, 0x22)
readU32UnsignedLoadSite(readU64_35abLoad408; 0x138d4, 408;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x8b, 0x19)
readU64SpillSite(readU64_35abSpill408; 0x138d8, 0x208;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x34, 0xa1, 0x20)
readU32UnsignedLoadSite(readU64_35abLoad409; 0x138dc, 409;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x9b, 0x19)
readU64SpillSite(readU64_35abSpill409; 0x138e0, 0x168;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x34, 0xa1, 0x16)
readU32UnsignedLoadSite(readU64_35abLoad410; 0x138e4, 410;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0xab, 0x19)
readU64SpillSite(readU64_35abSpill410; 0x138e8, 0x200;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x30, 0xa1, 0x20)
readU32UnsignedLoadSite(readU64_35abLoad411; 0x138ec, 411;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0xbb, 0x19)
readU64SpillSite(readU64_35abSpill411; 0x138f0, 0x1f8;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x3c, 0xa1, 0x1e)

readU32UnsignedLoadSite(readU64_361fLoad412; 0x138f4, 412;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0xcb, 0x19)
readU64SpillSite(readU64_361fSpill412; 0x138f8, 0x228;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x34, 0xa1, 0x22)
readU32UnsignedLoadSite(readU64_361fLoad413; 0x138fc, 413;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0xdb, 0x19)
readU64SpillSite(readU64_361fSpill413; 0x13900, 0x210;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x38, 0xa1, 0x20)
readU32UnsignedLoadSite(readU64_361fLoad414; 0x13904, 414;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0xeb, 0x19)
readU64SpillSite(readU64_361fSpill414; 0x13908, 0x220;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x30, 0xa1, 0x22)
readU32UnsignedLoadSite(readU64_361fLoad415; 0x1390c, 415;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0xfb, 0x19)
readU64SpillSite(readU64_361fSpill415; 0x13910, 0x218;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x3c, 0xa1, 0x20)
readU32UnsignedLoadSite(readU64_361fLoad416; 0x13914, 416;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x0b, 0x1a)
readU64SpillSite(readU64_361fSpill416; 0x13918, 0x160;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x30, 0xa1, 0x16)
readU32UnsignedLoadSite(readU64_361fLoad417; 0x1391c, 417;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x1b, 0x1a)
readU64SpillSite(readU64_361fSpill417; 0x13920, 0x148;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x34, 0xa1, 0x14)
readU32UnsignedLoadSite(readU64_361fLoad418; 0x13924, 418;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x2b, 0x1a)
readU64SpillSite(readU64_361fSpill418; 0x13928, 0x158;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x3c, 0xa1, 0x14)
readU32UnsignedLoadSite(readU64_361fLoad419; 0x1392c, 419;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 10#5, x10, wX_x10_run; 0x03, 0xc5, 0x3b, 0x1a)
readU64SpillSite(readU64_361fSpill419; 0x13930, 0x150;
  .Regidx 2#5, .Regidx 10#5; 0x23, 0x38, 0xa1, 0x14)

readU32UnsignedLoadSite(readU64_36ddLoad420; 0x1398c, 420;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 13#5, x13, wX_x13_run; 0x83, 0xc6, 0x4b, 0x1a)
readU64SpillSite(readU64_36ddSpill420; 0x13990, 0x140;
  .Regidx 2#5, .Regidx 13#5; 0x23, 0x30, 0xd1, 0x14)
readU32UnsignedLoadSite(readU64_36ddLoad421; 0x13994, 421;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 13#5, x13, wX_x13_run; 0x83, 0xc6, 0x5b, 0x1a)
readU64SpillSite(readU64_36ddSpill421; 0x13998, 0x128;
  .Regidx 2#5, .Regidx 13#5; 0x23, 0x34, 0xd1, 0x12)
readU32UnsignedLoadSite(readU64_36ddLoad422; 0x1399c, 422;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 13#5, x13, wX_x13_run; 0x83, 0xc6, 0x6b, 0x1a)
readU64SpillSite(readU64_36ddSpill422; 0x139a0, 0x138;
  .Regidx 2#5, .Regidx 13#5; 0x23, 0x3c, 0xd1, 0x12)
readU32UnsignedLoadSite(readU64_36ddLoad423; 0x139a4, 423;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 13#5, x13, wX_x13_run; 0x83, 0xc6, 0x7b, 0x1a)
readU64SpillSite(readU64_36ddSpill423; 0x139a8, 0x130;
  .Regidx 2#5, .Regidx 13#5; 0x23, 0x38, 0xd1, 0x12)

readU32UnsignedLoadSite(readU64_36ddLoad424; 0x139c8, 424;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0x8b, 0x1a)
readU64SpillSite(readU64_36ddSpill424; 0x139cc, 0x0e0;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x30, 0xc1, 0x0e)
readU32UnsignedLoadSite(readU64_36ddLoad425; 0x139d0, 425;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0x9b, 0x1a)
readU64SpillSite(readU64_36ddSpill425; 0x139d4, 0x0c8;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x34, 0xc1, 0x0c)
readU32UnsignedLoadSite(readU64_36ddLoad426; 0x139d8, 426;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xab, 0x1a)
readU64SpillSite(readU64_36ddSpill426; 0x139dc, 0x0d8;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x3c, 0xc1, 0x0c)
readU32UnsignedLoadSite(readU64_36ddLoad427; 0x139e0, 427;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xbb, 0x1a)
readU64SpillSite(readU64_36ddSpill427; 0x139e4, 0x0d0;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x38, 0xc1, 0x0c)

readU32UnsignedLoadSite(readU64_3731Load428; 0x139f4, 428;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xcb, 0x1a)
readU64SpillSite(readU64_3731Spill428; 0x139f8, 0x120;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x30, 0xc1, 0x12)
readU32UnsignedLoadSite(readU64_3731Load429; 0x139fc, 429;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xdb, 0x1a)
readU64SpillSite(readU64_3731Spill429; 0x13a00, 0x108;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x34, 0xc1, 0x10)
readU32UnsignedLoadSite(readU64_3731Load430; 0x13a04, 430;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xeb, 0x1a)
readU64SpillSite(readU64_3731Spill430; 0x13a08, 0x118;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x3c, 0xc1, 0x10)
readU32UnsignedLoadSite(readU64_3731Load431; 0x13a0c, 431;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xfb, 0x1a)
readU64SpillSite(readU64_3731Spill431; 0x13a10, 0x110;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x38, 0xc1, 0x10)
readU32UnsignedLoadSite(readU64_3731Load432; 0x13a14, 432;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 9#5, x9, wX_x9_run; 0x83, 0xc4, 0x0b, 0x1b)
readU32UnsignedLoadSite(readU64_3731Load433; 0x13a18, 433;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 21#5, x21, wX_x21_run; 0x83, 0xca, 0x1b, 0x1b)
readU32UnsignedLoadSite(readU64_3731Load434; 0x13a1c, 434;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 19#5, x19, wX_x19_run; 0x83, 0xc9, 0x2b, 0x1b)
readU32UnsignedLoadSite(readU64_3731Load435; 0x13a20, 435;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 20#5, x20, wX_x20_run; 0x03, 0xca, 0x3b, 0x1b)

readU32UnsignedLoadSite(readU64_37a5Load440; 0x13a24, 440;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0x8b, 0x1b)
readU64SpillSite(readU64_37a5Spill440; 0x13a28, 0x100;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x30, 0xc1, 0x10)
readU32UnsignedLoadSite(readU64_37a5Load441; 0x13a2c, 441;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0x9b, 0x1b)
readU64SpillSite(readU64_37a5Spill441; 0x13a30, 0x0e8;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x34, 0xc1, 0x0e)
readU32UnsignedLoadSite(readU64_37a5Load442; 0x13a34, 442;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xab, 0x1b)
readU64SpillSite(readU64_37a5Spill442; 0x13a38, 0x0f8;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x3c, 0xc1, 0x0e)
readU32UnsignedLoadSite(readU64_37a5Load443; 0x13a3c, 443;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 12#5, x12, wX_x12_run; 0x03, 0xc6, 0xbb, 0x1b)
readU64SpillSite(readU64_37a5Spill443; 0x13a40, 0x0f0;
  .Regidx 2#5, .Regidx 12#5; 0x23, 0x38, 0xc1, 0x0e)
readU32UnsignedLoadSite(readU64_37a5Load444; 0x13a44, 444;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 22#5, x22, wX_x22_run; 0x03, 0xcb, 0xcb, 0x1b)
readU32UnsignedLoadSite(readU64_37a5Load445; 0x13a48, 445;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 26#5, x26, wX_x26_run; 0x03, 0xcd, 0xdb, 0x1b)
readU32UnsignedLoadSite(readU64_37a5Load446; 0x13a4c, 446;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 24#5, x24, wX_x24_run; 0x03, 0xcc, 0xeb, 0x1b)
readU32UnsignedLoadSite(readU64_37a5Load447; 0x13a50, 447;
  .Regidx 23#5, x23, rX_x23_run;
  .Regidx 25#5, x25, wX_x25_run; 0x83, 0xcc, 0xfb, 0x1b)

/-! `fi:1:3823` has parent instructions between these shared reader operations. -/

readU32UnsignedLoadSite(readU64_3823Load532; 0x13cf0, 532;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 6#5, x6, wX_x6_run; 0x03, 0x43, 0x4f, 0x21)
readU32UnsignedLoadSite(readU64_3823Load533; 0x13cf4, 533;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 7#5, x7, wX_x7_run; 0x83, 0x43, 0x5f, 0x21)
readU32UnsignedLoadSite(readU64_3823Load534; 0x13cf8, 534;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 28#5, x28, wX_x28_run; 0x03, 0x4e, 0x6f, 0x21)
readU32UnsignedLoadSite(readU64_3823Load535; 0x13cfc, 535;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 29#5, x29, wX_x29_run; 0x83, 0x4e, 0x7f, 0x21)
readU32SlliSite(readU64_3823Shift533; 0x13d0c, 8;
  .Regidx 7#5, x7, rX_x7_run, wX_x7_run; 0x93, 0x93, 0x83, 0x00)
readU32SlliSite(readU64_3823Shift534; 0x13d10, 16;
  .Regidx 28#5, x28, rX_x28_run, wX_x28_run; 0x13, 0x1e, 0x0e, 0x01)
readU32SlliSite(readU64_3823Shift535; 0x13d14, 24;
  .Regidx 29#5, x29, rX_x29_run, wX_x29_run; 0x93, 0x9e, 0x8e, 0x01)
readU32OrSite(readU64_3823OrLow0; 0x13d20;
  .Regidx 7#5, x7, rX_x7_run; .Regidx 6#5, x6, rX_x6_run;
  .Regidx 17#5, x17, wX_x17_run; 0xb3, 0xe8, 0x63, 0x00)
readU32OrSite(readU64_3823OrLow1; 0x13d24;
  .Regidx 29#5, x29, rX_x29_run; .Regidx 28#5, x28, rX_x28_run;
  .Regidx 5#5, x5, wX_x5_run; 0xb3, 0xe2, 0xce, 0x01)
readU32UnsignedLoadSite(readU64_3823Load537; 0x13d28, 537;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 6#5, x6, wX_x6_run; 0x03, 0x43, 0x9f, 0x21)
readU32UnsignedLoadSite(readU64_3823Load536; 0x13d2c, 536;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 7#5, x7, wX_x7_run; 0x83, 0x43, 0x8f, 0x21)
readU32UnsignedLoadSite(readU64_3823Load538; 0x13d30, 538;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 28#5, x28, wX_x28_run; 0x03, 0x4e, 0xaf, 0x21)
readU32UnsignedLoadSite(readU64_3823Load539; 0x13d34, 539;
  .Regidx 30#5, x30, rX_x30_run;
  .Regidx 29#5, x29, wX_x29_run; 0x83, 0x4e, 0xbf, 0x21)
readU32SlliSite(readU64_3823Shift537; 0x13d38, 8;
  .Regidx 6#5, x6, rX_x6_run, wX_x6_run; 0x13, 0x13, 0x83, 0x00)
readU32OrSite(readU64_3823OrHigh0; 0x13d3c;
  .Regidx 6#5, x6, rX_x6_run; .Regidx 7#5, x7, rX_x7_run;
  .Regidx 6#5, x6, wX_x6_run; 0x33, 0x63, 0x73, 0x00)
readU32SlliSite(readU64_3823Shift538; 0x13d40, 16;
  .Regidx 28#5, x28, rX_x28_run, wX_x28_run; 0x13, 0x1e, 0x0e, 0x01)
readU32SlliSite(readU64_3823Shift539; 0x13d44, 24;
  .Regidx 29#5, x29, rX_x29_run, wX_x29_run; 0x93, 0x9e, 0x8e, 0x01)
readU32OrSite(readU64_3823OrHigh1; 0x13d48;
  .Regidx 29#5, x29, rX_x29_run; .Regidx 28#5, x28, rX_x28_run;
  .Regidx 7#5, x7, wX_x7_run; 0xb3, 0xe3, 0xce, 0x01)
readU32OrSite(readU64_3823Low; 0x13d54;
  .Regidx 5#5, x5, rX_x5_run; .Regidx 17#5, x17, rX_x17_run;
  .Regidx 15#5, x15, wX_x15_run; 0xb3, 0xe7, 0x12, 0x01)
readU32LiSite(readU64_3823Tag; 0x13d58, 1;
  .Regidx 16#5, x16, wX_x16_run; 0x13, 0x08, 0x10, 0x00)
readU32OrSite(readU64_3823High; 0x13d5c;
  .Regidx 7#5, x7, rX_x7_run; .Regidx 6#5, x6, rX_x6_run;
  .Regidx 17#5, x17, wX_x17_run; 0xb3, 0xe8, 0x63, 0x00)
readU32SlliSite(readU64_3823ShiftHigh; 0x13d60, 32;
  .Regidx 17#5, x17, rX_x17_run, wX_x17_run; 0x93, 0x98, 0x08, 0x02)
readU32OrSite(readU64_3823Result; 0x13d64;
  .Regidx 17#5, x17, rX_x17_run; .Regidx 15#5, x15, rX_x15_run;
  .Regidx 15#5, x15, wX_x15_run; 0xb3, 0xe7, 0xf8, 0x00)

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

/-- The shared high-word fragment completes `fi:1:3203` after its low-word fragment. -/
theorem readU64_3203TailRun (fromStep baseAddress v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (low : ∃ after, Seg readU64_3203OwnPc readU64_3203ExitPc
      (fun _ _ _ _ _ => False) readU64_3203Writes noMemory
      [⟨x5, (Sail.shift_bits_left
          (zero_extend (m := 64) (BitVec.ofNat 8 v3)) 24#64) |||
        (Sail.shift_bits_left (zero_extend (m := 64) (BitVec.ofNat 8 v2)) 16#64)⟩,
       ⟨x17, (Sail.shift_bits_left
          (zero_extend (m := 64) (BitVec.ofNat 8 v1)) 8#64) |||
        zero_extend (m := 64) (BitVec.ofNat 8 v0)⟩,
       ⟨x16, BitVec.ofNat 64 baseAddress⟩]
      fromStep 9 state after (BitVec.ofNat 64 0x12a74))
    (rep4 : UIntRep 1 state.mem (baseAddress + 4) v4)
    (rep5 : UIntRep 1 state.mem (baseAddress + 5) v5)
    (rep6 : UIntRep 1 state.mem (baseAddress + 6) v6)
    (rep7 : UIntRep 1 state.mem (baseAddress + 7) v7)
    (pma : ∀ offset, offset < 8 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : ∀ offset, offset < 8 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sourceFits : baseAddress + 8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU64_3203OwnPc readU64_3203ExitPc (fun _ _ _ _ _ => False)
      readU64_3203Writes noMemory
      [⟨x5, 1⟩, ⟨x16, readU64MachineValue v0 v1 v2 v3 v4 v5 v6 v7⟩]
      fromStep 23 state after (BitVec.ofNat 64 0x12aac) := by
  obtain ⟨afterLow, lowSeg⟩ := low
  exact read_u64_high_compose
    readU64_3203OwnPc, readU64_3203ExitPc, readU64_3203Writes,
    readU64_3203InstructionDisjoint, readU64_3203PlatformDisjoint;
    0x12a74; x16; x17, x5, x6, x7, x28, x16, x5;
    readU64_3203Load5, readU64_3203Load4, readU64_3203Load6, readU64_3203Load7,
    readU64_3203Shift5, readU64_3203OrHigh0, readU64_3203Shift6,
    readU64_3203Shift7, readU64_3203OrHigh1, readU64_3203Low, readU64_3203High,
    readU64_3203ShiftHigh, readU64_3203Result, readU64_3203Tag;
    fromStep, baseAddress, v0, v1, v2, v3, v4, v5, v6, v7, state, configured, lowSeg,
    rep4, rep5, rep6, rep7, pma, notMMIO, sourceFits, loaded

/-- Exact post-address-add schedule for the inlined `fi:1:3203` reader. -/
theorem readU64_3203Run (fromStep baseAddress v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12a50))
    (base : state.regs.get? x16 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem baseAddress v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 1) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 2) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 3) v3)
    (rep4 : UIntRep 1 state.mem (baseAddress + 4) v4)
    (rep5 : UIntRep 1 state.mem (baseAddress + 5) v5)
    (rep6 : UIntRep 1 state.mem (baseAddress + 6) v6)
    (rep7 : UIntRep 1 state.mem (baseAddress + 7) v7)
    (pma : ∀ offset, offset < 8 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : ∀ offset, offset < 8 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sourceFits : baseAddress + 8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU64_3203OwnPc readU64_3203ExitPc (fun _ _ _ _ _ => False)
      readU64_3203Writes noMemory
      [⟨x5, 1⟩, ⟨x16, readU64MachineValue v0 v1 v2 v3 v4 v5 v6 v7⟩]
      fromStep 23 state after (BitVec.ofNat 64 0x12aac) := by
  have low := readU64_3203LowRun fromStep baseAddress v0 v1 v2 v3 state configured
    atPc base rep0 rep1 rep2 rep3
    (fun offset bound => pma offset (by omega))
    (fun offset bound => notMMIO offset (by omega)) (by omega) loaded
  exact readU64_3203TailRun fromStep baseAddress v0 v1 v2 v3 v4 v5 v6 v7 state
    configured low rep4 rep5 rep6 rep7 pma notMMIO sourceFits loaded

/-- Exact alpha-renamed application of the shared schedule at `fi:1:327b`. -/
theorem readU64_327bRun (fromStep baseAddress v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12df8))
    (base : state.regs.get? x12 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem baseAddress v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 1) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 2) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 3) v3)
    (rep4 : UIntRep 1 state.mem (baseAddress + 4) v4)
    (rep5 : UIntRep 1 state.mem (baseAddress + 5) v5)
    (rep6 : UIntRep 1 state.mem (baseAddress + 6) v6)
    (rep7 : UIntRep 1 state.mem (baseAddress + 7) v7)
    (pma : ∀ offset, offset < 8 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : ∀ offset, offset < 8 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sourceFits : baseAddress + 8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU64_327bOwnPc readU64_327bExitPc (fun _ _ _ _ _ => False)
      readU64_327bWrites noMemory
      [⟨x16, 1⟩, ⟨x17, readU64MachineValue v0 v1 v2 v3 v4 v5 v6 v7⟩]
      fromStep 23 state after (BitVec.ofNat 64 0x12e54) := by
  have low : ∃ after, Seg readU64_327bOwnPc readU64_327bExitPc
      (fun _ _ _ _ _ => False) readU64_327bWrites noMemory
      [⟨x14, (Sail.shift_bits_left
          (zero_extend (m := 64) (BitVec.ofNat 8 v3)) 24#64) |||
        (Sail.shift_bits_left (zero_extend (m := 64) (BitVec.ofNat 8 v2)) 16#64)⟩,
       ⟨x13, (Sail.shift_bits_left
          (zero_extend (m := 64) (BitVec.ofNat 8 v1)) 8#64) |||
        zero_extend (m := 64) (BitVec.ofNat 8 v0)⟩,
       ⟨x12, BitVec.ofNat 64 baseAddress⟩]
      fromStep 9 state after (BitVec.ofNat 64 0x12e1c) :=
    read_u64_low_compose
      readU64_327bOwnPc, readU64_327bExitPc, readU64_327bWrites,
      readU64_327bInstructionDisjoint, readU64_327bPlatformDisjoint;
      0x12df8; x12; x13, x14, x15, x16;
      readU64_327bLoad1, readU64_327bLoad2, readU64_327bLoad3, readU64_327bLoad0,
      readU64_327bShift1, readU64_327bShift2, readU64_327bShift3,
      readU64_327bOrLow0, readU64_327bOrLow1;
      fromStep, baseAddress, v0, v1, v2, v3, state, configured, atPc, base,
      rep0, rep1, rep2, rep3,
      (fun offset (bound : offset < 4) => pma offset (by omega)),
      (fun offset (bound : offset < 4) => notMMIO offset (by omega)), (by omega), loaded
  obtain ⟨afterLow, lowSeg⟩ := low
  exact read_u64_high_compose
    readU64_327bOwnPc, readU64_327bExitPc, readU64_327bWrites,
    readU64_327bInstructionDisjoint, readU64_327bPlatformDisjoint;
    0x12e1c; x12; x13, x14, x15, x16, x17, x17, x16;
    readU64_327bLoad5, readU64_327bLoad4, readU64_327bLoad6, readU64_327bLoad7,
    readU64_327bShift5, readU64_327bOrHigh0, readU64_327bShift6,
    readU64_327bShift7, readU64_327bOrHigh1, readU64_327bLow, readU64_327bHigh,
    readU64_327bShiftHigh, readU64_327bResult, readU64_327bTag;
    fromStep, baseAddress, v0, v1, v2, v3, v4, v5, v6, v7, state, configured, lowSeg,
    rep4, rep5, rep6, rep7, pma, notMMIO, sourceFits, loaded

end BinaryFv.Zesu.MachineExecution
