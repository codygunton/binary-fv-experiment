namespace ShaFv.RISCV

/-- RV64 words are represented as natural numbers until their no-wrap proofs are discharged. -/
abbrev Word := Nat

def addressLimit : Nat := 2 ^ 64

def maxMessageSize : Nat := 2 ^ 63

/-- Convert a proved in-range natural address or value to its non-wrapping RV64 representation. -/
def rv64Word (value : Nat) (_fits64 : value < addressLimit) : BitVec 64 :=
  BitVec.ofNat 64 value

theorem rv64Word_toNat (value : Nat) (fits64 : value < addressLimit) :
    (rv64Word value fits64).toNat = value := by
  unfold rv64Word
  calc
    (BitVec.ofNat 64 value).toNat = value % 2 ^ 64 := BitVec.toNat_ofNat value 64
    _ = value := Nat.mod_eq_of_lt (by simpa [addressLimit] using fits64)

structure AddressRange where
  start : Nat
  size : Nat
deriving DecidableEq, Repr

namespace AddressRange

def stop (range : AddressRange) : Nat := range.start + range.size

def fits64 (range : AddressRange) : Prop := range.stop ≤ addressLimit

/-- Half-open ranges are disjoint when one ends before the other begins. -/
def disjoint (left right : AddressRange) : Prop :=
  left.stop ≤ right.start ∨ right.stop ≤ left.start

def containedIn (range container : AddressRange) : Prop :=
  container.start ≤ range.start ∧ range.stop ≤ container.stop

theorem containedIn_trans {first second third : AddressRange}
    (firstH : first.containedIn second) (secondH : second.containedIn third) :
    first.containedIn third :=
  ⟨Nat.le_trans secondH.1 firstH.1, Nat.le_trans firstH.2 secondH.2⟩

end AddressRange

/-- Gate 2 must prove that every loadable ELF segment lies in this virtual-address window. -/
def sha3CodeWindow : AddressRange := ⟨0x10000, 0x8000⟩

/-- The runner stops at this sentinel before attempting to fetch an instruction there. -/
def returnAddress : Word := 0x18000

def returnSentinelRange : AddressRange := ⟨returnAddress, 4⟩

def digestSize : Nat := 32

def outputAddress : Word := 0x20000

def outputRange : AddressRange := ⟨outputAddress, digestSize⟩

def messageAddress : Word := 0x100000

def messageRange (messageSize : Nat) : AddressRange := ⟨messageAddress, messageSize⟩

def stackTop : Word := 0xfffffffffffff000

def stackPageSize : Nat := 0x1000

def stackRange : AddressRange := ⟨stackTop - stackPageSize, stackPageSize⟩

def observedNestedStackUse : Nat := 752

def lowPmaRange : AddressRange := ⟨0, 0x8000000000100000⟩

def highPmaRange : AddressRange := stackRange

theorem lowPmaRange_wordBounds :
    lowPmaRange.start < addressLimit ∧ lowPmaRange.size < addressLimit := by
  exact ⟨by decide, by decide⟩

theorem highPmaRange_wordBounds :
    highPmaRange.start < addressLimit ∧ highPmaRange.size < addressLimit := by
  exact ⟨by decide, by decide⟩

theorem sha3CodeWindow_fits64 : sha3CodeWindow.fits64 := by
  change 0x10000 + 0x8000 ≤ 2 ^ 64
  decide

theorem returnSentinelRange_fits64 : returnSentinelRange.fits64 := by
  change 0x18000 + 4 ≤ 2 ^ 64
  decide

theorem outputRange_fits64 : outputRange.fits64 := by
  change 0x20000 + digestSize ≤ 2 ^ 64
  decide

theorem stackRange_fits64 : stackRange.fits64 := by
  change stackTop - stackPageSize + stackPageSize ≤ 2 ^ 64
  decide

theorem codeWindow_before_returnSentinel : sha3CodeWindow.stop ≤ returnSentinelRange.start := by
  decide

theorem codeWindow_before_output : sha3CodeWindow.stop ≤ outputRange.start := by
  decide

theorem codeWindow_before_message : sha3CodeWindow.stop ≤ messageAddress := by
  decide

theorem codeWindow_before_stack : sha3CodeWindow.stop ≤ stackRange.start := by
  decide

theorem returnSentinel_before_output : returnSentinelRange.stop ≤ outputRange.start := by
  decide

theorem returnSentinel_before_message : returnSentinelRange.stop ≤ messageAddress := by
  decide

theorem returnSentinel_before_stack : returnSentinelRange.stop ≤ stackRange.start := by
  decide

theorem output_before_message : outputRange.stop ≤ messageAddress := by
  decide

theorem output_before_stack : outputRange.stop ≤ stackRange.start := by
  decide

theorem sha3CodeWindow_within_lowPma : sha3CodeWindow.containedIn lowPmaRange := by
  change 0 ≤ 0x10000 ∧ 0x10000 + 0x8000 ≤ 0 + 0x8000000000100000
  decide

theorem returnSentinelRange_within_lowPma : returnSentinelRange.containedIn lowPmaRange := by
  change 0 ≤ returnAddress ∧ returnAddress + 4 ≤ 0 + 0x8000000000100000
  decide

theorem outputRange_within_lowPma : outputRange.containedIn lowPmaRange := by
  change 0 ≤ outputAddress ∧ outputAddress + digestSize ≤ 0 + 0x8000000000100000
  decide

theorem stackRange_within_highPma : stackRange.containedIn highPmaRange :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem pmaRanges_disjoint : lowPmaRange.disjoint highPmaRange := by
  change 0 + 0x8000000000100000 ≤ stackTop - stackPageSize ∨
    stackTop - stackPageSize + stackPageSize ≤ 0
  exact Or.inl (by decide)

theorem stackTop_aligned : stackTop % 16 = 0 := by
  decide

theorem observedNestedStackUse_fits : observedNestedStackUse ≤ stackPageSize := by
  decide

theorem messageRange_stop_lt_addressLimit {messageSize : Nat}
    (messageH : messageSize < maxMessageSize) :
    (messageRange messageSize).stop < addressLimit := by
  change messageAddress + messageSize < addressLimit
  calc
    messageAddress + messageSize ≤ messageAddress + (maxMessageSize - 1) :=
      Nat.add_le_add_left (Nat.le_sub_one_of_lt messageH) _
    _ < addressLimit := by decide

theorem messageRange_fits64 {messageSize : Nat} (messageH : messageSize < maxMessageSize) :
    (messageRange messageSize).fits64 :=
  Nat.le_of_lt <| messageRange_stop_lt_addressLimit messageH

theorem messageRange_stop_lt_lowPma {messageSize : Nat}
    (messageH : messageSize < maxMessageSize) :
    (messageRange messageSize).stop < lowPmaRange.stop := by
  change messageAddress + messageSize < lowPmaRange.stop
  calc
    messageAddress + messageSize ≤ messageAddress + (maxMessageSize - 1) :=
      Nat.add_le_add_left (Nat.le_sub_one_of_lt messageH) _
    _ < lowPmaRange.stop := by decide

theorem messageRange_within_lowPma {messageSize : Nat}
    (messageH : messageSize < maxMessageSize) :
    (messageRange messageSize).containedIn lowPmaRange := by
  refine ⟨Nat.zero_le _, Nat.le_of_lt <| messageRange_stop_lt_lowPma messageH⟩

theorem messageRange_before_stack {messageSize : Nat}
    (messageH : messageSize < maxMessageSize) :
    (messageRange messageSize).stop ≤ stackRange.start := by
  change messageAddress + messageSize ≤ stackRange.start
  calc
    messageAddress + messageSize ≤ messageAddress + (maxMessageSize - 1) :=
      Nat.add_le_add_left (Nat.le_sub_one_of_lt messageH) _
    _ ≤ stackRange.start := by decide

def codePlacement (code : AddressRange) : Prop :=
  code.fits64 ∧ code.containedIn sha3CodeWindow

theorem codePlacement_within_lowPma {code : AddressRange}
    (codeH : codePlacement code) : code.containedIn lowPmaRange :=
  AddressRange.containedIn_trans codeH.2 sha3CodeWindow_within_lowPma

structure Sha3Layout where
  code : AddressRange
  returnSentinel : AddressRange
  output : AddressRange
  message : AddressRange
  stack : AddressRange

def sha3Layout (code : AddressRange) (messageSize : Nat) : Sha3Layout where
  code := code
  returnSentinel := returnSentinelRange
  output := outputRange
  message := messageRange messageSize
  stack := stackRange

def Sha3Layout.wellFormed (layout : Sha3Layout) : Prop :=
  layout.code.fits64 ∧
    layout.returnSentinel.fits64 ∧
      layout.output.fits64 ∧
        layout.message.fits64 ∧
          layout.stack.fits64 ∧
            layout.code.disjoint layout.returnSentinel ∧
              layout.code.disjoint layout.output ∧
                layout.code.disjoint layout.message ∧
                  layout.code.disjoint layout.stack ∧
                    layout.returnSentinel.disjoint layout.output ∧
                      layout.returnSentinel.disjoint layout.message ∧
                        layout.returnSentinel.disjoint layout.stack ∧
                          layout.output.disjoint layout.message ∧
                            layout.output.disjoint layout.stack ∧
                              layout.message.disjoint layout.stack

def Sha3Layout.pmaCovered (layout : Sha3Layout) : Prop :=
  layout.code.containedIn lowPmaRange ∧
    layout.returnSentinel.containedIn lowPmaRange ∧
      layout.output.containedIn lowPmaRange ∧
        layout.message.containedIn lowPmaRange ∧ layout.stack.containedIn highPmaRange

theorem sha3Layout_wellFormed {code : AddressRange} {messageSize : Nat}
    (codeH : codePlacement code) (messageH : messageSize < maxMessageSize) :
    (sha3Layout code messageSize).wellFormed := by
  change
    code.fits64 ∧
      returnSentinelRange.fits64 ∧
        outputRange.fits64 ∧
          (messageRange messageSize).fits64 ∧
            stackRange.fits64 ∧
              code.disjoint returnSentinelRange ∧
                code.disjoint outputRange ∧
                  code.disjoint (messageRange messageSize) ∧
                    code.disjoint stackRange ∧
                      returnSentinelRange.disjoint outputRange ∧
                        returnSentinelRange.disjoint (messageRange messageSize) ∧
                          returnSentinelRange.disjoint stackRange ∧
                            outputRange.disjoint (messageRange messageSize) ∧
                              outputRange.disjoint stackRange ∧
                                (messageRange messageSize).disjoint stackRange
  refine ⟨codeH.1, returnSentinelRange_fits64, outputRange_fits64, messageRange_fits64 messageH,
    stackRange_fits64, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl <| Nat.le_trans codeH.2.2 codeWindow_before_returnSentinel
  · exact Or.inl <| Nat.le_trans codeH.2.2 codeWindow_before_output
  · exact Or.inl <| Nat.le_trans codeH.2.2 codeWindow_before_message
  · exact Or.inl <| Nat.le_trans codeH.2.2 codeWindow_before_stack
  · exact Or.inl returnSentinel_before_output
  · exact Or.inl returnSentinel_before_message
  · exact Or.inl returnSentinel_before_stack
  · exact Or.inl output_before_message
  · exact Or.inl output_before_stack
  · exact Or.inl <| messageRange_before_stack messageH

theorem sha3Layout_pmaCovered {code : AddressRange} {messageSize : Nat}
    (codeH : codePlacement code) (messageH : messageSize < maxMessageSize) :
    (sha3Layout code messageSize).pmaCovered := by
  change
    code.containedIn lowPmaRange ∧
      returnSentinelRange.containedIn lowPmaRange ∧
        outputRange.containedIn lowPmaRange ∧
          (messageRange messageSize).containedIn lowPmaRange ∧
            stackRange.containedIn highPmaRange
  exact ⟨codePlacement_within_lowPma codeH, returnSentinelRange_within_lowPma,
    outputRange_within_lowPma, messageRange_within_lowPma messageH, stackRange_within_highPma⟩

structure Sha3Abi where
  ra : Word
  sp : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
deriving DecidableEq, Repr

def sha3Abi (messageSize : Nat) : Sha3Abi where
  ra := returnAddress
  sp := stackTop
  a0 := messageAddress
  a1 := messageSize
  a2 := outputAddress
  a3 := digestSize

theorem sha3Abi_registers (messageSize : Nat) :
    (sha3Abi messageSize).ra = returnAddress ∧
      (sha3Abi messageSize).sp = stackTop ∧
        (sha3Abi messageSize).a0 = messageAddress ∧
          (sha3Abi messageSize).a1 = messageSize ∧
            (sha3Abi messageSize).a2 = outputAddress ∧ (sha3Abi messageSize).a3 = digestSize := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def Sha3Abi.wellFormed (abi : Sha3Abi) : Prop :=
  abi.ra < addressLimit ∧
    abi.sp < addressLimit ∧
      abi.a0 < addressLimit ∧
        abi.a1 < addressLimit ∧ abi.a2 < addressLimit ∧ abi.a3 < addressLimit

theorem sha3Abi_wellFormed {messageSize : Nat} (messageH : messageSize < maxMessageSize) :
    (sha3Abi messageSize).wellFormed := by
  change
    returnAddress < addressLimit ∧
      stackTop < addressLimit ∧
        messageAddress < addressLimit ∧
          messageSize < addressLimit ∧ outputAddress < addressLimit ∧ digestSize < addressLimit
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide⟩
  exact Nat.lt_trans messageH (by decide)

structure Sha3Call where
  pc : Word
  registers : Sha3Abi
deriving DecidableEq, Repr

def sha3Call (sha3Symbol : Word) (messageSize : Nat) : Sha3Call where
  pc := sha3Symbol
  registers := sha3Abi messageSize

def Sha3Call.wellFormed (call : Sha3Call) : Prop :=
  call.pc < addressLimit ∧ call.registers.wellFormed

theorem sha3Call_wellFormed {sha3Symbol messageSize : Nat}
    (symbolH : sha3Symbol < addressLimit) (messageH : messageSize < maxMessageSize) :
    (sha3Call sha3Symbol messageSize).wellFormed :=
  ⟨symbolH, sha3Abi_wellFormed messageH⟩

end ShaFv.RISCV
