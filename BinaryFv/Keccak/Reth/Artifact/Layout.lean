import BinaryFv.RiscV.Model.Address

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

def digestSize : Nat := 32

/-- The largest message the direct-call ABI accepts; it bounds the low PMA region. -/
def maxMessageSize : Nat := 2 ^ 63

/-- Keep the sentinel and caller-owned buffers outside the parsed load image. -/
def returnGap : Nat := 0x10

def outputGap : Nat := 0x1000

def messageGap : Nat := 0x2000

def stackPageSize : Nat := 0x1000

def stackTop : Word := addressLimit - stackPageSize

def lowPmaRange : AddressRange := ⟨0, maxMessageSize + 0x100000⟩

def stackRange : AddressRange := ⟨stackTop - stackPageSize, stackPageSize⟩

def returnAddress (code : AddressRange) : Word := code.stop + returnGap

def returnSentinelRange (code : AddressRange) : AddressRange :=
  ⟨returnAddress code, 4⟩

def outputAddress (code : AddressRange) : Word := code.stop + outputGap

def outputRange (code : AddressRange) : AddressRange :=
  ⟨outputAddress code, digestSize⟩

def messageAddress (code : AddressRange) : Word := code.stop + messageGap

def messageRange (code : AddressRange) (messageSize : Nat) : AddressRange :=
  ⟨messageAddress code, messageSize⟩

structure KeccakLayout where
  code : AddressRange
  returnSentinel : AddressRange
  output : AddressRange
  message : AddressRange
  stack : AddressRange
deriving Repr

def keccakLayout (code : AddressRange) (messageSize : Nat) : KeccakLayout where
  code
  returnSentinel := returnSentinelRange code
  output := outputRange code
  message := messageRange code messageSize
  stack := stackRange

def KeccakLayout.wellFormed (layout : KeccakLayout) : Prop :=
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

def KeccakLayout.pmaCovered (layout : KeccakLayout) : Prop :=
  layout.code.containedIn lowPmaRange ∧
    layout.returnSentinel.containedIn lowPmaRange ∧
      layout.output.containedIn lowPmaRange ∧
        layout.message.containedIn lowPmaRange ∧ layout.stack.containedIn stackRange

/-- A target-specific artifact establishes these bounds from its parsed load image. -/
def codePlacement (code : AddressRange) : Prop :=
  code.fits64 ∧
    code.containedIn lowPmaRange ∧
      code.stop + messageGap + maxMessageSize ≤ lowPmaRange.stop

instance : DecidablePred codePlacement := fun code => by
  unfold codePlacement AddressRange.fits64 AddressRange.containedIn AddressRange.stop
  infer_instance

theorem lowPmaRange_fits64 : lowPmaRange.fits64 := by
  change 0 + (2 ^ 63 + 0x100000) ≤ 2 ^ 64
  decide

theorem stackRange_fits64 : stackRange.fits64 := by
  change (2 ^ 64 - 0x1000 - 0x1000) + 0x1000 ≤ 2 ^ 64
  decide

theorem stackTop_aligned : stackTop % 16 = 0 := by
  decide

theorem lowPma_before_stack : lowPmaRange.stop ≤ stackRange.start := by
  change 0 + (2 ^ 63 + 0x100000) ≤ 2 ^ 64 - 0x1000 - 0x1000
  decide

theorem keccakLayout_wellFormed {code : AddressRange} {messageSize : Nat}
    (codeH : codePlacement code) (messageH : messageSize < maxMessageSize) :
    (keccakLayout code messageSize).wellFormed := by
  rcases codeH with ⟨codeFits, codeLow, codeMessageBound⟩
  have messageLe : messageSize ≤ maxMessageSize := Nat.le_of_lt messageH
  have maxMessageSizePositive : 0 < maxMessageSize := by
    change 0 < 2 ^ 63
    decide
  have returnBeforeMessage : returnGap + 4 ≤ messageGap := by
    change 0x10 + 4 ≤ 0x2000
    decide
  have outputBeforeMessage : outputGap + digestSize ≤ messageGap := by
    change 0x1000 + 32 ≤ 0x2000
    decide
  have returnBeforeOutput : returnGap + 4 ≤ outputGap := by
    change 0x10 + 4 ≤ 0x1000
    decide
  have lowFits : lowPmaRange.stop ≤ addressLimit := lowPmaRange_fits64
  have returnStopLow : (returnSentinelRange code).stop ≤ lowPmaRange.stop := by
    change code.stop + returnGap + 4 ≤ lowPmaRange.stop
    omega
  have outputStopLow : (outputRange code).stop ≤ lowPmaRange.stop := by
    change code.stop + outputGap + digestSize ≤ lowPmaRange.stop
    omega
  have messageStopLow : (messageRange code messageSize).stop ≤ lowPmaRange.stop := by
    change code.stop + messageGap + messageSize ≤ lowPmaRange.stop
    omega
  have returnFits : (returnSentinelRange code).fits64 := by
    change (returnSentinelRange code).stop ≤ addressLimit
    omega
  have outputFits : (outputRange code).fits64 := by
    change (outputRange code).stop ≤ addressLimit
    omega
  have messageFits : (messageRange code messageSize).fits64 := by
    change (messageRange code messageSize).stop ≤ addressLimit
    omega
  change
    code.fits64 ∧
      (returnSentinelRange code).fits64 ∧
        (outputRange code).fits64 ∧
          (messageRange code messageSize).fits64 ∧
            stackRange.fits64 ∧
              code.disjoint (returnSentinelRange code) ∧
                code.disjoint (outputRange code) ∧
                  code.disjoint (messageRange code messageSize) ∧
                    code.disjoint stackRange ∧
                      (returnSentinelRange code).disjoint (outputRange code) ∧
                        (returnSentinelRange code).disjoint (messageRange code messageSize) ∧
                          (returnSentinelRange code).disjoint stackRange ∧
                            (outputRange code).disjoint (messageRange code messageSize) ∧
                              (outputRange code).disjoint stackRange ∧
                                (messageRange code messageSize).disjoint stackRange
  refine ⟨codeFits, returnFits, outputFits, messageFits, stackRange_fits64, Or.inl ?_, Or.inl ?_,
    Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_⟩
  · change code.stop ≤ code.stop + returnGap
    omega
  · change code.stop ≤ code.stop + outputGap
    omega
  · change code.stop ≤ code.stop + messageGap
    omega
  · exact Nat.le_trans codeLow.2 lowPma_before_stack
  · change code.stop + returnGap + 4 ≤ code.stop + outputGap
    omega
  · change code.stop + returnGap + 4 ≤ code.stop + messageGap
    omega
  · exact Nat.le_trans returnStopLow lowPma_before_stack
  · change code.stop + outputGap + digestSize ≤ code.stop + messageGap
    omega
  · exact Nat.le_trans outputStopLow lowPma_before_stack
  · exact Nat.le_trans messageStopLow lowPma_before_stack

theorem keccakLayout_pmaCovered {code : AddressRange} {messageSize : Nat}
    (codeH : codePlacement code) (messageH : messageSize < maxMessageSize) :
    (keccakLayout code messageSize).pmaCovered := by
  rcases codeH with ⟨_codeFits, codeLow, codeMessageBound⟩
  have messageLe : messageSize ≤ maxMessageSize := Nat.le_of_lt messageH
  have maxMessageSizePositive : 0 < maxMessageSize := by
    change 0 < 2 ^ 63
    decide
  have returnBeforeMessage : returnGap + 4 ≤ messageGap := by
    change 0x10 + 4 ≤ 0x2000
    decide
  have outputBeforeMessage : outputGap + digestSize ≤ messageGap := by
    change 0x1000 + 32 ≤ 0x2000
    decide
  have returnStopLow : (returnSentinelRange code).stop ≤ lowPmaRange.stop := by
    change code.stop + returnGap + 4 ≤ lowPmaRange.stop
    omega
  have outputStopLow : (outputRange code).stop ≤ lowPmaRange.stop := by
    change code.stop + outputGap + digestSize ≤ lowPmaRange.stop
    omega
  have messageStopLow : (messageRange code messageSize).stop ≤ lowPmaRange.stop := by
    change code.stop + messageGap + messageSize ≤ lowPmaRange.stop
    omega
  change
    code.containedIn lowPmaRange ∧
      (returnSentinelRange code).containedIn lowPmaRange ∧
        (outputRange code).containedIn lowPmaRange ∧
          (messageRange code messageSize).containedIn lowPmaRange ∧
            stackRange.containedIn stackRange
  refine ⟨codeLow, ?_, ?_, ?_, ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
  · exact ⟨Nat.zero_le _, returnStopLow⟩
  · exact ⟨Nat.zero_le _, outputStopLow⟩
  · exact ⟨Nat.zero_le _, messageStopLow⟩

structure KeccakAbi where
  ra : Word
  sp : Word
  a0 : Word
  a1 : Word
  a2 : Word
deriving DecidableEq, Repr

def keccakAbi (code : AddressRange) (messageSize : Nat) : KeccakAbi where
  ra := returnAddress code
  sp := stackTop
  a0 := messageAddress code
  a1 := messageSize
  a2 := outputAddress code

theorem keccakAbi_registers (code : AddressRange) (messageSize : Nat) :
    (keccakAbi code messageSize).ra = returnAddress code ∧
      (keccakAbi code messageSize).sp = stackTop ∧
        (keccakAbi code messageSize).a0 = messageAddress code ∧
          (keccakAbi code messageSize).a1 = messageSize ∧
            (keccakAbi code messageSize).a2 = outputAddress code := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end BinaryFv.Keccak
