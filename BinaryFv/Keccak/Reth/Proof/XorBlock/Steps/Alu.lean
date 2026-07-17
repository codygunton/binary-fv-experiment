import BinaryFv.Keccak.Reth.Proof.XorBlock.Framing

/-!
# `xor_block` register-only body steps (`slli` / `or` / `xor` / ...)
-/

namespace BinaryFv.Keccak.XorBlock
open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 2a: register-only body step lemmas (slli / or / xor / addi) -/

theorem step_slli_10c84 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c84) 0x93#8 0x96#8 0x86#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)).regs.get? x13 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)).regs.insert x13 (v1 <<< 8) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c84) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x96#8 0x86#8 0x00#8 = (0x00869693 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x96#8 0x86#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a3_8_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)) _ (13#5) (8#6) v1
    (rX_x13_run _ v1 hv1) (wX_x13_run _ (v1 <<< (8#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c84) retired mseccfgBits inhibit config
    0x93#8 0x96#8 0x86#8 0x00#8 (.SHIFTIOP (8#6, .Regidx 13#5, .Regidx 13#5, .SLLI))
    x13 (v1 <<< 8) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10c88 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c88) 0x13#8 0x17#8 0x07#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)).regs.get? x14 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)).regs.insert x14 (v1 <<< 16) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c88) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x17#8 0x07#8 0x01#8 = (0x01071713 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x17#8 0x07#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 14#5, .Regidx 14#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a4_16_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)) _ (14#5) (16#6) v1
    (rX_x14_run _ v1 hv1) (wX_x14_run _ (v1 <<< (16#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c88) retired mseccfgBits inhibit config
    0x13#8 0x17#8 0x07#8 0x01#8 (.SHIFTIOP (16#6, .Regidx 14#5, .Regidx 14#5, .SLLI))
    x14 (v1 <<< 16) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10c8c (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c8c) 0x93#8 0x97#8 0x87#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)).regs.get? x15 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)).regs.insert x15 (v1 <<< 24) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c8c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x97#8 0x87#8 0x01#8 = (0x01879793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x87#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a5_24_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)) _ (15#5) (24#6) v1
    (rX_x15_run _ v1 hv1) (wX_x15_run _ (v1 <<< (24#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c8c) retired mseccfgBits inhibit config
    0x93#8 0x97#8 0x87#8 0x01#8 (.SHIFTIOP (24#6, .Regidx 15#5, .Regidx 15#5, .SLLI))
    x15 (v1 <<< 24) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10ca8 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ca8) 0x93#8 0x97#8 0x87#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)).regs.get? x15 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)).regs.insert x15 (v1 <<< 8) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca8) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x97#8 0x87#8 0x00#8 = (0x00879793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x87#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a5_8_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)) _ (15#5) (8#6) v1
    (rX_x15_run _ v1 hv1) (wX_x15_run _ (v1 <<< (8#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ca8) retired mseccfgBits inhibit config
    0x93#8 0x97#8 0x87#8 0x00#8 (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI))
    x15 (v1 <<< 8) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10cb0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cb0) 0x93#8 0x98#8 0x08#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)).regs.get? x17 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)).regs.insert x17 (v1 <<< 16) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x98#8 0x08#8 0x01#8 = (0x01089893 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x98#8 0x08#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 17#5, .Regidx 17#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a7_16_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)) _ (17#5) (16#6) v1
    (rX_x17_run _ v1 hv1) (wX_x17_run _ (v1 <<< (16#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cb0) retired mseccfgBits inhibit config
    0x93#8 0x98#8 0x08#8 0x01#8 (.SHIFTIOP (16#6, .Regidx 17#5, .Regidx 17#5, .SLLI))
    x17 (v1 <<< 16) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10cb4 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cb4) 0x93#8 0x92#8 0x82#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)).regs.get? x5 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)).regs.insert x5 (v1 <<< 24) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x92#8 0x82#8 0x01#8 = (0x01829293 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x92#8 0x82#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 5#5, .Regidx 5#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_t0_24_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)) _ (5#5) (24#6) v1
    (rX_x5_run _ v1 hv1) (wX_x5_run _ (v1 <<< (24#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cb4) retired mseccfgBits inhibit config
    0x93#8 0x92#8 0x82#8 0x01#8 (.SHIFTIOP (24#6, .Regidx 5#5, .Regidx 5#5, .SLLI))
    x5 (v1 <<< 24) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10cd0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cd0) 0x93#8 0x97#8 0x07#8 0x02#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)).regs.get? x15 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)).regs.insert x15 (v1 <<< 32) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x97#8 0x07#8 0x02#8 = (0x02079793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x07#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (32#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a5_32_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)) _ (15#5) (32#6) v1
    (rX_x15_run _ v1 hv1) (wX_x15_run _ (v1 <<< (32#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cd0) retired mseccfgBits inhibit config
    0x93#8 0x97#8 0x07#8 0x02#8 (.SHIFTIOP (32#6, .Regidx 15#5, .Regidx 15#5, .SLLI))
    x15 (v1 <<< 32) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10c90 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c90) 0xb3#8 0xe6#8 0x06#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)).regs.get? x13 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)).regs.get? x16 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)).regs.insert x13 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c90) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0xe6#8 0x06#8 0x01#8 = (0x0106e6b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe6#8 0x06#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 16#5, .Regidx 13#5, .Regidx 13#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a3_a3_a6_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)) _ (16#5) (13#5) (13#5) v1 v2
    (rX_x13_run _ v1 hv1) (rX_x16_run _ v2 hv2) (wX_x13_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c90) retired mseccfgBits inhibit config
    0xb3#8 0xe6#8 0x06#8 0x01#8 (.RTYPE (.Regidx 16#5, .Regidx 13#5, .Regidx 13#5, .OR))
    x13 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10c94 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c94) 0x33#8 0xe7#8 0xe7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)).regs.get? x15 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)).regs.get? x14 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)).regs.insert x14 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c94) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x33#8 0xe7#8 0xe7#8 0x00#8 = (0x00e7e733 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe7#8 0xe7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a4_a5_a4_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)) _ (14#5) (15#5) (14#5) v1 v2
    (rX_x15_run _ v1 hv1) (rX_x14_run _ v2 hv2) (wX_x14_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c94) retired mseccfgBits inhibit config
    0x33#8 0xe7#8 0xe7#8 0x00#8 (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR))
    x14 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cac (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cac) 0xb3#8 0xe7#8 0x07#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)).regs.get? x15 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)).regs.get? x16 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)).regs.insert x15 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cac) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0xe7#8 0x07#8 0x01#8 = (0x0107e7b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe7#8 0x07#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 16#5, .Regidx 15#5, .Regidx 15#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a5_a5_a6_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)) _ (16#5) (15#5) (15#5) v1 v2
    (rX_x15_run _ v1 hv1) (rX_x16_run _ v2 hv2) (wX_x15_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cac) retired mseccfgBits inhibit config
    0xb3#8 0xe7#8 0x07#8 0x01#8 (.RTYPE (.Regidx 16#5, .Regidx 15#5, .Regidx 15#5, .OR))
    x15 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cb8 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cb8) 0x33#8 0xe8#8 0x12#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)).regs.get? x5 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)).regs.get? x17 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)).regs.insert x16 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb8) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x33#8 0xe8#8 0x12#8 0x01#8 = (0x0112e833 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe8#8 0x12#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 17#5, .Regidx 5#5, .Regidx 16#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a6_t0_a7_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)) _ (17#5) (5#5) (16#5) v1 v2
    (rX_x5_run _ v1 hv1) (rX_x17_run _ v2 hv2) (wX_x16_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cb8) retired mseccfgBits inhibit config
    0x33#8 0xe8#8 0x12#8 0x01#8 (.RTYPE (.Regidx 17#5, .Regidx 5#5, .Regidx 16#5, .OR))
    x16 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cc4 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cc4) 0xb3#8 0x66#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)).regs.get? x14 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)).regs.get? x13 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)).regs.insert x13 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0x66#8 0xd7#8 0x00#8 = (0x00d766b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x66#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a3_a4_a3_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)) _ (13#5) (14#5) (13#5) v1 v2
    (rX_x14_run _ v1 hv1) (rX_x13_run _ v2 hv2) (wX_x13_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cc4) retired mseccfgBits inhibit config
    0xb3#8 0x66#8 0xd7#8 0x00#8 (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .OR))
    x13 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10ccc (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ccc) 0xb3#8 0x67#8 0xf8#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)).regs.get? x16 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)).regs.get? x15 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)).regs.insert x15 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ccc) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0x67#8 0xf8#8 0x00#8 = (0x00f867b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x67#8 0xf8#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 16#5, .Regidx 15#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a5_a6_a5_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)) _ (15#5) (16#5) (15#5) v1 v2
    (rX_x16_run _ v1 hv1) (rX_x15_run _ v2 hv2) (wX_x15_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ccc) retired mseccfgBits inhibit config
    0xb3#8 0x67#8 0xf8#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 16#5, .Regidx 15#5, .OR))
    x15 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cd4 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cd4) 0xb3#8 0xe6#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)).regs.get? x15 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)).regs.get? x13 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)).regs.insert x13 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0xe6#8 0xd7#8 0x00#8 = (0x00d7e6b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe6#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 15#5, .Regidx 13#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a3_a5_a3_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)) _ (13#5) (15#5) (13#5) v1 v2
    (rX_x15_run _ v1 hv1) (rX_x13_run _ v2 hv2) (wX_x13_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cd4) retired mseccfgBits inhibit config
    0xb3#8 0xe6#8 0xd7#8 0x00#8 (.RTYPE (.Regidx 13#5, .Regidx 15#5, .Regidx 13#5, .OR))
    x13 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_xor_10cd8 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cd8) 0xb3#8 0x46#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)).regs.get? x14 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)).regs.get? x13 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)).regs.insert x13 (v1 ^^^ v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd8) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0x46#8 0xd7#8 0x00#8 = (0x00d746b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x46#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .XOR)) := by
    rw [wordEq]; exact ext_decode_xor_a3_a4_a3_run _ privRead mseccfgBits mseccfgRead
  have exec := xorExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)) _ (13#5) (14#5) (13#5) v1 v2
    (rX_x14_run _ v1 hv1) (rX_x13_run _ v2 hv2) (wX_x13_run _ (v1 ^^^ v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cd8) retired mseccfgBits inhibit config
    0xb3#8 0x46#8 0xd7#8 0x00#8 (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .XOR))
    x13 (v1 ^^^ v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_addi_10cbc (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cbc) 0x13#8 0x06#8 0x86#8 0xff#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)).regs.get? x12 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)).regs.insert x12 (v1 + sign_extend (m := 64) 0xff8#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cbc) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x06#8 0x86#8 0xff#8 = (0xff860613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x86#8 0xff#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xff8#12, .Regidx 12#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a2_a2_m8_run _ privRead mseccfgBits mseccfgRead
  have exec := addiExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)) _ (0xff8#12) (12#5) v1
    (rX_x12_run _ v1 hv1) (wX_x12_run _ (v1 + sign_extend (m := 64) 0xff8#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cbc) retired mseccfgBits inhibit config
    0x13#8 0x06#8 0x86#8 0xff#8 (.ITYPE (0xff8#12, .Regidx 12#5, .Regidx 12#5, .ADDI))
    x12 (v1 + sign_extend (m := 64) 0xff8#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_addi_10cc0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cc0) 0x93#8 0x85#8 0x85#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)).regs.get? x11 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)).regs.insert x11 (v1 + sign_extend (m := 64) 8#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x85#8 0x85#8 0x00#8 = (0x00858593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x85#8 0x85#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (8#12, .Regidx 11#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a1_a1_8_run _ privRead mseccfgBits mseccfgRead
  have exec := addiExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)) _ (8#12) (11#5) v1
    (rX_x11_run _ v1 hv1) (wX_x11_run _ (v1 + sign_extend (m := 64) 8#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cc0) retired mseccfgBits inhibit config
    0x93#8 0x85#8 0x85#8 0x00#8 (.ITYPE (8#12, .Regidx 11#5, .Regidx 11#5, .ADDI))
    x11 (v1 + sign_extend (m := 64) 8#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_addi_10ce0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce0) 0x13#8 0x05#8 0x85#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)).regs.get? x10 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)).regs.insert x10 (v1 + sign_extend (m := 64) 8#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x05#8 0x85#8 0x00#8 = (0x00850513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x85#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (8#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a0_a0_8_run _ privRead mseccfgBits mseccfgRead
  have exec := addiExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)) _ (8#12) (10#5) v1
    (rX_x10_run _ v1 hv1) (wX_x10_run _ (v1 + sign_extend (m := 64) 8#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ce0) retired mseccfgBits inhibit config
    0x13#8 0x05#8 0x85#8 0x00#8 (.ITYPE (8#12, .Regidx 10#5, .Regidx 10#5, .ADDI))
    x10 (v1 + sign_extend (m := 64) 8#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

end BinaryFv.Keccak.XorBlock
