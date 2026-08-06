import BinaryFv.Zesu.MachineExecution.Level2Capstone
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch

/-! Tags one, two, and three reach `0x1035c`; tag zero ends at `0x1033c` and requires the separate
success-continuation proof from `0x1033c` to `0x1035c` before this epilogue theorem applies. -/
namespace BinaryFv.Zesu.MachineExecution
open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated PreSail LeanRV64DExecutable.Functions Register
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The concrete saved-frame and address facts required after a result-tag route. -/
structure WrapperSavedState (base before : State) (machineArgs : DecoderMachineArgs) where
  machine : DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    machineArgs base
  link : BitVec 64
  savedS0 : BitVec 64
  savedS1 : BitVec 64
  savedS2 : BitVec 64
  stack : BitVec 64
  restoredStack : BitVec 64
  savedFrame : WrapperSavedRegisterFrame stack.toNat link savedS0 savedS1 savedS2 before
  stackAvoidsStatusGlobals : stack.toNat + 0xa20 ≤ 0x4215020 ∨ 0x4215028 ≤ stack.toNat
  globalsValue : before.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  stackValue : before.regs.get? x2 = some stack

/-- The four saved-register load addresses, alignment facts, and readable-byte permissions. -/
structure WrapperRestoreAddresses (machineArgs : DecoderMachineArgs) (stack : BitVec 64) where
  raAddress : BitVec 64
  s0Address : BitVec 64
  s1Address : BitVec 64
  s2Address : BitVec 64
  raAddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e8#12) = raAddress
  s0AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e0#12) = s0Address
  s1AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d8#12) = s1Address
  s2AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d0#12) = s2Address
  raAddressNat : stack.toNat + 0xa18 = raAddress.toNat
  s0AddressNat : stack.toNat + 0xa10 = s0Address.toNat
  s1AddressNat : stack.toNat + 0xa08 = s1Address.toNat
  s2AddressNat : stack.toNat + 0xa00 = s2Address.toNat
  raAligned : is_aligned_vaddr (virtaddr.Virtaddr raAddress) 8 = true
  s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true
  s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true
  s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true
  raAllowed : DecoderAccessRange (DecoderReadableByte machineArgs) raAddress 8
  s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8
  s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8
  s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8

/-- The final stack restoration and the two low-bit facts required by the generated `ret`. -/
structure WrapperReturnTarget (stack restoredStack link : BitVec 64) where
  restoredStackEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7f0#12) = restoredStack
  linkEven : Sail.BitVec.update link 0 0#1 = link
  linkBit1 : Sail.BitVec.access link 1 = 0#1

theorem dispatch_route_to_epilogue {base before routeAfter : State} {machineArgs : DecoderMachineArgs}
    (h : WrapperSavedState base before machineArgs)
    (addresses : WrapperRestoreAddresses machineArgs h.stack)
    (target : WrapperReturnTarget h.stack h.restoredStack h.link)
    (n k : Nat) (result status : BitVec 64)
    (route : WrapperDispatchRouteFrame base before routeAfter n k
      (BitVec.ofNat 64 0x1035c) result status) :
    ∃ afterStore after,
      Runs (try_step (n + k) false) routeAfter afterStore false ∧
      Trace n (k + 8) before after ∧
      WrapperEpilogueCompleteResult (n + k + 1) base afterStore after
        h.link h.savedS0 h.savedS1 h.savedS2 h.restoredStack result status := by
  exact wrapper_dispatch_route_through_epilogue h.machine n k result status h.link h.savedS0
    h.savedS1 h.savedS2 h.stack h.restoredStack route.terminal
    (WrapperSavedRegisterFrame.of_mem_eq h.savedFrame route.memory)
    h.stackAvoidsStatusGlobals (route.savedS2.trans h.globalsValue)
    (route.savedStack.trans h.stackValue) addresses.raAddress addresses.s0Address
    addresses.s1Address addresses.s2Address addresses.raAddressEq addresses.s0AddressEq
    addresses.s1AddressEq addresses.s2AddressEq addresses.raAddressNat addresses.s0AddressNat
    addresses.s1AddressNat addresses.s2AddressNat addresses.raAligned addresses.s0Aligned
    addresses.s1Aligned addresses.s2Aligned addresses.raAllowed addresses.s0Allowed
    addresses.s1Allowed addresses.s2Allowed target.restoredStackEq target.linkEven target.linkBit1

theorem tag1_outcome_to_epilogue {base before : State} {machineArgs : DecoderMachineArgs}
    (h : WrapperSavedState base before machineArgs) (addresses : WrapperRestoreAddresses machineArgs h.stack)
    (target : WrapperReturnTarget h.stack h.restoredStack h.link) (agree : Agree platformPreserved base before)
    (retired : RetiredCounterPresent before) (code : canonicalContractParams.env.CodeIntact before)
    (n : Nat) (pc : before.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : before.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    ∃ routeAfter afterStore after, WrapperDispatchRouteFrame base before routeAfter n 7 (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) ∧
      Runs (try_step (n + 7) false) routeAfter afterStore false ∧ Trace n 15 before after ∧
      WrapperEpilogueCompleteResult (n + 8) base afterStore after h.link h.savedS0 h.savedS1 h.savedS2 h.restoredStack (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) := by
  obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag1_route_frame h.machine agree retired code n pc tag
  obtain ⟨afterStore, after, store, trace, complete⟩ := dispatch_route_to_epilogue h addresses target n 7 (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) route
  exact ⟨routeAfter, afterStore, after, route, store, trace, complete⟩

theorem tag2_outcome_to_epilogue {base before : State} {machineArgs : DecoderMachineArgs}
    (h : WrapperSavedState base before machineArgs)
    (addresses : WrapperRestoreAddresses machineArgs h.stack)
    (target : WrapperReturnTarget h.stack h.restoredStack h.link)
    (agree : Agree platformPreserved base before) (retired : RetiredCounterPresent before)
    (code : canonicalContractParams.env.CodeIntact before) (n : Nat)
    (pc : before.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : before.regs.get? x10 = some (BitVec.ofNat 64 2)) :
    ∃ routeAfter afterStore after,
      WrapperDispatchRouteFrame base before routeAfter n 9 (BitVec.ofNat 64 0x1035c)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 2) ∧
      Runs (try_step (n + 9) false) routeAfter afterStore false ∧
      Trace n 17 before after ∧
      WrapperEpilogueCompleteResult (n + 10) base afterStore after h.link h.savedS0 h.savedS1
        h.savedS2 h.restoredStack (BitVec.ofNat 64 0) (BitVec.ofNat 64 2) := by
  obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag2_route_frame h.machine agree retired code n pc tag
  obtain ⟨afterStore, after, store, trace, complete⟩ := dispatch_route_to_epilogue h addresses target n 9 (BitVec.ofNat 64 0) (BitVec.ofNat 64 2) route
  exact ⟨routeAfter, afterStore, after, route, store, trace, complete⟩

theorem tag3_outcome_to_epilogue {base before : State} {machineArgs : DecoderMachineArgs}
    (h : WrapperSavedState base before machineArgs)
    (addresses : WrapperRestoreAddresses machineArgs h.stack)
    (target : WrapperReturnTarget h.stack h.restoredStack h.link)
    (agree : Agree platformPreserved base before) (retired : RetiredCounterPresent before)
    (code : canonicalContractParams.env.CodeIntact before) (n : Nat)
    (pc : before.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : before.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    ∃ routeAfter afterStore after,
      WrapperDispatchRouteFrame base before routeAfter n 5 (BitVec.ofNat 64 0x1035c)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) ∧
      Runs (try_step (n + 5) false) routeAfter afterStore false ∧
      Trace n 13 before after ∧
      WrapperEpilogueCompleteResult (n + 6) base afterStore after h.link h.savedS0 h.savedS1
        h.savedS2 h.restoredStack (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) := by
  obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag3_route_frame h.machine agree retired code n pc tag
  obtain ⟨afterStore, after, store, trace, complete⟩ := dispatch_route_to_epilogue h addresses target n 5 (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) route
  exact ⟨routeAfter, afterStore, after, route, store, trace, complete⟩

end BinaryFv.Zesu.MachineExecution
