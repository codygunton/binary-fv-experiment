import BinaryFv.RiscV.Instruction.Frame.BType

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

private theorem audit_pure (value : α) : PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

private theorem audit_throw (error : Sail.Error exception) :
    PreservesStackPointer (throw error : SailM α) := by
  intro state
  rfl

private theorem audit_bind (first : SailM α) (next : α → SailM β)
    (firstFrame : PreservesStackPointer first)
    (nextFrame : ∀ value, PreservesStackPointer (next value)) :
    PreservesStackPointer (first >>= next) := by
  intro state
  cases hFirst : first.run state with
  | error error middle =>
    change first state = .error error middle at hFirst
    have firstFrame' := firstFrame state
    change (match first state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at firstFrame'
    change (match EStateM.bind first next state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = _
    unfold EStateM.bind
    rw [hFirst]
    simpa only [hFirst] using firstFrame'
  | ok value middle =>
    change first state = .ok value middle at hFirst
    have firstFrame' := firstFrame state
    change (match first state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at firstFrame'
    calc
      (match (first >>= next).run state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) =
        (match (next value).run middle with
        | .ok _ state' => state'.regs.get? x2
        | .error _ state' => state'.regs.get? x2) := by
          change (match EStateM.bind first next state with
          | .ok _ state' => state'.regs.get? x2
          | .error _ state' => state'.regs.get? x2) = _
          unfold EStateM.bind
          rw [hFirst]
          rfl
      _ = middle.regs.get? x2 := nextFrame value middle
      _ = state.regs.get? x2 := by simpa only [hFirst] using firstFrame'

private def AuditPreservesExcept {ε α : Type} (action : ExceptT ε SailM α) : Prop :=
  PreservesStackPointer (ExceptT.run action)

private theorem audit_except_pure {ε α : Type} (value : α) :
    AuditPreservesExcept (pure value : ExceptT ε SailM α) := by
  intro state
  rfl

private theorem audit_except_throw {ε α : Type} (error : ε) :
    AuditPreservesExcept (Sail.SailME.throw error : SailME ε α) := by
  change PreservesStackPointer (ExceptT.run (Sail.SailME.throw error : SailME ε α))
  unfold Sail.SailME.throw PreSail.PreSailME.throw
  exact audit_pure _

private theorem audit_except_ite {ε α : Type} (condition : Bool)
    (whenTrue whenFalse : SailME ε α) (trueFrame : AuditPreservesExcept whenTrue)
    (falseFrame : AuditPreservesExcept whenFalse) :
    AuditPreservesExcept (if condition then whenTrue else whenFalse) := by
  cases condition <;> assumption

private theorem audit_except_lift {ε α : Type} (action : SailM α)
    (frame : PreservesStackPointer action) :
    AuditPreservesExcept (ExceptT.lift action : ExceptT ε SailM α) := by
  intro state
  simp only [ExceptT.lift, ExceptT.mk, ExceptT.run, EStateM.instMonad]
  cases hAction : action state with
  | ok value after =>
    have frame' := frame state
    change (match action state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at frame'
    simpa [EStateM.run, EStateM.bind, EStateM.map, hAction] using frame'
  | error error after =>
    have frame' := frame state
    change (match action state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at frame'
    simpa [EStateM.run, EStateM.bind, EStateM.map, hAction] using frame'

private theorem audit_except_bind {ε α β : Type} (action : ExceptT ε SailM α)
    (next : α → ExceptT ε SailM β) (actionFrame : AuditPreservesExcept action)
    (nextFrame : ∀ value, AuditPreservesExcept (next value)) :
    AuditPreservesExcept (action >>= next) := by
  unfold AuditPreservesExcept
  have runEq : ExceptT.run (action >>= next) = (do
      let result ← ExceptT.run action
      match result with
      | .ok value => ExceptT.run (next value)
      | .error error => pure (.error error)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.run, ExceptT.mk,
      EStateM.instMonad]
    rfl
  rw [runEq]
  apply audit_bind (ExceptT.run action) _ actionFrame
  intro result
  cases result with
  | ok value => exact nextFrame value
  | error error => exact audit_pure (Except.error error : Except ε β)

private theorem audit_sail_me_run {α : Type} (action : SailME α α)
    (frame : AuditPreservesExcept action) : PreservesStackPointer (Sail.SailME.run action) := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  apply audit_bind (ExceptT.run action) _ frame
  intro result
  cases result with
  | ok value => exact audit_pure value
  | error error =>
    cases error with
    | inl error =>
      intro state
      rfl
    | inr value => exact audit_pure value

private theorem audit_read_reg (register : Register) :
    PreservesStackPointer (readReg register : SailM (RegisterType register)) := by
  intro state
  cases hAction : (readReg register : SailM (RegisterType register)).run state with
  | ok value after =>
    change (readReg register : SailM (RegisterType register)) state = .ok value after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection
  | error error after =>
    change (readReg register : SailM (RegisterType register)) state = .error error after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection

private theorem audit_assert (condition : Bool) (message : String) :
    PreservesStackPointer (Sail.assert condition message) := by
  unfold Sail.assert PreSail.assert
  split <;> exact audit_pure () <;> intro state <;> rfl

private theorem audit_page_based_mem_type_forwards (bits : BitVec 2) :
    PreservesStackPointer (page_based_mem_type_forwards bits) := by
  unfold page_based_mem_type_forwards
  split
  · exact audit_pure _
  · exact audit_pure _
  · exact audit_pure _
  · apply audit_bind (Sail.assert false "Pattern match failure at unknown location")
    · exact audit_assert _ _
    · intro _
      exact audit_throw _

/-- Structural all-outcome x2 frame for the generated recursive page-table walk. -/
theorem pt_walk_preserves_stack_pointer_of (svWidth : Nat) (vpn : BitVec (svWidth - 12))
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (mxr doSum : Bool)
    (external : Unit)
    (readPteFrame : ∀ address width, PreservesStackPointer (read_pte address width))
    (invalidFrame : ∀ flags extensions, PreservesStackPointer (pte_is_invalid flags extensions))
    (permissionFrame : ∀ flags extensions,
      PreservesStackPointer
        (check_PTE_permission access privilege mxr doSum flags extensions external))
    (enabledFrame : PreservesStackPointer (currentlyEnabled extension.Ext_Svnapot)) :
    ∀ (ptBase : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (level : Nat) (global : Bool),
      PreservesStackPointer (pt_walk svWidth vpn access privilege mxr doSum ptBase level global
        external) := by
  intro ptBase level global
  induction ptBase, level, global using pt_walk.induct svWidth vpn access privilege mxr doSum
      external with
  | case1 ptBase level global induction =>
    rw [pt_walk.eq_1]
    apply audit_sail_me_run
    apply audit_except_bind
    · exact audit_except_lift _ (audit_assert _ _)
    · intro _
      apply audit_except_bind
      · exact audit_except_lift _ (readPteFrame _ _)
      · intro readResult
        cases readResult with
        | Err error => exact audit_except_pure _
        | Ok pte =>
          apply audit_except_bind
          · exact audit_except_lift _ (invalidFrame _ _)
          · intro invalid
            cases hInvalid : invalid with
            | true =>
              exact audit_except_pure _
            | false =>
              cases hNonleaf : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) with
              | true =>
                cases hLevel : level >b 0 with
                | true =>
                  exact audit_except_lift _ (induction pte hNonleaf hLevel)
                | false =>
                  exact audit_except_pure _
              | false =>
                cases hLevel : level >b 0 with
                | true =>
                  apply audit_except_bind
                  · apply audit_except_ite
                    · exact audit_except_throw _
                    · exact audit_except_pure _
                  · intro _
                    apply audit_except_bind
                    · exact audit_except_lift _ (permissionFrame _ _)
                    · intro permission
                      cases permission with
                      | PTE_Check_Failure result => exact audit_except_pure _
                      | PTE_Check_Success extensionState =>
                        apply audit_except_bind
                        · apply audit_except_ite
                          · exact audit_except_throw _
                          · exact audit_except_pure _
                        · intro _
                          apply audit_except_bind
                          · exact audit_except_lift _ (audit_read_reg menvcfg)
                          · intro _
                            apply audit_except_ite
                            · exact audit_except_pure _
                            · apply audit_except_bind
                              · exact audit_except_lift _ (audit_page_based_mem_type_forwards _)
                              · intro _
                                exact audit_except_pure _
                | false =>
                  apply audit_except_bind
                  · exact audit_except_pure _
                  · intro _
                    apply audit_except_bind
                    · exact audit_except_lift _ (permissionFrame _ _)
                    · intro permission
                      cases permission with
                      | PTE_Check_Failure result => exact audit_except_pure _
                      | PTE_Check_Success extensionState =>
                        apply audit_except_bind
                        · apply audit_except_bind
                          · exact audit_except_lift _ enabledFrame
                          · intro enabled
                            apply audit_except_ite
                            · apply audit_except_ite
                              · exact audit_except_throw _
                              · exact audit_except_pure _
                            · exact audit_except_pure _
                        · intro _
                          apply audit_except_bind
                          · exact audit_except_lift _ (audit_read_reg menvcfg)
                          · intro _
                            apply audit_except_ite
                            · exact audit_except_pure _
                            · apply audit_except_bind
                              · exact audit_except_lift _ (audit_page_based_mem_type_forwards _)
                              · intro _
                                exact audit_except_pure _

/-- Structural all-outcome x2 frame for the generated TLB-hit translation branch. -/
theorem translate_tlb_hit_preserves_stack_pointer_of (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (vpn : BitVec (svWidth - 12)) (access : MemoryAccessType mem_payload)
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) (index : Nat) (entry : TLB_Entry)
    (permissionFrame : ∀ flags extensions,
      PreservesStackPointer
        (check_PTE_permission access privilege mxr doSum flags extensions external))
    (updateFrame : ∀ address width pte,
      PreservesStackPointer (update_and_write_pte address width pte access))
    (writeTlbFrame : ∀ index entry, PreservesStackPointer (write_TLB index entry))
    (pbmtFrame : PreservesStackPointer (tlb_get_pbmt entry)) :
    PreservesStackPointer
      (translate_TLB_hit svWidth asid vpn access privilege mxr doSum external index entry) := by
  unfold translate_TLB_hit
  apply audit_bind
      (check_PTE_permission access privilege mxr doSum _ _ external)
  · exact permissionFrame _ _
  · intro permission
    cases permission with
    | PTE_Check_Failure result => exact audit_pure _
    | PTE_Check_Success extensionState =>
      apply audit_bind (update_and_write_pte entry.pteAddr _ _ access)
      · exact updateFrame _ _ _
      · intro update
        cases update with
        | Err error =>
          cases error <;> exact audit_pure _
        | Ok updated =>
          cases updated with
          | some updatedPte =>
            apply audit_bind (write_TLB index (tlb_set_pte entry updatedPte))
            · exact writeTlbFrame _ _
            · intro _
              apply audit_bind (tlb_get_pbmt entry)
              · exact pbmtFrame
              · intro _
                exact audit_pure _
          | none =>
            apply audit_bind (tlb_get_pbmt entry)
            · exact pbmtFrame
            · intro _
              exact audit_pure _

/-- Structural all-outcome x2 frame for the generated TLB-miss translation branch. -/
theorem translate_tlb_miss_preserves_stack_pointer_of (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (vpn : BitVec (svWidth - 12)) (access : MemoryAccessType mem_payload)
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit)
    (ptWalkFrame : ∀ ptBase level global,
      PreservesStackPointer (pt_walk svWidth vpn access privilege mxr doSum ptBase level global
        external))
    (updateFrame : ∀ address width pte,
      PreservesStackPointer (update_and_write_pte address width pte access))
    (addTlbFrame : ∀ ppn pte pteAddress level global,
      PreservesStackPointer (add_to_TLB svWidth asid vpn ppn pte pteAddress level global)) :
    PreservesStackPointer
      (translate_TLB_miss svWidth asid basePpn vpn access privilege mxr doSum external) := by
  unfold translate_TLB_miss
  apply audit_bind
      (pt_walk svWidth vpn access privilege mxr doSum basePpn
        (if svWidth == 32 then 1 else if svWidth == 39 then 2 else if svWidth == 48 then 3 else 4)
        false external)
  · exact ptWalkFrame _ _ _
  · intro result
    cases result with
    | Err error => exact audit_pure _
    | Ok output =>
      rcases output with ⟨output, external⟩
      rcases output with ⟨ppn, pte, pteAddress, level, pbmt, global⟩
      apply audit_bind (update_and_write_pte pteAddress _ pte access)
      · exact updateFrame _ _ _
      · intro update
        cases update with
        | Err error => exact audit_pure _
        | Ok updated =>
          cases updated with
          | some updatedPte =>
            apply audit_bind (add_to_TLB svWidth asid vpn ppn updatedPte pteAddress level global)
            · exact addTlbFrame _ _ _ _ _
            · intro _
              exact audit_pure _
          | none =>
            apply audit_bind (add_to_TLB svWidth asid vpn ppn pte pteAddress level global)
            · exact addTlbFrame _ _ _ _ _
            · intro _
              exact audit_pure _

/-- Structural all-outcome x2 frame for the generated TLB selector. -/
theorem translate_preserves_stack_pointer_of (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (vpn : BitVec (svWidth - 12)) (access : MemoryAccessType mem_payload)
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit)
    (lookupFrame : PreservesStackPointer (lookup_TLB svWidth asid vpn))
    (hitFrame : ∀ index entry,
      PreservesStackPointer
        (translate_TLB_hit svWidth asid vpn access privilege mxr doSum external index entry))
    (missFrame : PreservesStackPointer
      (translate_TLB_miss svWidth asid basePpn vpn access privilege mxr doSum external)) :
    PreservesStackPointer
      (translate svWidth asid basePpn vpn access privilege mxr doSum external) := by
  unfold translate
  apply audit_bind (lookup_TLB svWidth asid vpn)
  · exact lookupFrame
  · intro lookup
    cases lookup with
    | none => exact missFrame
    | some entry =>
      rcases entry with ⟨index, entry⟩
      exact hitFrame index entry

/-- Structural all-outcome x2 frame for generated virtual-address translation. -/
theorem translate_addr_preserves_stack_pointer_of (vaddr : virtaddr)
    (access : MemoryAccessType mem_payload)
    (effectiveFrame : ∀ mstatus privilege,
      PreservesStackPointer (effectivePrivilege access mstatus privilege))
    (modeFrame : ∀ privilege, PreservesStackPointer (translationMode privilege))
    (shadowFrame : PreservesStackPointer (is_shadow_stack_access access))
    (widthFrame : ∀ mode, PreservesStackPointer (satp_mode_width_forwards mode))
    (satpFrame : ∀ svWidth, PreservesStackPointer (get_satp svWidth))
    (exceptionFrame : ∀ failure,
      PreservesStackPointer (translationException access failure))
    (translateFrame : ∀ (svWidth : Nat)
      (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
      (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
      (vpn : BitVec (svWidth - 12)) (privilege : Privilege) (mxr doSum : Bool),
      PreservesStackPointer
        (translate svWidth asid basePpn vpn access privilege mxr doSum init_ext_ptw)) :
    PreservesStackPointer (translateAddr vaddr access) := by
  unfold translateAddr
  apply audit_sail_me_run
  apply audit_except_bind
  · exact audit_except_lift _ (audit_read_reg mstatus)
  · intro mstatusBits
    apply audit_except_bind
    · exact audit_except_lift _ (audit_read_reg cur_privilege)
    · intro privilege
      apply audit_except_bind
      · exact audit_except_lift _ (effectiveFrame mstatusBits privilege)
      · intro effectivePrivilege
        apply audit_except_bind
        · exact audit_except_lift _ (modeFrame effectivePrivilege)
        · intro mode
          apply audit_except_bind
          · exact audit_except_lift _ shadowFrame
          · intro shadow
            cases shadow with
            | true =>
              apply audit_except_bind
              · apply audit_except_ite
                · exact audit_except_throw _
                · exact audit_except_pure _
              · intro _
                apply audit_except_ite
                · exact audit_except_pure _
                · apply audit_except_bind
                  · exact audit_except_lift _ (widthFrame mode)
                  · intro svWidth
                    apply audit_except_bind
                    · exact audit_except_lift _ (satpFrame svWidth)
                    · intro satp
                      apply audit_except_bind
                      · exact audit_except_lift _ (audit_assert _ _)
                      · intro _
                        apply audit_except_ite
                        · apply audit_except_bind
                          · exact audit_except_lift _ (exceptionFrame _)
                          · intro _
                            exact audit_except_pure _
                        · apply audit_except_bind
                          · exact audit_except_lift _ (audit_read_reg mstatus)
                          · intro mstatusBits
                            apply audit_except_bind
                            · exact audit_except_pure _
                            · intro mxr
                              apply audit_except_bind
                              · exact audit_except_lift _ (audit_read_reg mstatus)
                              · intro mstatusBits'
                                apply audit_except_bind
                                · exact audit_except_pure _
                                · intro doSum
                                  apply audit_except_bind
                                  · exact audit_except_lift _
                                      (translateFrame _ _ _ _ effectivePrivilege mxr doSum)
                                  · intro translation
                                    cases translation with
                                    | Err failure =>
                                      rcases failure with ⟨failure, extensionState⟩
                                      apply audit_except_bind
                                      · exact audit_except_lift _ (exceptionFrame failure)
                                      · intro _
                                        exact audit_except_pure _
                                    | Ok translation => exact audit_except_pure _
            | false =>
              apply audit_except_bind
              · exact audit_except_pure _
              · intro _
                apply audit_except_ite
                · exact audit_except_pure _
                · apply audit_except_bind
                  · exact audit_except_lift _ (widthFrame mode)
                  · intro svWidth
                    apply audit_except_bind
                    · exact audit_except_lift _ (satpFrame svWidth)
                    · intro satp
                      apply audit_except_bind
                      · exact audit_except_lift _ (audit_assert _ _)
                      · intro _
                        apply audit_except_ite
                        · apply audit_except_bind
                          · exact audit_except_lift _ (exceptionFrame _)
                          · intro _
                            exact audit_except_pure _
                        · apply audit_except_bind
                          · exact audit_except_lift _ (audit_read_reg mstatus)
                          · intro mstatusBits
                            apply audit_except_bind
                            · exact audit_except_pure _
                            · intro mxr
                              apply audit_except_bind
                              · exact audit_except_lift _ (audit_read_reg mstatus)
                              · intro mstatusBits'
                                apply audit_except_bind
                                · exact audit_except_pure _
                                · intro doSum
                                  apply audit_except_bind
                                  · exact audit_except_lift _
                                      (translateFrame _ _ _ _ effectivePrivilege mxr doSum)
                                  · intro translation
                                    cases translation with
                                    | Err failure =>
                                      rcases failure with ⟨failure, extensionState⟩
                                      apply audit_except_bind
                                      · exact audit_except_lift _ (exceptionFrame failure)
                                      · intro _
                                        exact audit_except_pure _
                                    | Ok translation => exact audit_except_pure _

end BinaryFv.RiscV
