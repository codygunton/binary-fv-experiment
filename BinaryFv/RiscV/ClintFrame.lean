import BinaryFv.RiscV.EnabledFrame

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

private theorem clint_frame_pure (value : α) :
    PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

private theorem clint_frame_bind (first : SailM α) (next : α → SailM β)
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

private theorem clint_frame_ite (condition : Bool) (whenTrue whenFalse : SailM α)
    (trueFrame : PreservesStackPointer whenTrue)
    (falseFrame : PreservesStackPointer whenFalse) :
    PreservesStackPointer (if condition then whenTrue else whenFalse) := by
  cases condition <;> assumption

private theorem clint_frame_read_reg (register : Register) :
    PreservesStackPointer (readReg register : SailM (RegisterType register)) := by
  intro state
  cases hAction : (readReg register : SailM (RegisterType register)).run state with
  | ok value after =>
    change (readReg register : SailM (RegisterType register)) state = .ok value after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun current : State => current.regs.get? x2) projection
  | error error after =>
    change (readReg register : SailM (RegisterType register)) state = .error error after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun current : State => current.regs.get? x2) projection

private theorem clint_frame_write_reg (written : Register) (value : RegisterType written)
    (notStack : x2 ≠ written) : PreservesStackPointer (writeReg written value) := by
  intro state
  change (match (PreSail.writeReg written value : SailM PUnit).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  rw [writeReg_run]
  exact writeReg_read_unchanged state written x2 value notStack

private theorem clint_frame_external_seip :
    PreservesStackPointer (do
      let enabled ← currentlyEnabled extension.Ext_S
      if enabled then readReg sig_seip else pure 0#1) := by
  apply clint_frame_bind (currentlyEnabled extension.Ext_S)
  · exact currentlyEnabled_s_preserves_stack_pointer
  · intro enabled
    apply clint_frame_ite
    · exact clint_frame_read_reg sig_seip
    · exact clint_frame_pure _

private theorem clint_frame_external_interrupts_pending :
    PreservesStackPointer (external_interrupts_pending ()) := by
  unfold external_interrupts_pending
  apply clint_frame_bind (readReg sig_meip)
  · exact clint_frame_read_reg sig_meip
  · intro _
    apply clint_frame_bind
    · exact clint_frame_external_seip
    · intro _
      exact clint_frame_pure _

private theorem clint_frame_read_mip (readType : XipReadType) :
    PreservesStackPointer (read_mip readType) := by
  cases readType
  · unfold read_mip
    apply clint_frame_bind (readReg mip)
    · exact clint_frame_read_reg mip
    · intro _
      apply clint_frame_bind (external_interrupts_pending ())
      · exact clint_frame_external_interrupts_pending
      · intro _
        exact clint_frame_pure _
  · unfold read_mip
    exact clint_frame_read_reg mip

private theorem clint_frame_csr_name_map_backwards_mip :
    PreservesStackPointer (csr_name_map_backwards "mip") := by
  unfold csr_name_map_backwards
  exact clint_frame_pure _

private theorem clint_frame_csr_name_write_callback_mip (value : BitVec 64) :
    PreservesStackPointer (csr_name_write_callback "mip" value) := by
  unfold csr_name_write_callback
  apply clint_frame_bind (csr_name_map_backwards "mip")
  · exact clint_frame_csr_name_map_backwards_mip
  · intro _
    exact clint_frame_pure _

private theorem clint_frame_dispatch_postlude (oldMip : BitVec 64) (mipWasWritten : Bool) :
    PreservesStackPointer (do
      let _ ← (pure () : SailM PUnit)
      let currentMip ← readReg mip
      if (oldMip != currentMip || mipWasWritten) then do
        let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
        csr_name_write_callback "mip" mipValue
      else pure ()) := by
  apply clint_frame_bind (pure ())
  · exact clint_frame_pure _
  · intro _
    apply clint_frame_bind (readReg mip)
    · exact clint_frame_read_reg mip
    · intro _
      apply clint_frame_ite
      · apply clint_frame_bind (read_mip XipReadType.IncludePlatformInterrupts)
        · exact clint_frame_read_mip XipReadType.IncludePlatformInterrupts
        · intro mipValue
          exact clint_frame_csr_name_write_callback_mip mipValue
      · exact clint_frame_pure _

/-- The generated CLINT interrupt recomputation preserves `x2` on normal and error outcomes. -/
theorem clint_dispatch_preserves_stack_pointer (mipWasWritten : Bool) :
    PreservesStackPointer (clint_dispatch mipWasWritten) := by
  unfold clint_dispatch
  simp only [get_config_print_clint, Bool.false_eq_true, ↓reduceIte]
  apply clint_frame_bind (readReg mip)
  · exact clint_frame_read_reg mip
  · intro oldMip
    apply clint_frame_bind (readReg mip)
    · exact clint_frame_read_reg mip
    · intro _
      apply clint_frame_bind (readReg mtimecmp)
      · exact clint_frame_read_reg mtimecmp
      · intro _
        apply clint_frame_bind (readReg mtime)
        · exact clint_frame_read_reg mtime
        · intro _
          apply clint_frame_bind (writeReg mip _)
          · exact clint_frame_write_reg mip _ (by decide)
          · intro _
            apply clint_frame_bind (currentlyEnabled extension.Ext_Sstc)
            · exact currentlyEnabled_sstc_preserves_stack_pointer
            · intro supervisorTimeCompare
              apply clint_frame_bind (readReg menvcfg)
              · exact clint_frame_read_reg menvcfg
              · intro _
                apply clint_frame_ite
                · apply clint_frame_bind (readReg mip)
                  · exact clint_frame_read_reg mip
                  · intro _
                    apply clint_frame_bind (readReg stimecmp)
                    · exact clint_frame_read_reg stimecmp
                    · intro _
                      apply clint_frame_bind (readReg mtime)
                      · exact clint_frame_read_reg mtime
                      · intro _
                        apply clint_frame_bind (writeReg mip _)
                        · exact clint_frame_write_reg mip _ (by decide)
                        · intro _
                          exact clint_frame_dispatch_postlude oldMip mipWasWritten
                · exact clint_frame_dispatch_postlude oldMip mipWasWritten

end BinaryFv.RiscV
