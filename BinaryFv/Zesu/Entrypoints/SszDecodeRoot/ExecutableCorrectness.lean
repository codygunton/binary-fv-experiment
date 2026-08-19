import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Executable
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level0Contract

/-! Connection between executable outcomes and the reviewed Level 0 meaning. -/

namespace BinaryFv.Zesu

open LeanRV64DExecutable.Functions Register

theorem readMemoryBytes_eq_some_of_bytesRep {memory : Std.ExtHashMap Nat (BitVec 8)}
    {address : Nat} {bytes : Array UInt8} (rep : BytesRep memory address bytes) :
    readMemoryBytes memory address bytes.size = some bytes := by
  have hprefix : ∀ count, count ≤ bytes.size →
      readMemoryBytes memory address count = some (bytes.extract 0 count) := by
    intro count bound
    induction count with
    | zero => simp [readMemoryBytes]
    | succ count ih =>
        rw [readMemoryBytes, ih (by omega), rep.2 count (by omega)]
        have byteEq : UInt8.ofNat (BitVec.ofNat 8 bytes[count].toNat).toNat = bytes[count] := by
          rw [BitVec.toNat_ofNat]
          have reduced : bytes[count].toNat % 2 ^ 8 = bytes[count].toNat :=
            Nat.mod_eq_of_lt bytes[count].toNat_lt
          rw [reduced]
          exact UInt8.ofNat_toNat
        change some ((bytes.extract 0 count).push
          (UInt8.ofNat (BitVec.ofNat 8 bytes[count].toNat).toNat)) = _
        rw [byteEq]
        exact congrArg some (Array.extract_succ_right (as := bytes) (i := 0) (j := count)
          (by omega) (by omega)).symm
  simpa using hprefix bytes.size (by omega)

theorem endpointStep_evaluates {stepNo : Nat} {before after : EndpointState}
    (step : EndpointStep stepNo before after) : endpointStep stepNo before = .ok after := by
  cases step with
  | sail notHost machineStep stdin cursor stdout exitCode =>
      unfold MachineStep at machineStep
      unfold endpointStep
      rw [machineStep]
      simp only
      have notRead : before.machine.regs.get? PC ≠ some (BitVec.ofNat 64 readContextReturnPc) := by
        intro atPc
        exact notHost _ (by simpa [EndpointPc] using atPc) (Or.inl rfl)
      have notWrite : before.machine.regs.get? PC ≠ some (BitVec.ofNat 64 writeContextReturnPc) := by
        intro atPc
        exact notHost _ (by simpa [EndpointPc] using atPc) (Or.inr (Or.inl rfl))
      have notExit : before.machine.regs.get? PC ≠ some (BitVec.ofNat 64 exitContextStorePc) := by
        intro atPc
        exact notHost _ (by simpa [EndpointPc] using atPc) (Or.inr (Or.inr rfl))
      cases pcRead : before.machine.regs.get? PC with
      | none =>
          simp [pcRead]
          apply EndpointState.ext <;> simp_all
      | some pc =>
          simp only
          have readNe : pc.toNat ≠ readContextReturnPc := by
            intro eq
            apply notRead
            rw [← eq]
            simpa using pcRead
          have writeNe : pc.toNat ≠ writeContextReturnPc := by
            intro eq
            apply notWrite
            rw [← eq]
            simpa using pcRead
          have exitNe : pc.toNat ≠ exitContextStorePc := by
            intro eq
            apply notExit
            rw [← eq]
            simpa using pcRead
          simp [readNe, writeNe, exitNe]
          apply EndpointState.ext <;> simp_all
  | read step =>
      rcases step with ⟨atPc, bytes, machineStep, stdin, cursor, stdout, exitCode⟩
      unfold MachineStep at machineStep
      unfold endpointStep
      rw [machineStep, atPc]
      apply congrArg Except.ok
      apply EndpointState.ext <;> simp_all

  | write step =>
      rcases step with ⟨buffer, count, chunk, atPc, bufferAt, countAt, bufferFits, countFits,
        size, bytes,
        machineStep, stdin, cursor, stdout, exitCode⟩
      unfold MachineStep at machineStep
      unfold endpointStep
      rw [machineStep, atPc, bufferAt, countAt]
      have read := readMemoryBytes_eq_some_of_bytesRep bytes
      rw [size] at read
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bufferFits, Nat.mod_eq_of_lt countFits]
      rw [read]
      apply congrArg Except.ok
      apply EndpointState.ext <;> simp_all
  | exit step =>
      rcases step with ⟨code, atPc, codeAt, codeFits, machineStep, stdin, cursor, stdout, exitCode,
        terminal⟩
      unfold MachineStep at machineStep
      unfold endpointStep
      rw [machineStep, atPc, codeAt]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt codeFits]
      apply congrArg Except.ok
      apply EndpointState.ext <;> simp_all

theorem runEndpoint_of_confinedTrace {region : BitVec 64 → Prop}
    (regionAvoidsTerminal : ∀ pc, region pc → pc ≠ BitVec.ofNat 64 Elflings.zkvmExitTerminalPc)
    {fromStep count fuel : Nat} {before after : EndpointState}
    (trace : ConfinedTrace EndpointStep EndpointPc region fromStep count before after)
    (fuelSuffices : count < fuel)
    (terminal : EndpointPc after = some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc)) :
    runEndpoint fuel fromStep before = finishEndpoint after := by
  induction trace generalizing fuel with
  | refl =>
      cases fuel with
      | zero => omega
      | succ remaining =>
          rw [runEndpoint, if_pos (by simpa [EndpointPc] using terminal)]
  | step stepNo count pc before middle after atPc inside step rest ih =>
      cases fuel with
      | zero => omega
      | succ remaining =>
          rw [runEndpoint]
          have notTerminal : before.machine.regs.get? PC ≠
              some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc) := by
            intro equal
            have pcEq : pc = BitVec.ofNat 64 Elflings.zkvmExitTerminalPc := by
              rw [EndpointPc] at atPc
              exact Option.some.inj (atPc.symm.trans equal)
            exact regionAvoidsTerminal pc inside pcEq
          rw [if_neg notTerminal, endpointStep_evaluates step]
          exact ih (by omega) terminal
def ZesuDecodeOutcome.ofMainOutcome : MainOutcome → ZesuDecodeOutcome
  | .failure => .rejected
  | .success value => .decoded value

theorem finishEndpoint_of_mainExit {args : MainArgs} {outcome : MainOutcome}
    {before after : EndpointState} (exit : MainExit args outcome before after) :
    finishEndpoint after = ZesuDecodeOutcome.ofMainOutcome outcome := by
  rcases exit with ⟨terminal, _stdin, _cursor, exitCode, bytes, stdout, observed⟩
  unfold finishEndpoint
  rw [if_neg (by simpa [EndpointPc] using terminal), if_neg (by simpa [exitCode])]
  rw [stdout]
  cases outcome with
  | failure => rw [observed]; rfl
  | success decoded => rw [observed]; rfl

theorem allowedModuloKnownBugs_ofMainOutcome_iff (args : MainArgs) (outcome : MainOutcome) :
    (ZesuDecodeOutcome.ofMainOutcome outcome).AllowedModuloKnownBugs args.input ↔
      MainMeaningModulo knownBugs args outcome := by
  cases outcome <;> simp [ZesuDecodeOutcome.ofMainOutcome,
    ZesuDecodeOutcome.AllowedModuloKnownBugs, MainMeaningModulo]

theorem canonicalOutcome_eq_ofMainOutcome (args : MainArgs) (outcome : MainOutcome)
    (meaning : MainMeaningModulo knownBugs args outcome) :
    CanonicalOutcome.ofZesuKnownBugs args.input (ZesuDecodeOutcome.ofMainOutcome outcome) =
        CanonicalOutcome.ofEvmSail args.input :=
  canonicalOutcome_eq_of_allowed args.input _
    ((allowedModuloKnownBugs_ofMainOutcome_iff args outcome).2 meaning)

end BinaryFv.Zesu
