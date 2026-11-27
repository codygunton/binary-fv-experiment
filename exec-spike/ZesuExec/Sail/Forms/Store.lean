import ZesuExec.Sail.Forms.Mem

/-!
# Simulation of the stores

`sd sw sh sb`: `Machine.store` succeeds only for a naturally aligned range inside RAM whose bytes
are all present; the profile's RAM region admits the write, the generated store writes the low
bytes of `rs2` little-endian, and `sim_store_of_exec` relates the two memories.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType mem_payload

variable {img : Image} {m m' : Machine} {s : State} {w : Nat}

theorem sim_sd {rs1 rs2 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sd rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.storeFrom, Option.map_eq_some_iff] at hex
  obtain ⟨m1, hst, rfl⟩ := hex
  unfold Machine.store at hst
  split at hst
  · rename_i hc
    obtain ⟨hal, hwr, _⟩ := hc
    cases hst
    obtain ⟨mst, hmst, hmprv⟩ := hR.conf.mstatus
    obtain ⟨sec, hsec, hpmm⟩ := hR.conf.mseccfg
    let st := T s m.pc
    have hmst' : st.regs.get? mstatus = some mst := by rw [T_get? (by decide) (by decide)]; exact hmst
    have hpriv : st.regs.get? cur_privilege = some .Machine := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.privilege
    have hsec' : st.regs.get? mseccfg = some sec := by rw [T_get? (by decide) (by decide)]; exact hsec
    have hpma : st.regs.get? pma_regions = some zesuPmaRegions := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.pma
    have hag := RegsAgree.T (m := m) hR.regs m.pc
    have addrReg : Runs (get_transformed_data_addr (rg rs1) (sign_extend (m := 64) imm)
        (Store Data) 8) st st (.Ext_DataAddr_OK (virtaddr.Virtaddr (m.reg rs1 + Machine.sx imm))) :=
      get_transformed_data_addr_machine_data_run .store st (rg rs1) 8 (m.reg rs1)
        (sign_extend (m := 64) imm) mst sec (rX_rg_run hag rs1) hmst' hpriv hmprv hsec' hpmm
    have hal' := aligned_of_mod hal
    have physAccess := phys_access_check_machine_store_allowed st _ 8 (storePma hpma hwr) hal'.2
    refine sim_store_of_exec hR hw hd hpc (data := (m.reg rs2 : BitVec (8 * 8))) hwr
      (fun j _ => rfl) ?_ n
    change Runs (execute_STORE imm (rg rs2) (rg rs1) 8) _ _ _
    exact execute_STORE_dword_run st _ (rg rs2) (rg rs1) imm _ mst (m.reg rs2) hmst' hpriv hmprv
      (rX_rg_run hag rs2) addrReg hal'.1 physAccess (writeBytes_run_exact st _ _)
  · cases hst

theorem sim_sw {rs1 rs2 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sw rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.storeFrom, Option.map_eq_some_iff] at hex
  obtain ⟨m1, hst, rfl⟩ := hex
  unfold Machine.store at hst
  split at hst
  · rename_i hc
    obtain ⟨hal, hwr, _⟩ := hc
    cases hst
    obtain ⟨mst, hmst, hmprv⟩ := hR.conf.mstatus
    obtain ⟨sec, hsec, hpmm⟩ := hR.conf.mseccfg
    let st := T s m.pc
    have hmst' : st.regs.get? mstatus = some mst := by rw [T_get? (by decide) (by decide)]; exact hmst
    have hpriv : st.regs.get? cur_privilege = some .Machine := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.privilege
    have hsec' : st.regs.get? mseccfg = some sec := by rw [T_get? (by decide) (by decide)]; exact hsec
    have hpma : st.regs.get? pma_regions = some zesuPmaRegions := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.pma
    have hag := RegsAgree.T (m := m) hR.regs m.pc
    have addrReg : Runs (get_transformed_data_addr (rg rs1) (sign_extend (m := 64) imm)
        (Store Data) 4) st st (.Ext_DataAddr_OK (virtaddr.Virtaddr (m.reg rs1 + Machine.sx imm))) :=
      get_transformed_data_addr_machine_data_run .store st (rg rs1) 4 (m.reg rs1)
        (sign_extend (m := 64) imm) mst sec (rX_rg_run hag rs1) hmst' hpriv hmprv hsec' hpmm
    have hal' := aligned_of_mod hal
    have physAccess := phys_access_check_machine_store_allowed st _ 4 (storePma hpma hwr) hal'.2
    refine sim_store_of_exec hR hw hd hpc (data := (Sail.BitVec.extractLsb (m.reg rs2) 31 0 : BitVec (8 * 4))) hwr
      (fun j hj => by
        apply BitVec.eq_of_toNat_eq
        simp only [Sail.BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases this with rfl|rfl|rfl|rfl <;> simp <;> omega) ?_ n
    change Runs (execute_STORE imm (rg rs2) (rg rs1) 4) _ _ _
    exact execute_STORE_word_aligned_run st _ (rg rs2) (rg rs1) imm _ mst (m.reg rs2) hmst' hpriv hmprv
      (rX_rg_run hag rs2) addrReg hal'.1 physAccess (writeBytes_run_exact st _ _)
  · cases hst

theorem sim_sh {rs1 rs2 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sh rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.storeFrom, Option.map_eq_some_iff] at hex
  obtain ⟨m1, hst, rfl⟩ := hex
  unfold Machine.store at hst
  split at hst
  · rename_i hc
    obtain ⟨hal, hwr, _⟩ := hc
    cases hst
    obtain ⟨mst, hmst, hmprv⟩ := hR.conf.mstatus
    obtain ⟨sec, hsec, hpmm⟩ := hR.conf.mseccfg
    let st := T s m.pc
    have hmst' : st.regs.get? mstatus = some mst := by rw [T_get? (by decide) (by decide)]; exact hmst
    have hpriv : st.regs.get? cur_privilege = some .Machine := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.privilege
    have hsec' : st.regs.get? mseccfg = some sec := by rw [T_get? (by decide) (by decide)]; exact hsec
    have hpma : st.regs.get? pma_regions = some zesuPmaRegions := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.pma
    have hag := RegsAgree.T (m := m) hR.regs m.pc
    have addrReg : Runs (get_transformed_data_addr (rg rs1) (sign_extend (m := 64) imm)
        (Store Data) 2) st st (.Ext_DataAddr_OK (virtaddr.Virtaddr (m.reg rs1 + Machine.sx imm))) :=
      get_transformed_data_addr_machine_data_run .store st (rg rs1) 2 (m.reg rs1)
        (sign_extend (m := 64) imm) mst sec (rX_rg_run hag rs1) hmst' hpriv hmprv hsec' hpmm
    have hal' := aligned_of_mod hal
    have physAccess := phys_access_check_machine_store_allowed st _ 2 (storePma hpma hwr) hal'.2
    refine sim_store_of_exec hR hw hd hpc (data := (Sail.BitVec.extractLsb (m.reg rs2) 15 0 : BitVec (8 * 2))) hwr
      (fun j hj => by
        apply BitVec.eq_of_toNat_eq
        simp only [Sail.BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
        have : j = 0 ∨ j = 1 := by omega
        rcases this with rfl|rfl <;> simp <;> omega) ?_ n
    change Runs (execute_STORE imm (rg rs2) (rg rs1) 2) _ _ _
    exact execute_STORE_half_aligned_run st _ (rg rs2) (rg rs1) imm _ mst (m.reg rs2) hmst' hpriv hmprv
      (rX_rg_run hag rs2) addrReg hal'.1 physAccess (writeBytes_run_exact st _ _)
  · cases hst

theorem sim_sb {rs1 rs2 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sb rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.storeFrom, Option.map_eq_some_iff] at hex
  obtain ⟨m1, hst, rfl⟩ := hex
  unfold Machine.store at hst
  split at hst
  · rename_i hc
    obtain ⟨hal, hwr, _⟩ := hc
    cases hst
    obtain ⟨mst, hmst, hmprv⟩ := hR.conf.mstatus
    obtain ⟨sec, hsec, hpmm⟩ := hR.conf.mseccfg
    let st := T s m.pc
    have hmst' : st.regs.get? mstatus = some mst := by rw [T_get? (by decide) (by decide)]; exact hmst
    have hpriv : st.regs.get? cur_privilege = some .Machine := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.privilege
    have hsec' : st.regs.get? mseccfg = some sec := by rw [T_get? (by decide) (by decide)]; exact hsec
    have hpma : st.regs.get? pma_regions = some zesuPmaRegions := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.pma
    have hag := RegsAgree.T (m := m) hR.regs m.pc
    have addrReg : Runs (get_transformed_data_addr (rg rs1) (sign_extend (m := 64) imm)
        (Store Data) 1) st st (.Ext_DataAddr_OK (virtaddr.Virtaddr (m.reg rs1 + Machine.sx imm))) :=
      get_transformed_data_addr_machine_data_run .store st (rg rs1) 1 (m.reg rs1)
        (sign_extend (m := 64) imm) mst sec (rX_rg_run hag rs1) hmst' hpriv hmprv hsec' hpmm
    have hal' := aligned_of_mod hal
    have physAccess := phys_access_check_machine_store_allowed st _ 1 (storePma hpma hwr) hal'.2
    refine sim_store_of_exec hR hw hd hpc (data := (Sail.BitVec.extractLsb (m.reg rs2) 7 0 : BitVec (8 * 1))) hwr
      (fun j hj => by
        apply BitVec.eq_of_toNat_eq
        simp only [Sail.BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
        have : j = 0 := by omega
        rcases this with rfl <;> simp <;> omega) ?_ n
    change Runs (execute_STORE imm (rg rs2) (rg rs1) 1) _ _ _
    exact execute_STORE_byte_run st _ (rg rs2) (rg rs1) imm _ mst (m.reg rs2) hmst' hpriv hmprv
      (rX_rg_run hag rs2) addrReg physAccess (writeBytes_run_exact st _ _)
  · cases hst

end ZesuExec.SailLink
