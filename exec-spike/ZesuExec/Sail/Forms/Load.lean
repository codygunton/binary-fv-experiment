import ZesuExec.Sail.Forms.Mem

/-!
# Simulation of the loads

`ld lw lhu lbu lb`: `Machine.load` succeeds only for a naturally aligned range inside rodata,
input or RAM whose bytes are all present; `Rel.mem` puts those bytes in Sail's byte map, the
profile's PMA regions admit the read, and the generated load returns their little-endian value.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType mem_payload

variable {img : Image} {m m' : Machine} {s : State} {w : Nat}

theorem sim_ld {rd rs1 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.ld rd rs1 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.loadInto, Option.map_eq_some_iff] at hex
  obtain ⟨v, hl, rfl⟩ := hex
  unfold Machine.load at hl
  split at hl
  · rename_i hc
    obtain ⟨hal, hrd⟩ := hc
    simp only [Option.map_eq_some_iff] at hl
    obtain ⟨bs, hbs, rfl⟩ := hl
    obtain ⟨hlen, hbytes⟩ := readBytes_spec _ _ _ hbs
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ :
        ∃ b0 b1 b2 b3 b4 b5 b6 b7, bs = [b0, b1, b2, b3, b4, b5, b6, b7] := by
      match bs, hlen with
      | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨_, _, _, _, _, _, _, _, rfl⟩
    refine sim_wreg hR hw hd hpc ?_ n
    obtain ⟨mst, hmst, hmprv⟩ := hR.conf.mstatus
    obtain ⟨sec, hsec, hpmm⟩ := hR.conf.mseccfg
    have hrange : (m.reg rs1 + Machine.sx imm).toNat + 8 ≤ 2 ^ 64 := by
      simp only [Machine.readable, Machine.inRange, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, Layout.rodataLo, Layout.rodataHi, Layout.inputLo, Layout.inputHi,
        Layout.ramLo, Layout.ramHi] at hrd
      omega
    let st := T s m.pc
    have hmst' : st.regs.get? mstatus = some mst := by rw [T_get? (by decide) (by decide)]; exact hmst
    have hpriv : st.regs.get? cur_privilege = some .Machine := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.privilege
    have hsec' : st.regs.get? mseccfg = some sec := by rw [T_get? (by decide) (by decide)]; exact hsec
    have hpma : st.regs.get? pma_regions = some zesuPmaRegions := by
      rw [T_get? (by decide) (by decide)]; exact hR.conf.pma
    have addrReg : Runs (get_transformed_data_addr (rg rs1) (sign_extend (m := 64) imm)
        (Load Data) 8) st st (.Ext_DataAddr_OK (virtaddr.Virtaddr (m.reg rs1 + Machine.sx imm))) := by
      exact get_transformed_data_addr_machine_data_run .load st (rg rs1) 8 (m.reg rs1)
        (sign_extend (m := 64) imm) mst sec (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1)
        hmst' hpriv hmprv hsec' hpmm
    have hal' := aligned_of_mod hal
    have hmem : ∀ (i : Nat) (h : i < [b0, b1, b2, b3, b4, b5, b6, b7].length),
        st.mem.get? ((m.reg rs1 + Machine.sx imm).toNat + i) =
          some [b0, b1, b2, b3, b4, b5, b6, b7][i] :=
      fun i h => hR.memAt (by simp at h; omega) (hbytes i h)
    have hmr := mem_read_load_run st (m.reg rs1 + Machine.sx imm) mst
      [b0, b1, b2, b3, b4, b5, b6, b7] hmst' hpriv hmprv hmem
      (phys_access_check_machine_load_allowed st _ 8 (loadPma hpma (by decide) hrd) hal'.2)
    have hread := vmem_read_dword_run st (rg rs1) _ _ mst _ hmst' hpriv hmprv addrReg hal'.1 hmr
    have hval : (leWord [b0, b1, b2, b3, b4, b5, b6, b7] : BitVec 64) =
        Machine.ofBytesLE [b0, b1, b2, b3, b4, b5, b6, b7] :=
      BitVec.eq_of_toNat_eq (by rw [toNat_leWord]; exact (toNat_ofBytesLE _ (by simp)).symm)
    change Runs (execute_LOAD imm (rg rs1) (rg rd) false 8) _ _ _
    refine execute_LOAD_run st _ imm (rg rs1) (rg rd) false 8 _ (by decide) hread ?_
    have hx : extend_value false (leWord [b0, b1, b2, b3, b4, b5, b6, b7] : BitVec (8 * 8)) =
        Machine.ofBytesLE [b0, b1, b2, b3, b4, b5, b6, b7] := by
      rw [← hval]; simp [extend_value, sign_extend, Sail.BitVec.signExtend]
    rw [show id (Machine.ofBytesLE [b0, b1, b2, b3, b4, b5, b6, b7]) = _ from hx.symm]
    exact wX_rg_run st rd _
  · cases hl

end ZesuExec.SailLink
