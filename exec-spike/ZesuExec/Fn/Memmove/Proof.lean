import ZesuExec.Fn.SvcSteps
import ZesuExec.Image.Gen

/-!
# `memmove` (`0x800e06d0`, 3 instructions) against the CSR `0x813` definition

    800e06d0: 8135a073  csrs 0x813, a1
    800e06d4: 00c50033  add  zero, a0, a2
    800e06d8: 00008067  ret

The first two words are one `csr813` step (register form: destination `x10`, source `x11`, count
`x12`), the third a return. The result is exactly `ziskMemcpy`'s, so `memmove` meets `memcpy`'s
contract (`MemcpyPre`, `MemcpyPost`): ZisK's DMA copy reads a snapshot of the source, so
overlapping ranges are moved correctly (`Machine.copyMem`, `dmaMemcpyMem`).
-/

namespace ZesuExec.Fn.Memmove
open ZesuExec ZesuExec.Sym

def entry : Nat := 0x800e06d0
def bound : Nat := 3

theorem fetch0 : fetchI zesuImage entry = none := by decide +kernel
theorem fetch2 : fetchI zesuImage (entry + 8) = some (.jalr 0 1 0) := by decide +kernel
theorem svcw0 : Svc.fetch zesuImage entry = some 0x8135a073 := by decide +kernel
theorem svcw1 : Svc.fetch zesuImage (entry + 4) = some 0x00c50033 := by decide +kernel

theorem memmove_spec : Spec zesuImage entry bound MemcpyPre MemcpyPost := by
  intro m hpc hpre
  have hd := hpre
  simp only [MemcpyPre, ziskMemcpyDomain, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hal, hew⟩, hep⟩, hn⟩ := hd
  -- the service step
  let e : SvcEffect :=
    { addrs := (List.range 8).map (Layout.extraParams + ·) ++
        (List.range (m.reg 12).toNat).map ((m.reg 10).toNat + ·),
      mem := dmaMemcpyMem m.mem (m.reg 10).toNat (m.reg 11).toNat (m.reg 12),
      pc := m.pc + 8, cost := 2 }
  have he : svc zesuImage m = some e := by
    have h813 : csr813 zesuImage m = some e := by
      unfold csr813
      rw [hpc, svcw0, svcw1]
      simp only [show Svc.isCsrs 0x8135a073 0x813 = true by decide,
        show Svc.isAddX0 0x00c50033 = true by decide, if_true,
        show Decode.reg 0x8135a073 15 = 11 by decide, show Decode.reg 0x00c50033 15 = 10 by decide,
        show Decode.reg 0x00c50033 20 = 12 by decide]
      rw [if_pos]
      simp only [dmaMemcpyDomain, Bool.and_eq_true]
      exact ⟨⟨hew, hep⟩, hn⟩
    simp [svc, h813]
  have hmc : m.pc.toNat ≠ Layout.memcpyEntry := by rw [hpc]; decide
  have hn1 := next_svc hmc (by rw [hpc]; exact fetch0) he
  -- the return
  have hpc1 : (e.apply m).pc.toNat = entry + 8 := by
    simp only [SvcEffect.apply, e]
    rw [BitVec.toNat_add, hpc]; simp [entry]
  have hmc1 : (e.apply m).pc.toNat ≠ Layout.memcpyEntry := by rw [hpc1]; decide
  have hal' : ((e.apply m).reg 1 + BitVec.signExtend 64 (0 : BitVec 12) &&& ~~~(1 : Word)).toNat
      % 4 = 0 := by
    simpa [SvcEffect.apply, e, Machine.setReg, Machine.reg] using hal
  have hn2 := next_exec hmc1 (by rw [hpc1]; exact fetch2)
    (show (e.apply m).exec (.jalr 0 1 0) = some
      { e.apply m with pc := (e.apply m).reg 1 + BitVec.signExtend 64 (0 : BitVec 12) &&& ~~~1 } by
      simp only [Machine.exec, Machine.jumpTo, Machine.setReg, Machine.sx]
      simp only [show ((0 : Fin 32).val = 0) from rfl, if_true]
      rw [if_pos hal'])
  refine ⟨3, _, Nat.le_refl _, RunsIn.step hn1 (RunsIn.step hn2 .refl), ?_⟩
  simp only [MemcpyPost, ziskMemcpy, show ziskMemcpyDomain m = true from hpre, if_true,
    Option.some.injEq]
  simp [SvcEffect.apply, e, Machine.setReg, Machine.reg, ziskMemcpyMem_eq]

end ZesuExec.Fn.Memmove
