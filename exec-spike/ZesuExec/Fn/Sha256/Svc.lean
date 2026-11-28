import ZesuExec.Fn.Sha256.Mid

/-!
# `zkvm_sha256`: its service steps, as `next` takes them

One lemma per form the function uses: CSR `0x813` with an immediate and with a register count,
CSR `0x816` with an immediate count, CSR `0x805`. Each takes the site's words (checked by
`decide` where it is used) and the domain facts, and states the machine after the step.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

theorem setReg_zero (m : Machine) (v : Word) : m.setReg 0 v = m := by
  simp [Machine.setReg]

theorem csr813_none {m : Machine} {w : Nat} (hw : Svc.fetch zesuImage m.pc.toNat = some w)
    (h : Svc.isCsrs w 0x813 = false) : csr813 zesuImage m = none := by
  unfold csr813; rw [hw]
  cases Svc.fetch zesuImage (m.pc.toNat + 4) <;> simp [h]

theorem csr816_none {m : Machine} {w : Nat} (hw : Svc.fetch zesuImage m.pc.toNat = some w)
    (h1 : Svc.isCsrs w 0x816 = false) (h2 : Svc.isCsrsi816 w = false) :
    csr816 zesuImage m = none := by
  unfold csr816; rw [hw]
  cases Svc.fetch zesuImage (m.pc.toNat + 4) <;> simp [h1, h2]

/-- CSR `0x813`, immediate count `n`: copy `[s, s+n)` to `[d, d+n)`. -/
theorem next_813i {m : Machine} {w0 w1 : Nat}
    (hmc : m.pc.toNat ≠ Layout.memcpyEntry) (hf : fetchI zesuImage m.pc.toNat = none)
    (h0 : Svc.fetch zesuImage m.pc.toNat = some w0)
    (h1 : Svc.fetch zesuImage (m.pc.toNat + 4) = some w1)
    (hc : Svc.isCsrs w0 0x813 = true) (ha : Svc.isAddX0 w1 = false)
    (hi : Svc.isAddiX0 w1 = true ∧ 0 ≤ Svc.immInt w1)
    {s d n : Nat} (hs : (m.reg (Decode.reg w0 15)).toNat = s)
    (hd : (m.reg (Decode.reg w1 15)).toNat = d) (hn : (Svc.immInt w1).toNat = n)
    (hsrc : srcOk m.mem s n = true) (hdst : dstOk m.mem d n = true) :
    next zesuImage m = some ({ m with mem := copyMem m.mem d s n, pc := m.pc + 8 }, 2) := by
  have he : csr813 zesuImage m = some ⟨0, 0, (List.range n).map (d + ·),
      copyMem m.mem d s n, m.pc + 8, 2⟩ := by
    unfold csr813; rw [h0, h1]
    simp only [hc, ha, if_true, if_false, hi, and_self, hs, hd, hn, Bool.false_eq_true]
    rw [if_pos (by simp [hsrc, hdst])]
  rw [next_svc hmc hf (show svc zesuImage m = _ by simp only [svc, he]; rfl)]
  simp [SvcEffect.apply, setReg_zero]

/-- CSR `0x813`, register count: stage the count, then copy. -/
theorem next_813r {m : Machine} {w0 w1 : Nat}
    (hmc : m.pc.toNat ≠ Layout.memcpyEntry) (hf : fetchI zesuImage m.pc.toNat = none)
    (h0 : Svc.fetch zesuImage m.pc.toNat = some w0)
    (h1 : Svc.fetch zesuImage (m.pc.toNat + 4) = some w1)
    (hc : Svc.isCsrs w0 0x813 = true) (ha : Svc.isAddX0 w1 = true)
    (hdom : dmaMemcpyDomain m.mem (m.reg (Decode.reg w1 15)).toNat (m.reg (Decode.reg w0 15)).toNat
      (m.reg (Decode.reg w1 20)).toNat = true) :
    next zesuImage m = some ({ m with
      mem := dmaMemcpyMem m.mem (m.reg (Decode.reg w1 15)).toNat (m.reg (Decode.reg w0 15)).toNat
        (m.reg (Decode.reg w1 20)), pc := m.pc + 8 }, 2) := by
  have he : csr813 zesuImage m = some ⟨0, 0, (List.range 8).map (Layout.extraParams + ·) ++
        (List.range (m.reg (Decode.reg w1 20)).toNat).map ((m.reg (Decode.reg w1 15)).toNat + ·),
      dmaMemcpyMem m.mem (m.reg (Decode.reg w1 15)).toNat (m.reg (Decode.reg w0 15)).toNat
        (m.reg (Decode.reg w1 20)), m.pc + 8, 2⟩ := by
    unfold csr813; rw [h0, h1]
    simp only [hc, ha, if_true]
    rw [if_pos hdom]
  rw [next_svc hmc hf (show svc zesuImage m = _ by simp only [svc, he]; rfl)]
  simp [SvcEffect.apply, setReg_zero]

/-- CSR `0x816`, immediate count `n`: fill `[d, d+n)` with `b`. -/
theorem next_816i {m : Machine} {w0 w1 w2 : Nat} {b : Byte}
    (hmc : m.pc.toNat ≠ Layout.memcpyEntry) (hf : fetchI zesuImage m.pc.toNat = none)
    (h0 : Svc.fetch zesuImage m.pc.toNat = some w0)
    (h1 : Svc.fetch zesuImage (m.pc.toNat + 4) = some w1)
    (h2 : Svc.fetch zesuImage (m.pc.toNat + 8) = some w2)
    (hn813 : Svc.isCsrs w0 0x813 = false) (hn816 : Svc.isCsrs w0 0x816 = false)
    (hc : Svc.isCsrsi816 w0 = true) (ha : Svc.isAddiX0 w1 = true) (hi : 0 ≤ Svc.immInt w1)
    (hb : Svc.byteImm? w2 = some b) {d n : Nat} (hd : (m.reg (Decode.reg w1 15)).toNat = d)
    (hn : (Svc.immInt w1).toNat = n) (hdst : dstOk m.mem d n = true) :
    next zesuImage m = some (
      { m with mem := fillMem m.mem d n b, pc := m.pc + BitVec.ofNat 64 12 }, 3) := by
  have he : csr816 zesuImage m = some ⟨0, 0, (List.range n).map (d + ·),
      fillMem m.mem d n b, m.pc + BitVec.ofNat 64 12, 3⟩ := by
    unfold csr816; rw [h0, h1]
    simp only [hn816, hc, ha, hi, Bool.false_eq_true, false_and, if_false,
      and_self, if_true, h2, hb, hd, hn, memsetEffect, hdst, Bool.or_true]
  rw [next_svc hmc hf (show svc zesuImage m = _ by simp only [svc, csr813_none h0 hn813, he]; rfl)]
  simp [SvcEffect.apply, setReg_zero]

/-- CSR `0x805`: compress the 64-byte block at `inp` into the state at `st`. -/
theorem next_805 {m : Machine} {w0 : Nat}
    (hmc : m.pc.toNat ≠ Layout.memcpyEntry) (hf : fetchI zesuImage m.pc.toNat = none)
    (h0 : Svc.fetch zesuImage m.pc.toNat = some w0)
    (hn813 : Svc.isCsrs w0 0x813 = false) (hn816 : Svc.isCsrs w0 0x816 = false)
    (hn816i : Svc.isCsrsi816 w0 = false) (hc : Svc.isCsrs w0 0x805 = true)
    {p st inp : Nat} {pb ib sb blk : List Byte} (hp : (m.reg (Decode.reg w0 15)).toNat = p)
    (hp8 : p % 8 = 0) (hpok : srcOk m.mem p 16 = true)
    (hpb : readBytes m.mem p 8 = some pb) (hib : readBytes m.mem (p + 8) 8 = some ib)
    (hst : (ofBytesLE pb).toNat = st) (hin : (ofBytesLE ib).toNat = inp)
    (hst8 : st % 8 = 0) (hin8 : inp % 8 = 0) (hdst : dstOk m.mem st 32 = true)
    (hsrc : srcOk m.mem inp 64 = true)
    (hsb : readBytes m.mem st 32 = some sb) (hblk : readBytes m.mem inp 64 = some blk) :
    next zesuImage m = some ({ m with
      mem := putBytes m.mem st 32 (Sha256.leBytes
        (Sha256.sha256Compress ((List.range 8).map (Sha256.leWord sb)) blk)),
      pc := m.pc + 4 }, 1) := by
  have he : csr805 zesuImage m = some ⟨0, 0, (List.range 32).map (st + ·),
      putBytes m.mem st 32 (Sha256.leBytes
        (Sha256.sha256Compress ((List.range 8).map (Sha256.leWord sb)) blk)), m.pc + 4, 1⟩ := by
    unfold csr805; rw [h0]
    simp only [hc, if_true, hp]
    rw [if_pos ⟨hp8, hpok⟩, hpb, hib]
    simp only [hst, hin]
    rw [if_pos ⟨hst8, hin8, hdst, hsrc⟩, hsb, hblk]
  rw [next_svc hmc hf (show svc zesuImage m = _ by
    simp only [svc, csr813_none h0 hn813, csr816_none h0 hn816 hn816i, he]; rfl)]
  simp [SvcEffect.apply, setReg_zero]

end ZesuExec.Fn.Sha256
