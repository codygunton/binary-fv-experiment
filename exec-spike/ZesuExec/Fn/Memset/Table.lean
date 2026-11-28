import ZesuExec.Fn.Memset.Spec

/-! # `memset`: the code facts its proof reads from `zesuImage` (kernel evaluation) -/

namespace ZesuExec.Fn.Memset
open ZesuExec ZesuExec.Sym

/-- The `addi zero, a2, b` word of table entry `b`. -/
def addiWord (b : Nat) : Nat := b * 2 ^ 20 + 0x60013

/-- The table: entry `b` is `csrs 0x816, a0; addi zero, a2, b; ret`. -/
theorem table_words : ∀ b : Fin 256,
    fetchI zesuImage (table + 16 * b.val) = none ∧
    Svc.fetch zesuImage (table + 16 * b.val) = some 0x81652073 ∧
    Svc.fetch zesuImage (table + 16 * b.val + 4) = some (addiWord b.val) ∧
    fetchI zesuImage (table + 16 * b.val + 8) = some (.jalr 0 1 0) ∧
    Svc.isAddiX0 (addiWord b.val) = true ∧ Decode.reg (addiWord b.val) 15 = 12 ∧
    Svc.byteImm? (addiWord b.val) = some (BitVec.ofNat 8 b.val) := by
  decide +kernel

theorem fetch_bne : fetchI zesuImage 0x800e06f0 = some (.bne 11 0 16) := by decide +kernel
theorem fetch_zero_csr : fetchI zesuImage 0x800e06f4 = none := by decide +kernel
theorem svc_zero_w0 : Svc.fetch zesuImage 0x800e06f4 = some 0x81652073 := by decide +kernel
theorem svc_zero_w1 : Svc.fetch zesuImage 0x800e06f8 = some 0x00060013 := by decide +kernel
theorem fetch_zero_ret : fetchI zesuImage 0x800e06fc = some (.jalr 0 1 0) := by decide +kernel
theorem fetch_andi : fetchI zesuImage 0x800e0700 = some (.andi 11 11 0xff) := by decide +kernel
theorem fetch_slli : fetchI zesuImage 0x800e0704 = some (.slli 11 11 4) := by decide +kernel
theorem fetch_auipc : fetchI zesuImage 0x800e0708 = some (.auipc 5 0) := by decide +kernel
theorem fetch_addi : fetchI zesuImage 0x800e070c = some (.addi 5 5 0x18) := by decide +kernel
theorem fetch_add : fetchI zesuImage 0x800e0710 = some (.add 5 5 11) := by decide +kernel
theorem fetch_jr : fetchI zesuImage 0x800e0714 = some (.jalr 0 5 0) := by decide +kernel

end ZesuExec.Fn.Memset
