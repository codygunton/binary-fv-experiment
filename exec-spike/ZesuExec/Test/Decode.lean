import ZesuExec.Image.Gen
import ZesuExec.Image.Expected

/-!
Every emitted word decodes, and to the constructor `llvm-objdump -M no-aliases` names.
The one exception is `memcpy`'s `csrrs`, which must not decode (it is never executed by
`step`; `next` substitutes `ziskMemcpy` at `Layout.memcpyEntry`).
-/

namespace ZesuExec.Test

def decodeAgrees : Nat × Nat × String → Bool
  | (pc, w, mn) =>
    zesuImage.word? pc == some w &&
    match decodeNat w with
    | some i => i.mnemonic == mn
    | none => mn == "csrrs"

theorem decode_table : Expected.table.all decodeAgrees = true := by decide +kernel

theorem decode_table_size : Expected.table.length = 1572 := by decide +kernel

end ZesuExec.Test
