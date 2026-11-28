import ZesuExec.Image.Gen
import ZesuExec.Image.Expected

/-!
Every emitted word decodes, and to the constructor `llvm-objdump -M no-aliases` names.
The one exception is `memcpy`'s `csrrs`, which must not decode (it is never executed by
`step`; `next` substitutes `ziskMemcpy` at `Layout.memcpyEntry`).

The check is split in two linear passes (a per-entry `zesuImage.word?` lookup is quadratic in the
segment length and exceeds the kernel's budget once `decodeTxFields` is in the image): the
`(pc, word)` pairs of the table are exactly those of the image's segments, in order, and every
table word decodes to the table's mnemonic.
-/

namespace ZesuExec.Test

/-- The `(pc, word)` pairs of an image's code segments, in segment order. -/
def pairsOf (img : Image) : List (Nat × Nat) :=
  img.text.flatMap fun s => ((List.range s.words.length).zip s.words).map fun (i, w) => (s.base + 4 * i, w)

def mnemonicAgrees : Nat × Nat × String → Bool
  | (_, w, mn) =>
    match decodeNat w with
    | some i => i.mnemonic == mn
    | none => mn == "csrrs"

theorem table_pairs : Expected.table.map (fun e => (e.1, e.2.1)) = pairsOf zesuImage := by
  decide +kernel

theorem decode_table : Expected.table.all mnemonicAgrees = true := by decide +kernel

theorem decode_table_size : Expected.table.length = 4397 := by decide +kernel

/-- Words of the forms added in S12, taken from functions outside the image (address, word,
mnemonic as `llvm-objdump -M no-aliases` prints them). -/
def s12Samples : List (Nat × Nat × String) :=
  [(0x800059e0, 0x00a64633, "xor"), (0x800053a0, 0xfff38e9b, "addiw"),
   (0x800053b0, 0x020f5c63, "bge"), (0x800059bc, 0x01096603, "lwu"),
   (0x80003df4, 0x0186d39b, "srliw"), (0x800061b4, 0x40c5053b, "subw"),
   (0x80011bfc, 0xf7e41703, "lh"), (0x80003224, 0x080a6693, "ori"),
   (0x8000862c, 0x0186d6b3, "srl"), (0x8000fa1c, 0x02b555b3, "divu"),
   (0x80019c78, 0x0219f533, "remu")]

theorem decode_s12_samples : s12Samples.all mnemonicAgrees = true := by decide +kernel

end ZesuExec.Test
