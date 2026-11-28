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

/-- Words of the forms added in S12 and S12b, taken from functions outside the image (address,
word, mnemonic as `llvm-objdump -M no-aliases` prints them). -/
def s12Samples : List (Nat × Nat × String) :=
  [(0x800059e0, 0x00a64633, "xor"), (0x800053a0, 0xfff38e9b, "addiw"),
   (0x800053b0, 0x020f5c63, "bge"), (0x800059bc, 0x01096603, "lwu"),
   (0x80003df4, 0x0186d39b, "srliw"), (0x800061b4, 0x40c5053b, "subw"),
   (0x80011bfc, 0xf7e41703, "lh"), (0x80003224, 0x080a6693, "ori"),
   (0x8000862c, 0x0186d6b3, "srl"), (0x8000fa1c, 0x02b555b3, "divu"),
   (0x80019c78, 0x0219f533, "remu"), (0x8001fb44, 0x002d149b, "slliw"),
   (0x80024be4, 0x000da513, "slti"), (0x8000f9d8, 0x01702633, "slt"),
   (0x8000db90, 0x43f6d693, "srai"), (0x80031f24, 0x438a5913, "srai"),
   (0x800e9060, 0x6b86d593, "rev8"), (0x800e9068, 0x6b875813, "rev8"),
   (0x800e1800, 0x0ac7f633, "maxu"), (0x8010381c, 0x0bea78b3, "maxu"),
   (0x800e8fe0, 0x094ac933, "pack"), (0x800e8fe4, 0x096bcfb3, "pack"),
   (0x800e18d8, 0x0862f2b3, "packh"), (0x800e8d00, 0x0858f0b3, "packh"),
   (0x800e5b68, 0x49465633, "bext"), (0x800f0470, 0x4956d6b3, "bext"),
   (0x800e5b88, 0x29461633, "bset"), (0x800e5c94, 0x294014b3, "bset"),
   (0x800e8a34, 0x4bf51a93, "bclri"), (0x8010f7e4, 0x4a079793, "bclri"),
   (0x8010f910, 0x60069793, "clz"), (0x8010f91c, 0x60061f13, "clz")]

theorem decode_s12_samples : s12Samples.all mnemonicAgrees = true := by decide +kernel

end ZesuExec.Test
