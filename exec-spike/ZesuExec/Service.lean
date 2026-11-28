import ZesuExec.Service.Memcpy
import ZesuExec.Service.Memset
import ZesuExec.Service.Sha256f
import ZesuExec.Service.Arch

/-!
# The ZisK service registry and the machine's `next`

The trusted definitions about ZisK, one file per CSR number under `ZesuExec/Service/`, each citing
the ZisK source (`/home/cody/zisk`, commit `eed62f4d9`) it transcribes:

| CSR | file | service |
|---|---|---|
| `0x813` | `Memcpy.lean` | DMA `memcpy` (register and immediate count); `ziskMemcpy` at `memcpy`'s entry |
| `0x816` | `Memset.lean` | DMA `memset` (register and immediate count) |
| `0x805` | `Sha256f.lean` | SHA-256 compression |
| `0xf12` | `Arch.lean` | `marchid` read; also the exit `ecall` and `ZiskBoot` |

`tools/svc_test.py` runs each against `ziskemu`. `next` takes one transition: the function-level
`memcpy` service at its entry (cost 3), else an ordinary instruction (cost 1), else a service step
(`svc`) at a word the decoder does not know.
-/

namespace ZesuExec

/-- The service step at `m.pc`, if any. -/
def svc (img : Image) (m : Machine) : Option SvcEffect :=
  (csr813 img m).orElse fun _ => (csr816 img m).orElse fun _ =>
    (csr805 img m).orElse fun _ => csrF12 img m

/-- One machine transition and its cost in instructions. -/
def next (img : Image) (m : Machine) : Option (Machine × Nat) :=
  if m.pc.toNat = Layout.memcpyEntry then (ziskMemcpy m).map (·, 3)
  else
    match step img m with
    | some m' => some (m', 1)
    | none => (svc img m).map fun e => (e.apply m, e.cost)

end ZesuExec
