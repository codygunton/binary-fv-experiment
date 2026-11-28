import ZesuExec.Sym.Sound

/-!
# One `next` at a time: an ordinary instruction or a registry service step

For hand proofs of short functions over service steps (`memmove`, `memset`): `next_exec` takes
an instruction the decoder knows, `next_svc` a service step at a word it does not.
-/

namespace ZesuExec.Fn
open ZesuExec ZesuExec.Sym

theorem next_exec {img : Image} {m m' : Machine} {i : Instr}
    (hmc : m.pc.toNat ≠ Layout.memcpyEntry) (hf : fetchI img m.pc.toNat = some i)
    (hx : m.exec i = some m') : next img m = some (m', 1) := by
  simp [next, hmc, fetch_step rfl hf, hx]

theorem step_none {img : Image} {m : Machine} (hf : fetchI img m.pc.toNat = none) :
    step img m = none := by
  unfold fetchI at hf
  unfold step
  split at hf
  · rename_i hr
    rw [if_pos hr]
    split at hf
    · rename_i w hw; rw [hw]; simp only; rw [hf]
    · rename_i hw; rw [hw]
  · rename_i hr; rw [if_neg hr]

theorem next_svc {img : Image} {m : Machine} {e : SvcEffect}
    (hmc : m.pc.toNat ≠ Layout.memcpyEntry) (hf : fetchI img m.pc.toNat = none)
    (he : svc img m = some e) : next img m = some (e.apply m, e.cost) := by
  simp [next, hmc, step_none hf, he]

end ZesuExec.Fn
