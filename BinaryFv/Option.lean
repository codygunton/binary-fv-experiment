/-!
# Transport across computed `Option` dispatch

These lemmas keep a computed scrutinee out of a caller's rewrite motive. This matters when the
scrutinee parses an ELF, resolves symbols, or decodes a generated program: unfolding and rewriting
the concrete computation can make the kernel repeat it at every use site.
-/

namespace BinaryFv.Option

theorem getD_map_of_eq_some {α β : Type _} {o : Option α} {f : α → β} {a : α} {d : β}
    (ho : o = some a) : (o.map f).getD d = f a := by
  subst ho
  rfl

theorem getD_map_eq_true_of_eq_some {α : Type _} {o : Option α} {f : α → Bool} {a : α}
    (ho : o = some a) (h : (o.map f).getD false = true) : f a = true := by
  rw [getD_map_of_eq_some ho] at h
  exact h

end BinaryFv.Option

namespace BinaryFv.Except

theorem getD_map_toOption_of_eq_ok {ε α β : Type _} {e : Except ε α} {f : α → β} {a : α}
    {d : β} (he : e = .ok a) : (e.toOption.map f).getD d = f a := by
  subst he
  rfl

theorem getD_map_toOption_eq_true_of_eq_ok {ε α : Type _} {e : Except ε α}
    {f : α → Bool} {a : α} (he : e = .ok a)
    (h : (e.toOption.map f).getD false = true) : f a = true := by
  rw [getD_map_toOption_of_eq_ok he] at h
  exact h

end BinaryFv.Except
