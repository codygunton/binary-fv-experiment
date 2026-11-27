import Lean

/-!
# Functions proved in the spike without a plan (programme plan S2 step 5)

`zesu-status` lists these with `"legacy": true`. The names are checked to exist in
`ZesuExec.Test.Vc`.
-/

namespace ZesuExec.Vc
open Lean

structure LegacyFn where
  /-- spike id -/
  fn : String
  entry : Nat
  spec : Name
  sail : Name
  compliance : Option Name

def legacyFns : List LegacyFn := [
  ⟨"F0", 0x8004218c, `ZesuExec.Fn.F0.f0_spec, `ZesuExec.Fn.F0.f0_sail, none⟩,
  ⟨"F1", 0x800cb40c, `ZesuExec.Fn.F1.f1_spec, `ZesuExec.Fn.F1.f1_sail, none⟩,
  ⟨"F2", 0x800d6960, `ZesuExec.Fn.F2.f2_spec, `ZesuExec.Fn.F2.f2_sail,
    some `ZesuExec.Compliance.F2.f2_compliance⟩,
  ⟨"F3", 0x800d6274, `ZesuExec.Fn.F3.f3_spec, `ZesuExec.Fn.F3.f3_sail,
    some `ZesuExec.Compliance.F3.f3_compliance⟩,
  ⟨"F4", 0x800d677c, `ZesuExec.Fn.F4.f4_spec, `ZesuExec.Fn.F4.f4_sail, none⟩,
  ⟨"F5", 0x800d6554, `ZesuExec.Fn.F5.f5_spec, `ZesuExec.Fn.F5.f5_sail, none⟩,
  ⟨"F6", 0x800d5cb8, `ZesuExec.Fn.F6.f6_spec, `ZesuExec.Fn.F6.f6_sail,
    some `ZesuExec.Compliance.F6.f6_compliance⟩]

end ZesuExec.Vc
