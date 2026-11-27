import ZesuExec.Compliance.F6
import ZesuExec.Fn.F6.Sail
import ZesuExec.Compliance.F3
import ZesuExec.Compliance.F2
import ZesuExec.Fn.F0.Proof
import ZesuExec.Fn.F0.Sail
import ZesuExec.Fn.F1.Proof
import ZesuExec.Fn.F1.Sail
import ZesuExec.Fn.F2.Proof
import ZesuExec.Fn.F2.Sail
import ZesuExec.Fn.F3.Proof
import ZesuExec.Fn.F3.Sail
import ZesuExec.Fn.F4.Proof
import ZesuExec.Fn.F4.Sail
import ZesuExec.Fn.F5.Proof
import ZesuExec.Fn.F5.Sail
import ZesuExec.Sail.Run
import ZesuExec.Sail.Step
import ZesuExec.Sym.Sound
import ZesuExec.Sym.Summary
import ZesuExec.Vc.Sound
import ZesuExec.Vc.SoundW
import ZesuExec.Fn.F1.Vc
import ZesuExec.Fn.DTF.Reach

/-! Axiom guards for every end theorem (plan Verification item 4). -/

/--
info: 'ZesuExec.Sym.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Sym.run_sound

/--
info: 'ZesuExec.SailLink.sail_step_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.SailLink.sail_step_sim

/--
info: 'ZesuExec.SailLink.sail_reaches' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.SailLink.sail_reaches

/--
info: 'ZesuExec.Fn.F0.f0_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F0.f0_spec

/--
info: 'ZesuExec.Fn.F0.f0_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F0.f0_sail

/--
info: 'ZesuExec.Fn.F1.f1_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F1.f1_spec

/--
info: 'ZesuExec.Fn.F1.f1_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F1.f1_sail

/--
info: 'ZesuExec.Fn.F2.f2_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F2.f2_spec

/--
info: 'ZesuExec.Fn.F2.f2_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F2.f2_sail

/--
info: 'ZesuExec.Fn.F3.f3_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F3.f3_spec

/--
info: 'ZesuExec.Fn.F3.f3_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F3.f3_sail

/--
info: 'ZesuExec.Fn.F4.f4_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F4.f4_spec

/--
info: 'ZesuExec.Fn.F4.f4_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F4.f4_sail

/--
info: 'ZesuExec.Fn.F5.f5_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F5.f5_spec

/--
info: 'ZesuExec.Fn.F5.f5_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F5.f5_sail

/--
info: 'ZesuExec.Compliance.F2.f2_compliance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Compliance.F2.f2_compliance

/--
info: 'ZesuExec.Compliance.F2.f2_compliance_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Compliance.F2.f2_compliance_sail

/--
info: 'ZesuExec.Compliance.F3.f3_compliance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Compliance.F3.f3_compliance

/--
info: 'ZesuExec.Compliance.F3.f3_compliance_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Compliance.F3.f3_compliance_sail

/--
info: 'ZesuExec.Fn.F6.f6_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F6.f6_spec

/--
info: 'ZesuExec.Fn.F6.f6_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F6.f6_sail

/--
info: 'ZesuExec.Compliance.F6.f6_compliance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Compliance.F6.f6_compliance

/--
info: 'ZesuExec.Compliance.F6.f6_compliance_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Compliance.F6.f6_compliance_sail

/--
info: 'ZesuExec.Vc.vc_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Vc.vc_sound

/--
info: 'ZesuExec.Fn.F2.F2.reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F2.F2.reach

/--
info: 'ZesuExec.Fn.F1.F1.reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F1.F1.reach

/--
info: 'ZesuExec.Sym.Match.generalise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Sym.Match.generalise

/--
info: 'ZesuExec.Sym.Match.generalise_to' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Sym.Match.generalise_to

/--
info: 'ZesuExec.Sym.runWith_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Sym.runWith_sound

/--
info: 'ZesuExec.Vc.vc_soundW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Vc.vc_soundW

/--
info: 'ZesuExec.Fn.F6.F6.reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.F6.F6.reach

/--
info: 'ZesuExec.Fn.DTF.DTF.reach_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZesuExec.Fn.DTF.DTF.reach_from
