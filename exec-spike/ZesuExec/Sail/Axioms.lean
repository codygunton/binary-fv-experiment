import ZesuExec.Sail.Run

/-! Gate S3 (rule 4): the end theorems of the Sail link use only the standard axioms. -/

/-- info: 'ZesuExec.SailLink.decode_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ZesuExec.SailLink.decode_sound

/-- info: 'ZesuExec.SailLink.sail_step_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ZesuExec.SailLink.sail_step_sim

/-- info: 'ZesuExec.SailLink.sail_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ZesuExec.SailLink.sail_reaches
