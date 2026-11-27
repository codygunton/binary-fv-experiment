import ZesuExec.Sym.LoadStore

/-!
# Soundness of the symbolic executor

`stepI_sound`: one symbolic instruction against `Machine.exec`. `run_sound`: a whole `run`
against `RunsIn`, by induction on fuel.
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

/-! ## Registers -/

theorem SState.reg_setReg {S : SState} (hl : S.regs.length = 32) (i : Fin 32) (v : Sym)
    (j : Fin 32) :
    (S.setReg i.val v).reg j.val = if j = i ∧ i.val ≠ 0 then v else S.reg j.val := by
  unfold SState.setReg SState.reg
  by_cases hi : i.val = 0
  · simp [hi]
  · simp only [hi, if_false, ne_eq, not_false_eq_true, and_true]
    by_cases hj : j.val = 0
    · have : j ≠ i := fun e => hi (e ▸ hj)
      simp [hj, this]
    · simp only [hj, if_false, List.getD_eq_getElem?_getD, List.getElem?_set]
      by_cases e : j = i
      · subst e; simp [hl]
      · have : (i.val = j.val) = False := by
          apply propext; constructor
          · intro h; exact e (Fin.ext h.symm)
          · intro h; exact h.elim
        simp [this, e]

theorem Machine.reg_setReg (m : Machine) (i : Fin 32) (v : Word) (j : Fin 32) :
    (m.setReg i v).reg j = if j = i ∧ i.val ≠ 0 then v else m.reg j := by
  unfold Machine.setReg Machine.reg
  by_cases hi : i.val = 0
  · simp [hi]
  · simp only [hi, if_false]
    by_cases hj : j.val = 0
    · have : j ≠ i := fun e => hi (e ▸ hj)
      simp [hj, this]
    · by_cases e : j = i <;> simp [hj, e, hi]

theorem SState.setReg_regs_length {S : SState} (i : Nat) (v : Sym) :
    (S.setReg i v).regs.length = S.regs.length := by
  unfold SState.setReg; split <;> simp

@[simp] theorem SState.setReg_mem (S : SState) (i : Nat) (v : Sym) : (S.setReg i v).mem = S.mem := by
  unfold SState.setReg; split <;> rfl
@[simp] theorem SState.setReg_known (S : SState) (i : Nat) (v : Sym) :
    (S.setReg i v).known = S.known := by
  unfold SState.setReg; split <;> rfl
@[simp] theorem SState.setReg_regions (S : SState) (i : Nat) (v : Sym) :
    (S.setReg i v).regions = S.regions := by
  unfold SState.setReg; split <;> rfl
@[simp] theorem SState.setReg_steps (S : SState) (i : Nat) (v : Sym) :
    (S.setReg i v).steps = S.steps := by
  unfold SState.setReg; split <;> rfl
@[simp] theorem Machine.setReg_mem (m : Machine) (i : Fin 32) (v : Word) :
    (m.setReg i v).mem = m.mem := by
  unfold Machine.setReg; split <;> rfl
@[simp] theorem Machine.setReg_pc (m : Machine) (i : Fin 32) (v : Word) :
    (m.setReg i v).pc = m.pc := by
  unfold Machine.setReg; split <;> rfl

theorem Match.setReg {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (i : Fin 32)
    (v : Sym) (val : Word) (hv : v.eval env = val) :
    Match env (S.setReg i.val v) (m.setReg i val) where
  regsLen := by rw [SState.setReg_regs_length]; exact hm.regsLen
  regs j := by
    rw [SState.reg_setReg hm.regsLen, Machine.reg_setReg]
    split
    · exact hv
    · exact hm.regs j
  mem r j hr hj := by simpa using hm.mem r j (by simpa using hr) hj
  known := by simpa using hm.known

theorem Match.with_steps {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (k : Nat) :
    Match env { S with steps := k } m :=
  ⟨hm.regsLen, hm.regs, hm.mem, hm.known⟩

theorem Match.with_pc {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (p : Word) :
    Match env S { m with pc := p } :=
  ⟨hm.regsLen, hm.regs, hm.mem, hm.known⟩

theorem Env.WF.congr {env : Env} {S S' : SState} (hwf : Env.WF env S)
    (h : S'.regions = S.regions) : Env.WF env S' := by
  obtain ⟨a, b, c, d, e⟩ := hwf
  exact ⟨h ▸ a, b, h ▸ c, h ▸ d, h ▸ e⟩

theorem InWritable.congr {env : Env} {S S' : SState} (h : S'.regions = S.regions) :
    InWritable env S' = InWritable env S := by
  unfold InWritable; rw [h]

/-! ## Addresses -/

theorem eval_wlit (env : Env) (x : Word) : (wlit x).eval env = x := by simp [Sym.eval]

theorem pc_eq {m : Machine} {pc : Nat} (hpc : m.pc.toNat = pc) : m.pc = BitVec.ofNat 64 pc := by
  subst hpc; simp

theorem ofInt_nonneg {o : Int} (h : 0 ≤ o) : BitVec.ofInt 64 o = BitVec.ofNat 64 o.toNat := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h; simp

theorem place_cst {a : Sym} {r off : Nat} (h : place a = some (.cst r off)) (env : Env) :
    a.eval env = env.base r + BitVec.ofNat 64 off := by
  unfold place at h
  split at h
  · simp at h
  · next r' o =>
    split at h
    · next ho => simp at h; obtain ⟨rfl, rfl⟩ := h; simp [Sym.eval, ofInt_nonneg ho]
    · simp at h
  · split at h <;> simp at h
  · simp at h

theorem place_ro {a : Sym} {x : Nat} (h : place a = some (.ro x)) : a = .lit x := by
  unfold place at h
  split at h
  · simp at h; rw [h]
  · split at h <;> simp at h
  · split at h <;> simp at h
  · simp at h

theorem idxOf_spec (env : Env) (i0 : Sym) :
    ((idxOf i0).2 * ((idxOf i0).1.eval env).toNat < 2 ^ 64) →
      (i0.eval env).toNat = (idxOf i0).2 * ((idxOf i0).1.eval env).toNat := by
  unfold idxOf
  split
  · next x k =>
    split
    · next hk =>
      intro hb
      simp only [Sym.eval, BinOp.eval] at hb ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hb]
    · intro _; simp
  · intro _; simp

theorem place_idx {a : Sym} {r off sc : Nat} {i : Sym} (h : place a = some (.idx r off i sc))
    (env : Env) (hb : (env.base r).toNat + (off + sc * (i.eval env).toNat) < 2 ^ 64) :
    (a.eval env).toNat = (env.base r).toNat + (off + sc * (i.eval env).toNat) := by
  unfold place at h
  split at h
  · simp at h
  · split at h <;> simp at h
  · next r' o i0 =>
    split at h
    · next ho =>
      simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hi := idxOf_spec env i0 (by omega)
      have hbase := (env.base r').isLt
      simp only [Sym.eval, BinOp.eval, ofInt_nonneg ho, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [hi]
      rw [Nat.mod_eq_of_lt (show o.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · simp at h
  · simp at h

/-! ## Loads and stores -/

theorem loadSym_sound {img : Image} {env : Env} {S : SState} {m : Machine} {a v : Sym} {n : Nat}
    {ob : List Oblig} (hwf : Env.WF env S) (hm : Match env S m) (hro : RoLoaded img m)
    (h : loadSym img S a n = some (v, ob)) (hob : ∀ o ∈ ob, o.holds env) :
    m.load (a.eval env) n = some (v.eval env) := by
  unfold loadSym at h
  split at h
  · next x hp =>
    rw [place_ro hp]
    split at h
    · next hc =>
      cases hv : roValue img x n with
      | none => simp [hv] at h
      | some val =>
        simp [hv] at h; obtain ⟨rfl, rfl⟩ := h
        have hin := hc
        simp [inRange] at hin
        obtain ⟨bs, hbs, hval⟩ := roValue_spec hro n x val hv hin.1 hin.2
        have hx : x < 2 ^ 64 := by unfold Layout.rodataHi at hin; omega
        unfold Machine.load
        simp only [Sym.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
        rw [if_pos (by simp [readable, inRange, hin.1, hin.2]), hbs]
        simp [hval]
    · simp at h
  · next r off hp =>
    rw [place_cst hp]
    cases hR : S.region r with
    | none => simp [hR] at h
    | some R =>
      simp only [hR] at h
      replace hR : S.regions[r]? = some R := hR
      cases hc : cstCheck R r off n with
      | none => simp [hc] at h
      | some ob' =>
        simp [hc] at h; obtain ⟨rfl, rfl⟩ := h
        exact load_cst hwf hm hR (cstCheck_spec hwf hR hc hob)
  · next r off i sc hp =>
    cases hR : S.region r with
    | none => simp [hR] at h
    | some R =>
      simp only [hR] at h
      replace hR : S.regions[r]? = some R := hR
      split at h
      · next hc =>
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hb := hob (.inBounds r off i sc n) (by simp)
        simp only [Oblig.holds] at hb
        have hfit := hwf.fits hR
        exact load_idx hwf hm hR hc hb _
          (place_idx hp env (by unfold Layout.ramHi at hfit; omega))
      · simp at h
  · simp at h

theorem storeSym_sound {env : Env} {S S' : SState} {m : Machine} {a sv : Sym} {n : Nat}
    {ob : List Oblig} (hwf : Env.WF env S) (hm : Match env S m)
    (h : storeSym S a n sv = some (S', ob)) (hob : ∀ o ∈ ob, o.holds env) :
    ∃ m', m.store (a.eval env) n (sv.eval env) = some m' ∧ Match env S' m' ∧
      S'.regs = S.regs ∧ S'.regions = S.regions ∧ S'.known = S.known ∧ S'.steps = S.steps ∧
      SameOutside (InWritable env S) m m' ∧ m'.pc = m.pc ∧ m'.regs = m.regs := by
  unfold storeSym at h
  split at h
  · next r off hp =>
    cases hR : S.region r with
    | none => simp [hR] at h
    | some R =>
      simp only [hR] at h
      replace hR : S.regions[r]? = some R := hR
      split at h
      · next hw =>
        cases hc : cstCheck R r off n with
        | none => simp [hc] at h
        | some ob' =>
          simp [hc] at h; obtain ⟨rfl, rfl⟩ := h
          have hb := cstCheck_spec hwf hR hc hob
          have hfit := hwf.fits hR
          have hrlt : r < S.regions.length := (List.getElem?_eq_some_iff.mp hR).1
          have hlt : (env.base r).toNat + off < 2 ^ 64 := by unfold Layout.ramHi at hfit; omega
          have ha : (env.base r + BitVec.ofNat 64 off).toNat = (env.base r).toNat + off :=
            toNat_add_ofNat hlt
          have hA : (env.base r).toNat + off + n ≤ 2 ^ 64 := by unfold Layout.ramHi at hfit; omega
          have hpres : (readBytes m.mem ((env.base r).toNat + off) n).isSome :=
            readBytes_isSome_of fun t ht => by
              rw [Nat.add_assoc, ofNat_toNat_add, hm.mem r (off + t) hrlt (by omega)]; rfl
          rw [place_cst hp]
          unfold Machine.store
          rw [ha, if_pos ⟨hwf.writable_of hR hw (by omega), hpres⟩]
          refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
          · refine ⟨hm.regsLen, hm.regs, ?_, hm.known⟩
            intro r' j' hr' hj'
            simp only
            rw [writeBytes_apply hA, addr_toNat hwf hj', memByte_cons]
            by_cases e : r' = r
            · subst e
              have hcov : (⟨r', off, n, sv⟩ : Write).covers r' j' =
                  decide (off ≤ j' ∧ j' < off + n) := by
                simp [Write.covers]
              rw [hcov]
              by_cases hin : off ≤ j' ∧ j' < off + n
              · rw [if_pos (by omega)]; simp [hin]; congr 1; omega
              · rw [if_neg (by omega)]; simp [hin]; exact hm.mem r' j' hr' hj'
            · have hcov : (⟨r, off, n, sv⟩ : Write).covers r' j' = false := by
                simp [Write.covers]; intro h; exact absurd h.symm e
              rw [hcov, if_neg]
              · exact hm.mem r' j' hr' hj'
              · intro hin
                have := addr_inj hwf (r := r) (j := off + ((env.base r').toNat + j' -
                  ((env.base r).toNat + off))) (by omega) hj' (by omega)
                exact e this.1.symm
          · intro x hx
            simp only
            rw [writeBytes_apply hA, if_neg]
            intro hin
            apply hx
            refine ⟨r, R, x.toNat - (env.base r).toNat, hR, hw, by omega, ?_⟩
            apply BitVec.eq_of_toNat_eq
            rw [toNat_add_ofNat (by omega)]; omega
      · simp at h
  · simp at h

/-! ## One instruction -/

theorem some_triple {α β γ : Type} {a a' : α} {b b' : β} {c c' : γ}
    (h : some (a, b, c) = some (a', b', c')) : a = a' ∧ b = b' ∧ c = c' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem beq_add_left (a b c : Word) : (a + b == a + c) = (b == c) := by
  have : a + b = a + c ↔ b = c :=
    ⟨fun e => by have := congrArg (· - a) e; simpa using this, fun e => by rw [e]⟩
  cases hb : (a + b == a + c) <;> cases hc : (b == c) <;> simp_all

/-- How the machine left one instruction, matching `StepExit`. -/
def StepExitOk (env : Env) : StepExit → Machine → Prop
  | .next pc, m => m.pc.toNat = pc
  | .branch c t f, m => m.pc.toNat = if c.eval env then t else f
  | .call t _, m => m.pc.toNat = t
  | .callInd t _, m => m.pc = t.eval env
  | .ret t, m => m.pc = t.eval env
  | .jumpInd t, m => m.pc = t.eval env

structure StepOk (env : Env) (S S' : SState) (m m' : Machine) (e : StepExit) : Prop where
  hmatch : Match env S' m'
  regions : S'.regions = S.regions
  known : S'.known = S.known
  steps : S'.steps = S.steps + 1
  frame : SameOutside (InWritable env S) m m'
  exit : StepExitOk env e m'

theorem wr_ok {env : Env} {S : SState} {m : Machine} {pc : Nat} (hm : Match env S m)
    (hpc : m.pc.toNat = pc) (rd : Fin 32) (v : Sym) (val : Word) (hv : v.eval env = val) :
    StepOk env S ({ S with steps := S.steps + 1 }.setReg rd.val v) m ((m.setReg rd val).advance)
      (.next (BitVec.ofNat 64 pc + 4).toNat) where
  hmatch := ((hm.with_steps _).setReg rd v val hv).with_pc _
  regions := by simp
  known := by simp
  steps := by simp
  frame := fun _ _ => by simp [Machine.advance]
  exit := by simp [StepExitOk, Machine.advance, pc_eq hpc]

theorem SBool.static?_sound {env : Env} {c : SBool} {b : Bool} (h : c.static? = some b) :
    c.eval env = b := by
  unfold SBool.static? at h
  split at h
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 => obtain rfl := Option.some.inj h; rfl
  case h_7 =>
    split at h
    · obtain rfl := Option.some.inj h; subst_vars; simp [SBool.eval, Sym.eval, beq_add_left]
    · simp at h
  case h_8 =>
    split at h
    · obtain rfl := Option.some.inj h; subst_vars; simp [SBool.eval, Sym.eval, bne, beq_add_left]
    · simp at h
  all_goals simp at h

theorem SBool.neg_eval (env : Env) (c : SBool) : c.neg.eval env = !c.eval env := by
  cases c <;> simp [SBool.neg, SBool.eval, bne]

theorem branch_ok {env : Env} {S S' : SState} {m : Machine} {pc : Nat} {e : StepExit}
    {ob : List Oblig} (hm : Match env S m) (hpc : m.pc.toNat = pc) (c : SBool) (cond : Bool)
    (hc : c.eval env = cond) (imm : BitVec 13)
    (h : branchSym { S with steps := S.steps + 1 } pc c imm = some (S', e, ob)) :
    ∃ m', m.branch cond imm = some m' ∧ StepOk env S S' m m' e := by
  have hpc' := pc_eq hpc
  dsimp only [branchSym] at h
  have hm1 := hm.with_steps (S.steps + 1)
  have base : ∀ p, StepOk env S { S with steps := S.steps + 1 } m { m with pc := p }
      (.next p.toNat) := fun p =>
    ⟨hm1.with_pc p, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩
  split at h
  · next hs =>
    have := SBool.static?_sound (env := env) hs
    split at h
    · next ha =>
      obtain ⟨rfl, rfl, rfl⟩ := some_triple h
      refine ⟨_, ?_, base (BitVec.ofNat 64 pc + sx imm)⟩
      simp only [Machine.branch, ← hc, this, if_true, Machine.jumpTo, hpc']
      rw [if_pos ha]
    · simp at h
  · next hs =>
    have := SBool.static?_sound (env := env) hs
    obtain ⟨rfl, rfl, rfl⟩ := some_triple h
    refine ⟨_, ?_, base (BitVec.ofNat 64 pc + 4)⟩
    simp [Machine.branch, ← hc, this, Machine.advance, hpc']
  · split at h
    · next ha =>
      obtain ⟨rfl, rfl, rfl⟩ := some_triple h
      cases hcv : cond
      · refine ⟨{ m with pc := BitVec.ofNat 64 pc + 4 },
          by simp [Machine.branch, Machine.advance, hpc'], ?_⟩
        exact ⟨hm1.with_pc _, rfl, rfl, rfl, fun _ _ => rfl, by simp [StepExitOk, hc, hcv]⟩
      · refine ⟨{ m with pc := BitVec.ofNat 64 pc + sx imm }, ?_, ?_⟩
        · simp only [Machine.branch, if_true, Machine.jumpTo, hpc']
          rw [if_pos ha]
        · exact ⟨hm1.with_pc _, rfl, rfl, rfl, fun _ _ => rfl, by simp [StepExitOk, hc, hcv]⟩
    · simp at h

theorem regEval {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (i : Fin 32) :
    (S.reg i.val).eval env = m.reg i := hm.regs i

theorem loadI_ok {img : Image} {env : Env} {S S' : SState} {m : Machine} {pc : Nat}
    {e : StepExit} {ob : List Oblig} (hwf : Env.WF env S) (hm : Match env S m)
    (hro : RoLoaded img m) (hpc : m.pc.toNat = pc) (rd rs1 : Fin 32) (imm : BitVec 12) (n : Nat)
    (f : Sym → Sym) (g : Word → Word) (hfg : ∀ s, (f s).eval env = g (s.eval env))
    (h : loadI img S { S with steps := S.steps + 1 } pc rd rs1 imm n f = some (S', e, ob))
    (hob : ∀ o ∈ ob, o.holds env) :
    ∃ m', m.loadInto rd rs1 imm n g = some m' ∧ StepOk env S S' m m' e := by
  unfold loadI at h
  cases hl : loadSym img S (mkAdd (S.reg rs1) (wlit (sx imm))) n with
  | none => simp [hl] at h
  | some p =>
    obtain ⟨v, ob'⟩ := p
    simp only [hl, Option.map_some] at h; obtain ⟨rfl, rfl, rfl⟩ := some_triple h
    have := loadSym_sound hwf hm hro hl hob
    simp only [mkAdd_eval, eval_wlit, regEval hm] at this
    refine ⟨(m.setReg rd (g (v.eval env))).advance, by simp [Machine.loadInto, this], ?_⟩
    exact wr_ok hm hpc rd (f v) (g (v.eval env)) (hfg v)

theorem storeI_ok {env : Env} {S S' : SState} {m : Machine} {pc : Nat}
    {e : StepExit} {ob : List Oblig} (hwf : Env.WF env S) (hm : Match env S m)
    (hpc : m.pc.toNat = pc) (rs1 rs2 : Fin 32) (imm : BitVec 12) (n : Nat)
    (h : storeI S { S with steps := S.steps + 1 } pc rs1 rs2 imm n = some (S', e, ob))
    (hob : ∀ o ∈ ob, o.holds env) :
    ∃ m', m.storeFrom rs1 rs2 imm n = some m' ∧ StepOk env S S' m m' e := by
  unfold storeI at h
  cases hs : storeSym { S with steps := S.steps + 1 } (mkAdd (S.reg rs1) (wlit (sx imm))) n
      (S.reg rs2) with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨S2, ob'⟩ := p
    simp only [hs, Option.map_some] at h; obtain ⟨rfl, rfl, rfl⟩ := some_triple h
    have hwf1 : Env.WF env { S with steps := S.steps + 1 } := hwf.congr rfl
    obtain ⟨m', hst, hm', hregs, hreg, hkn, hsteps, hfr, hpc', _⟩ :=
      storeSym_sound hwf1 (hm.with_steps _) hs hob
    simp only [mkAdd_eval, eval_wlit, regEval hm] at hst
    refine ⟨m'.advance, by simp [Machine.storeFrom, hst], ?_⟩
    exact ⟨hm'.with_pc _, hreg, hkn, hsteps, fun a ha => by
      simpa [Machine.advance] using hfr a ha,
      by simp [StepExitOk, Machine.advance, hpc', pc_eq hpc]⟩

theorem lit_toNat_eval (env : Env) (t : Nat) (h : t < 2 ^ 64) :
    ((Sym.lit t).eval env).toNat = t := by
  simp [Sym.eval, Nat.mod_eq_of_lt h]

set_option maxHeartbeats 400000 in
theorem stepI_sound {img : Image} {pc : Nat} {i : Instr} {S S' : SState} {e : StepExit}
    {ob : List Oblig} {env : Env} {m : Machine}
    (h : stepI img pc i S = some (S', e, ob)) (hwf : Env.WF env S) (hm : Match env S m)
    (hpc : m.pc.toNat = pc) (hro : RoLoaded img m) (hob : ∀ o ∈ ob, o.holds env) :
    ∃ m', m.exec i = some m' ∧ StepOk env S S' m m' e := by
  have hpc' := pc_eq hpc
  have r := regEval hm
  have wr : ∀ (rd : Fin 32) (v : Sym) (val : Word), v.eval env = val →
      some ({ S with steps := S.steps + 1 }.setReg rd.val v,
        StepExit.next (BitVec.ofNat 64 pc + 4).toNat, ([] : List Oblig)) = some (S', e, ob) →
      ∃ m', m.writeReg rd val = some m' ∧ StepOk env S S' m m' e := by
    intro rd v val hv hh
    obtain ⟨rfl, rfl, rfl⟩ := some_triple hh
    exact ⟨_, rfl, wr_ok hm hpc rd v val hv⟩
  cases i with
  | lui rd imm => exact wr rd _ _ (eval_wlit _ _) h
  | auipc rd imm => exact wr rd _ (m.pc + sx (imm ++ (0 : BitVec 12))) (by rw [eval_wlit, hpc']) h
  | addi rd rs1 imm => exact wr rd _ _ (by simp [r, eval_wlit]) h
  | andi rd rs1 imm => exact wr rd _ _ (by simp [r, eval_wlit, BinOp.eval]) h
  | xori rd rs1 imm => exact wr rd _ _ (by simp [r, eval_wlit, BinOp.eval]) h
  | sltiu rd rs1 imm => exact wr rd _ _ (by simp [r, eval_wlit, BinOp.eval]) h
  | slli rd rs1 sh =>
    exact wr rd _ _ (by
      have := sh.isLt
      simp [r, BinOp.eval, Sym.eval, Nat.mod_eq_of_lt (show sh.toNat < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt this]) h
  | srli rd rs1 sh =>
    exact wr rd _ _ (by
      have := sh.isLt
      simp [r, BinOp.eval, Sym.eval, Nat.mod_eq_of_lt (show sh.toNat < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt this]) h
  | add rd rs1 rs2 => exact wr rd _ _ (by simp [r]) h
  | sub rd rs1 rs2 => exact wr rd _ _ (by simp [r]) h
  | and rd rs1 rs2 => exact wr rd _ _ (by simp [r, BinOp.eval]) h
  | or rd rs1 rs2 => exact wr rd _ _ (by simp [r, BinOp.eval]) h
  | sll rd rs1 rs2 => exact wr rd _ _ (by simp [r, BinOp.eval]) h
  | sltu rd rs1 rs2 => exact wr rd _ _ (by simp [r, BinOp.eval]) h
  | mul rd rs1 rs2 => exact wr rd _ _ (by simp [r, BinOp.eval]) h
  | mulhu rd rs1 rs2 => exact wr rd _ _ (by simp [r, BinOp.eval]) h
  | beq rs1 rs2 imm => exact branch_ok hm hpc _ _ (by simp [SBool.eval, r]) imm h
  | bne rs1 rs2 imm => exact branch_ok hm hpc _ _ (by simp [SBool.eval, r]) imm h
  | blt rs1 rs2 imm => exact branch_ok hm hpc _ _ (by simp [SBool.eval, r]) imm h
  | bltu rs1 rs2 imm => exact branch_ok hm hpc _ _ (by simp [SBool.eval, r]) imm h
  | bgeu rs1 rs2 imm => exact branch_ok hm hpc _ _ (by simp [SBool.eval, r]) imm h
  | lb rd rs1 imm =>
    exact loadI_ok hwf hm hro hpc rd rs1 imm 1 _ _ (fun s => by simp) h hob
  | lbu rd rs1 imm => exact loadI_ok hwf hm hro hpc rd rs1 imm 1 _ _ (fun s => rfl) h hob
  | lhu rd rs1 imm => exact loadI_ok hwf hm hro hpc rd rs1 imm 2 _ _ (fun s => rfl) h hob
  | lw rd rs1 imm =>
    exact loadI_ok hwf hm hro hpc rd rs1 imm 4 _ _ (fun s => by simp) h hob
  | ld rd rs1 imm => exact loadI_ok hwf hm hro hpc rd rs1 imm 8 _ _ (fun s => rfl) h hob
  | sb rs1 rs2 imm => exact storeI_ok hwf hm hpc rs1 rs2 imm 1 h hob
  | sh rs1 rs2 imm => exact storeI_ok hwf hm hpc rs1 rs2 imm 2 h hob
  | sw rs1 rs2 imm => exact storeI_ok hwf hm hpc rs1 rs2 imm 4 h hob
  | sd rs1 rs2 imm => exact storeI_ok hwf hm hpc rs1 rs2 imm 8 h hob
  | jal rd imm =>
    simp only [stepI] at h
    split at h
    · next ha =>
      obtain ⟨rfl, rfl, rfl⟩ := some_triple h
      have hm2 := (hm.with_steps (S.steps + 1)).setReg rd (.lit (BitVec.ofNat 64 pc + 4).toNat)
        (m.pc + 4) (by
          show BitVec.ofNat 64 (BitVec.ofNat 64 pc + 4).toNat = m.pc + 4
          rw [ofNat_toNat64, hpc'])
      refine ⟨_, ?_, ⟨hm2.with_pc (m.pc + sx imm), by simp, by simp, by simp,
        fun _ _ => by simp, ?_⟩⟩
      · simp only [Machine.exec, Machine.jumpTo]
        rw [if_pos (by rw [hpc']; exact ha)]
      · split <;> simp [StepExitOk, hpc']
    · simp at h
  | jalr rd rs1 imm =>
    simp only [stepI] at h
    have htgt : (mkBin .and (mkAdd (S.reg rs1) (wlit (sx imm))) (wlit (~~~(1 : Word)))).eval env =
        (m.reg rs1 + sx imm) &&& ~~~(1 : Word) := by simp [r, eval_wlit, BinOp.eval]
    have hm2 := (hm.with_steps (S.steps + 1)).setReg rd (.lit (BitVec.ofNat 64 pc + 4).toNat)
      (m.pc + 4) (by
          show BitVec.ofNat 64 (BitVec.ofNat 64 pc + 4).toNat = m.pc + 4
          rw [ofNat_toNat64, hpc'])
    have hexec : ∀ t : Word, t = (m.reg rs1 + sx imm) &&& ~~~(1 : Word) → t.toNat % 4 = 0 →
        m.exec (.jalr rd rs1 imm) = some { m.setReg rd (m.pc + 4) with pc := t } := by
      intro t ht h4
      simp only [Machine.exec, Machine.jumpTo]
      rw [← ht, if_pos h4]
    split at h
    · next t heq =>
      rw [heq] at htgt
      split at h
      · next ha =>
        obtain ⟨rfl, rfl, rfl⟩ := some_triple h
        have ht : (Sym.lit t).eval env = BitVec.ofNat 64 t := rfl
        have htl := ha.2
        refine ⟨_, hexec _ (htgt.symm.trans ht |>.symm) (by
          simp [Nat.mod_eq_of_lt htl]; exact ha.1), ⟨hm2.with_pc _, by simp, by simp, by simp,
          fun _ _ => by simp, ?_⟩⟩
        split <;> simp [StepExitOk, Nat.mod_eq_of_lt htl]
      · simp at h
    · obtain ⟨rfl, rfl, rfl⟩ := some_triple h
      have ha := hob _ (List.mem_singleton_self _)
      simp only [Oblig.holds] at ha
      rw [htgt] at ha
      refine ⟨_, hexec _ rfl ha, ⟨hm2.with_pc _, by simp, by simp, by simp,
        fun _ _ => by simp, ?_⟩⟩
      split
      · exact htgt.symm
      · split
        · exact htgt.symm
        · exact htgt.symm

/-! ## Whole runs -/

theorem RoLoaded.frame {img : Image} {env : Env} {S : SState} {m m' : Machine}
    (hwf : Env.WF env S) (hro : RoLoaded img m) (hfr : SameOutside (InWritable env S) m m') :
    RoLoaded img m' := by
  intro a b hlo hhi hb
  rw [hfr]
  · exact hro a b hlo hhi hb
  · rintro ⟨r, R, j, hR, hw, hj, hx⟩
    have hram := hwf.writable_ram hR hw
    have hlt : (env.base r).toNat + j < 2 ^ 64 := by unfold Layout.ramHi at hram; omega
    have := congrArg BitVec.toNat hx
    rw [toNat_add_ofNat hlt] at this
    simp at this
    unfold Layout.rodataHi Layout.ramLo at *
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

theorem SameOutside.trans {R : Word → Prop} {m₁ m₂ m₃ : Machine}
    (h₁ : SameOutside R m₁ m₂) (h₂ : SameOutside R m₂ m₃) : SameOutside R m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem fetch_step {img : Image} {m : Machine} {pc : Nat} {i : Instr} (hpc : m.pc.toNat = pc)
    (hf : fetchI img pc = some i) : step img m = m.exec i := by
  unfold fetchI at hf
  unfold step
  rw [hpc]
  split at hf
  · next hr =>
    rw [if_pos hr]
    split at hf
    · next w hw => rw [hw]; simp only; rw [hf]
    · simp at hf
  · simp at hf

/-- What a leaf promises for a machine that matches the state the run started from. -/
def LeafRuns (img : Image) (env : Env) (S : SState) (pc : Nat) (l : Leaf) : Prop :=
  ∀ m, Env.WF env S → Match env S m → m.pc.toNat = pc → RoLoaded img m →
    S.steps ≤ l.S.steps ∧ ∃ m', RunsIn img (l.S.steps - S.steps) m m' ∧ Match env l.S m' ∧
      ExitOk env l.exit m' ∧ SameOutside (InWritable env S) m m'

/-- One machine step under `stepI`, then the rest of the run. -/
theorem stepThen {img : Image} {env : Env} {pc : Nat} {i : Instr} {S S' : SState} {e : StepExit}
    {ob : List Oblig} {l : Leaf} (hf : fetchI img pc = some i)
    (hs : stepI img pc i S = some (S', e, ob)) (hmc : pc ≠ Layout.memcpyEntry)
    (hob : ∀ o ∈ ob, o.holds env)
    (rest : ∀ m₁, Env.WF env S' → Match env S' m₁ → StepExitOk env e m₁ → RoLoaded img m₁ →
      S'.steps ≤ l.S.steps ∧ ∃ m', RunsIn img (l.S.steps - S'.steps) m₁ m' ∧ Match env l.S m' ∧
        ExitOk env l.exit m' ∧ SameOutside (InWritable env S') m₁ m') :
    LeafRuns img env S pc l := by
  intro m hwf hm hpc hro
  obtain ⟨m₁, hx, hok⟩ := stepI_sound hs hwf hm hpc hro hob
  have hn : next img m = some (m₁, 1) := by
    simp [next, hpc, hmc, fetch_step hpc hf, hx]
  have hwf' := hwf.congr hok.regions
  obtain ⟨hle, m', hr, hm', hex, hfr⟩ := rest m₁ hwf' hok.hmatch hok.exit (hro.frame hwf hok.frame)
  rw [InWritable.congr hok.regions] at hfr
  have hst := hok.steps
  refine ⟨by omega, m', ?_, hm', hex, SameOutside.trans hok.frame hfr⟩
  have := RunsIn.step hn hr
  rwa [show 1 + (l.S.steps - S'.steps) = l.S.steps - S.steps by rw [hok.steps] at hle ⊢; omega]
    at this

theorem go_sound {img : Image} {cuts : List Nat} {env : Env} :
    ∀ fuel started pc S cs os ls, go img cuts fuel started pc S cs os = some ls →
      (∀ c ∈ cs, c.eval env = true) →
      ∃ l ∈ ls, (∀ c ∈ l.conds, c.eval env = true) ∧ (∀ o ∈ os, o ∈ l.obligs) ∧
        ((∀ o ∈ l.obligs, o.holds env) → LeafRuns img env S pc l)
  | 0, _, _, _, _, _, _, h, _ => by simp [go] at h
  | fuel + 1, started, pc, S, cs, os, ls, h, hcs => by
    unfold go at h
    split at h
    · simp at h; subst h
      refine ⟨_, List.mem_singleton_self _, hcs, fun o ho => ho, fun _ m _ hm hpc _ =>
        ⟨Nat.le_refl _, m, ?_, hm, hpc, fun _ _ => rfl⟩⟩
      simpa using (RunsIn.refl : RunsIn img 0 m m)
    · next hcut =>
      have hmc : pc ≠ Layout.memcpyEntry := by intro e; apply hcut; simp [e]
      cases hf : fetchI img pc with
      | none => simp [hf] at h
      | some i =>
        simp only [hf] at h
        cases hs : stepI img pc i S with
        | none => simp [hs] at h
        | some res =>
          obtain ⟨S', e, ob⟩ := res
          simp only [hs] at h
          have sub : ∀ (l : Leaf), (∀ o ∈ os ++ ob, o ∈ l.obligs) → (∀ o ∈ l.obligs, o.holds env) →
              ∀ o ∈ ob, o.holds env := fun l hsub hl o ho => hl o (hsub o (by simp [ho]))
          have osub : ∀ (l : Leaf), (∀ o ∈ os ++ ob, o ∈ l.obligs) → ∀ o ∈ os, o ∈ l.obligs :=
            fun l hsub o ho => hsub o (by simp [ho])
          -- a leaf right after this instruction
          have leafHere : ∀ x, StepExitOk env e = ExitOk env x →
              some [⟨S', x, cs, os ++ ob⟩] = some ls →
              ∃ l ∈ ls, (∀ c ∈ l.conds, c.eval env = true) ∧ (∀ o ∈ os, o ∈ l.obligs) ∧
                ((∀ o ∈ l.obligs, o.holds env) → LeafRuns img env S pc l) := by
            intro x hx hh
            simp at hh; subst hh
            refine ⟨_, List.mem_singleton_self _, hcs, fun o ho => by simp [ho], fun hl => ?_⟩
            refine stepThen hf hs hmc (sub _ (fun o ho => ho) hl) fun m₁ _ hm₁ he _ =>
              ⟨Nat.le_refl _, m₁, ?_, hm₁, hx ▸ he, fun _ _ => rfl⟩
            simpa using (RunsIn.refl : RunsIn img 0 m₁ m₁)
          cases e with
          | next pc' =>
            obtain ⟨l, hl, hc, ho, hr⟩ := go_sound fuel true pc' S' cs (os ++ ob) ls h hcs
            refine ⟨l, hl, hc, osub l ho, fun hlo => stepThen hf hs hmc (sub l ho hlo)
              fun m₁ hwf₁ hm₁ he hro₁ => hr hlo m₁ hwf₁ hm₁ he hro₁⟩
          | branch c t f =>
            cases h₁ : go img cuts fuel true t S' (cs ++ [c]) (os ++ ob) with
            | none => simp [h₁] at h
            | some l₁ =>
              cases h₂ : go img cuts fuel true f S' (cs ++ [c.neg]) (os ++ ob) with
              | none => simp [h₁, h₂] at h
              | some l₂ =>
                simp [h₁, h₂] at h; subst h
                cases hce : c.eval env
                · obtain ⟨l, hl, hc, ho, hr⟩ := go_sound fuel true f S' (cs ++ [c.neg]) (os ++ ob)
                    l₂ h₂ (by intro c' hc'; simp at hc'; rcases hc' with hc' | rfl
                              · exact hcs c' hc'
                              · simp [SBool.neg_eval, hce])
                  refine ⟨l, by simp [hl], hc, osub l ho, fun hlo => stepThen hf hs hmc (sub l ho hlo)
                    fun m₁ hwf₁ hm₁ he hro₁ => hr hlo m₁ hwf₁ hm₁ (by simpa [StepExitOk, hce] using he)
                      hro₁⟩
                · obtain ⟨l, hl, hc, ho, hr⟩ := go_sound fuel true t S' (cs ++ [c]) (os ++ ob)
                    l₁ h₁ (by intro c' hc'; simp at hc'; rcases hc' with hc' | rfl
                              · exact hcs c' hc'
                              · exact hce)
                  refine ⟨l, by simp [hl], hc, osub l ho, fun hlo => stepThen hf hs hmc (sub l ho hlo)
                    fun m₁ hwf₁ hm₁ he hro₁ => hr hlo m₁ hwf₁ hm₁ (by simpa [StepExitOk, hce] using he)
                      hro₁⟩
          | call t r => exact leafHere (.call t r) rfl h
          | callInd t r => exact leafHere (.callInd t r) rfl h
          | ret t => exact leafHere (.ret t) rfl h
          | jumpInd t => exact leafHere (.jumpInd t) rfl h

/-- Soundness of `run`: some leaf's conditions hold, and if its obligations hold, the machine
runs to a state that matches the leaf in exactly the leaf's number of steps. -/
theorem run_sound {img : Image} {cuts : List Nat} {fuel pc : Nat} {S : SState} {ls : List Leaf}
    {env : Env} {m : Machine}
    (h : run img cuts fuel pc S = some ls) (hwf : Env.WF env S) (hm : Match env S m)
    (hpc : m.pc.toNat = pc) (hro : RodataLoaded img m) :
    ∃ l ∈ ls, (∀ c ∈ l.conds, c.eval env = true) ∧
      ((∀ o ∈ l.obligs, o.holds env) →
        ∃ m', RunsIn img (l.S.steps - S.steps) m m' ∧ Match env l.S m' ∧ ExitOk env l.exit m' ∧
          SameOutside (InWritable env S) m m') := by
  obtain ⟨l, hl, hc, -, hr⟩ := go_sound fuel false pc S [] [] ls h (by simp)
  exact ⟨l, hl, hc, fun ho => (hr ho m hwf hm hpc fun a b _ _ hb => hro a b hb).2⟩

end ZesuExec.Sym
