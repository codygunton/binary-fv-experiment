import GeneratedBindings
import BinaryFv.RiscV.Elfling.Contract

/-!
# Complete generated occurrence bindings

`GeneratedBindings.lean` is *untrusted* generated data: the entry-time location of every occurrence's
formal parameters, resolved from DWARF `.debug_loc` at each occurrence's entry PC (see
`tools/generate_elfling_program.py --out-bindings`). Each parameter's DWARF kind is one of:

- `reg` / `fbreg` / `breg` / `addr` — a concrete register, frame slot, base+offset location, or
  memory address; `bregValue` / `addrValue` preserve DWARF's `DW_OP_stack_value` distinction
  (emitted occurrences carry their real optimized ABI this way, and many inlined occurrences too);
- `const` — the concrete constant value (from DWARF or deterministic source recovery);
- `derived` — a loop-carried value: the source argument is `index * stride + constant`, and the
  compiled loop keeps `index * stride` in a register (see below);
- `callerProvided` — the optimizer emitted **no** location at the occurrence's entry PC. This kind
  appears only in the RAW table; generation fails if one survives recovery.

## Raw DWARF versus effective bindings

`rawBindings` preserves exactly what DWARF said, including 61 `callerProvided` gaps. `bindings` is the
effective table: the generator resolves those gaps from pinned Zig call-site literals, forwarding
through the reader chain, `readArray` specialization widths, the RISC-V C ABI for `memmove`, or the
loop-induction register for a loop-carried reader offset. **Generation fails if any gap remains** —
there is no bucket for a parameter with no machine meaning, because a row like that would make the
occurrence's entry predicate unsatisfiable and every implication out of it vacuous.
`recoveredBindings` records every change beside the raw table, so recovery is inspectable rather than
silently replacing the compiler evidence.

## The binding-classification spike

A classification spike over all 148 parameter rows — one row per *signature* parameter, taken from each
occurrence's DWARF abstract-origin DIE, so a parameter the optimizer dropped from the concrete instance
is a visible row rather than an absence — separates every parameter into:

1. **concrete DWARF location** (`reg`/`fbreg`/`breg`/`addr`/`bregValue`/`addrValue`) or
   **constant-folded** (`const`) — 140 rows, `resolvedBindingCount`;
2. **loop-derived** (`derived`) — 8 rows: the `offset` of the `decodeWithdrawals` reader chain, whose
   source argument is `index * WITHDRAWAL_SIZE + k`;
3. **genuinely unresolved semantic input** — zero, and the generator refuses to emit the artifact if
   one appears (`no_genuinely_unresolved`, plus the generator's own hard failure).

`no_binding_kind_is_impossible` is the machine-checked statement that (3) is not hiding inside (1) or
(2): every effective row's kind has a real case in `bindingRowHolds`, so no occurrence's entry
predicate is unsatisfiable merely because of a kind. Row C separately checks that each occurrence's
predicate is satisfied by the register/memory state captured at its entry PC in the unchanged
production ELF.

## Recovery rules (the 61 raw `callerProvided` rows)

Rather than 61 handwritten Lean entries, five generator rules cover every missing location:

- `readArrayWidth`: the `len` of a `ssz_raw.bytesAt` occurrence. `bytesAt(data, offset,
  len)` is always called with a *compile-time* length by its enclosing reader — `readArray(N,…)` →
  `N`, `readU32` → 4, `readU64` → 8, `readU256` → 32 — so `len` is the constant recovered from the
  parent occurrence's routine/specialization (recorded as the fourth field).
- `riscvCAbiArg2`: occ140 = `memmove`, an emitted body whose `n` DWARF location is absent.
  By the RISC-V C ABI the third integer argument is in `x12`; the adjacent emitted `memcpy` (occ139)
  carries `n = reg x12`, and the shared `preCopy` contract binds `x12 = length`. Recovered to `x12`.
- `sourceLiteral`: a literal argument at the pinned Zig call site;
- `forwardedParentParam`: a reader forwards its parent's already-resolved parameter, such as
  `readOffset` forwarding `offset` into `readU32`, then into `bytesAt`.
- `loopInductionOffset`: the reader chain inside `decodeWithdrawals`' element loop takes
  `offset`/`offset + 8`/`offset + 16`/`offset + 36` where `const offset = index * WITHDRAWAL_SIZE`.
  The generator recovers, from the loaded image, the unique register that is (a) written exactly once
  in the natural loop containing the occurrence's entry PC, by `addi r, r, WITHDRAWAL_SIZE`, and
  (b) zero on every edge entering that loop. The row becomes `derived`, and `derivedBindings` records
  the register, stride, constant, pinned source expression and loop so the derivation is auditable.

The effective rows feed `generatedEntryBinding`, and `withGeneratedEntry` attaches that predicate to
a typed `OccurrenceBinding`. Rows E-I only supply the small typed-argument-to-name projection; they
do not rediscover locations or constants.
-/

namespace BinaryFv.SSZ.Zesu.Elfling

open BinaryFv.SSZ.Zesu.Elfling.GeneratedBindings

/-- The effective `(name, kind, register-or-address, offset-or-value)` parameters of occurrence `i`.
Unlike the raw DWARF rows, this table includes deterministic pinned-source/ABI recovery. -/
def occurrenceParams (i : Nat) : List (String × String × Int × Int) :=
  bindings.filterMap fun r => if r.1 == i then some (r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2) else none

/-- The raw DWARF parameters before source/ABI recovery. Kept visible so recovery is auditable. -/
def rawOccurrenceParams (i : Nat) : List (String × String × Int × Int) :=
  rawBindings.filterMap fun r =>
    if r.1 == i then some (r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2) else none

/-! ## Raw gaps and complete effective resolution -/

/-- The DWARF kinds that resolve a parameter to a concrete *location or value*. `callerProvided` is
deliberately **absent** (a missing location is a defect, not a resolution), and so is `unresolved`
(an undecodable expression). `derived` is also absent: it resolves the parameter to a machine
*relation*, not to a fixed location, and is counted separately. -/
def resolvedBindingKinds : List String :=
  ["reg", "fbreg", "breg", "addr", "bregValue", "addrValue", "const"]

/-- `callerProvided` is not a resolved kind — the fix for the prior inventory, which listed it. -/
theorem callerProvided_not_resolved : resolvedBindingKinds.contains "callerProvided" = false := by
  native_decide

/-- The raw artifact has exactly the 61 DWARF-absent rows that recovery must explain. -/
theorem raw_callerProvided_count :
    (rawBindings.filter fun r => r.2.2.1 == "callerProvided").length = 61 := by native_decide

/-- **Every effective parameter is resolved to a location/value or derived from a loop relation.**

There is no third bucket. A `derived` row is not a gap: it names the loop register carrying
`index * stride`, so the entry predicate still constrains both the machine and the argument (see
`bindingRowHolds` and `derived_row_constrains_machine`). -/
theorem all_bindings_resolved_or_derived :
    bindings.all (fun r => resolvedBindingKinds.contains r.2.2.1 || r.2.2.1 == "derived")
      = true := by native_decide

/-- The number of genuinely resolved (concrete-location or constant-folded) parameter bindings. -/
def resolvedBindingCount : Nat := (bindings.filter fun r => resolvedBindingKinds.contains r.2.2.1).length

/-- Rows whose value is a loop relation rather than a fixed location. -/
def derivedBindingCount : Nat := (bindings.filter fun r => r.2.2.1 == "derived").length

theorem resolved_count : resolvedBindingCount = 140 := by native_decide

/-- **The 8 derived rows are exactly the `derivedBindings` audit table**, and each effective row's
register and constant agree with the audited derivation. -/
theorem derived_count : derivedBindingCount = 8 ∧ derivedBindings.length = 8 := by native_decide

theorem derived_rows_are_audited :
    derivedBindings.all (fun d =>
      bindings.contains (d.1, d.2.1, "derived", (d.2.2.1 : Int), (d.2.2.2.2.1 : Int)))
      = true := by native_decide

/-- **Every derived row is pinned to one loop, one register and one source constant.** All eight are
the `decodeWithdrawals` element loop `[72120, 72488]`, keeping `index * WITHDRAWAL_SIZE` in `x23`. A
different register, stride, or loop fails this. -/
theorem derived_derivations_pinned :
    derivedBindings.all (fun d =>
      d.2.2.1 == 23 && d.2.2.2.1 == 44 && d.2.2.2.2.2.2.1 == "WITHDRAWAL_SIZE" &&
      d.2.2.2.2.2.2.2.1 == 72120 && d.2.2.2.2.2.2.2.2 == 72488) = true := by native_decide

/-- The derived constants are the four `RawWithdrawal` field offsets, each shared by the
`readU64`/`readArray` occurrence and the `bytesAt` occurrence it forwards to. -/
theorem derived_constants_are_the_withdrawal_field_offsets :
    (derivedBindings.map fun d => (d.1, d.2.2.2.2.1)) =
      [(46, 0), (47, 0), (48, 8), (49, 8), (50, 16), (51, 16), (52, 36), (53, 36)] := by
  native_decide

/-- Every derived row records a non-empty pinned source expression, so the relation is described in the
source's own terms, not merely asserted in machine terms. -/
theorem derived_rows_have_source_expressions :
    derivedBindings.all (fun d => d.2.2.2.2.2.1 != "") = true := by native_decide

/-! ## Recovery coverage -/

/-- The `(occurrence, parameter)` keys missing from raw DWARF. -/
def callerProvidedKeys : List (Nat × String) :=
  rawBindings.filterMap fun r => if r.2.2.1 == "callerProvided" then some (r.1, r.2.1) else none

/-- The keys for which the generator emitted a concrete recovery. -/
def recoveredKeys : List (Nat × String) := recoveredBindings.map fun r => (r.1, r.2.1)

/-- The keys whose recovery is the loop-derived relation. -/
def derivedKeys : List (Nat × String) := derivedBindings.map fun d => (d.1, d.2.1)

/-- Every raw gap is mechanically recovered — none is dropped and none is left without a meaning. -/
theorem recovery_covers_all_callerProvided :
    callerProvidedKeys.all (fun k => recoveredKeys.contains k) = true := by native_decide

theorem recovery_only_callerProvided :
    recoveredKeys.all (fun k => callerProvidedKeys.contains k) = true := by native_decide

/-- Recovery explains every raw gap: 61 recovered = the 61 rows DWARF left without a location, of which
8 are the loop-derived offsets. Nothing falls between the two. -/
theorem recovery_count :
    recoveredBindings.length = 61 ∧ callerProvidedKeys.length = 61 ∧ derivedKeys.length = 8 := by
  native_decide

/-- Counts plus membership are a genuine one-to-one recovery, not duplicate rows hiding an omission. -/
theorem recovery_keys_unique : callerProvidedKeys.Nodup ∧ recoveredKeys.Nodup := by native_decide

/-- The only accepted mechanical recovery rules. -/
def recoveryForms : List String :=
  ["sourceLiteral", "forwardedParentParam", "readArrayWidth", "riscvCAbiArg2", "loopInductionOffset"]

/-- Every recovery was produced by one of the narrow generator rules. -/
theorem recovery_forms_valid :
    recoveredBindings.all (fun r => recoveryForms.contains r.2.2.1) = true := by native_decide

/-- Every recovered row appears in the effective binding table with its exact kind/location/value. -/
theorem recoveries_are_effective :
    recoveredBindings.all (fun r =>
      bindings.contains (r.1, r.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2)) = true := by
  native_decide

/-- Every effective register number is a real stored integer register, every address is nonnegative,
and every constant has a concrete nonnegative value. -/
theorem effective_locations_well_formed :
    bindings.all (fun r =>
      if r.2.2.1 = "const" then decide (0 ≤ r.2.2.2.2)
      else if r.2.2.1 = "reg" ∨ r.2.2.1 = "breg" ∨ r.2.2.1 = "bregValue" ∨
          r.2.2.1 = "fbreg" then
        decide (1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ 31)
      else if r.2.2.1 = "addr" ∨ r.2.2.1 = "addrValue" then decide (0 ≤ r.2.2.2.1)
      else if r.2.2.1 = "derived" then
        decide (1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ 31 ∧ 0 ≤ r.2.2.2.2)
      else false) = true := by
  native_decide

/-- No effective row retains a missing/undecodable marker. -/
theorem no_genuinely_unresolved :
    bindings.all (fun r => r.2.2.1 != "callerProvided" && r.2.2.1 != "unresolved") = true := by
  native_decide

/-! ## Executable entry predicates for occurrence contracts -/

open BinaryFv.RiscV
open LeanRV64DExecutable.Functions
open Register

/-- A value in the numbered RISC-V integer register used by DWARF. `x0` is not stored in Sail state
and no generated parameter binding uses it. The explicit match keeps Lean's dependent register-file
value type fixed at `BitVec 64`. -/
def RegisterValueRep (state : State) (number value : Nat) : Prop :=
  let bits := some (BitVec.ofNat 64 value)
  match number with
  | 1 => state.regs.get? x1 = bits | 2 => state.regs.get? x2 = bits
  | 3 => state.regs.get? x3 = bits | 4 => state.regs.get? x4 = bits
  | 5 => state.regs.get? x5 = bits | 6 => state.regs.get? x6 = bits
  | 7 => state.regs.get? x7 = bits | 8 => state.regs.get? x8 = bits
  | 9 => state.regs.get? x9 = bits | 10 => state.regs.get? x10 = bits
  | 11 => state.regs.get? x11 = bits | 12 => state.regs.get? x12 = bits
  | 13 => state.regs.get? x13 = bits | 14 => state.regs.get? x14 = bits
  | 15 => state.regs.get? x15 = bits | 16 => state.regs.get? x16 = bits
  | 17 => state.regs.get? x17 = bits | 18 => state.regs.get? x18 = bits
  | 19 => state.regs.get? x19 = bits | 20 => state.regs.get? x20 = bits
  | 21 => state.regs.get? x21 = bits | 22 => state.regs.get? x22 = bits
  | 23 => state.regs.get? x23 = bits | 24 => state.regs.get? x24 = bits
  | 25 => state.regs.get? x25 = bits | 26 => state.regs.get? x26 = bits
  | 27 => state.regs.get? x27 = bits | 28 => state.regs.get? x28 = bits
  | 29 => state.regs.get? x29 = bits | 30 => state.regs.get? x30 = bits
  | 31 => state.regs.get? x31 = bits
  | _ => False

/-- The address denoted by a signed DWARF base-register offset. -/
def addSignedOffset (base : Nat) (offset : Int) : Nat :=
  if offset < 0 then base - offset.natAbs else base + offset.toNat

/-- A little-endian machine word used by generated stack/global parameter locations. -/
def ParameterWordRep (state : State) (base value : Nat) : Prop :=
  ∀ index, index < 8 →
    state.mem.get? (base + index) =
      some (BitVec.ofNat 8 ((value / 256 ^ index) % 256))

/-- Values supplied by the typed routine-specific argument adapter, keyed by Zig parameter name. -/
abbrev ParameterValues := String → Option Nat

/-- The pinned loop stride of a `derived` row, from the generated audit table. -/
def derivedStride (occurrence : Nat) (name : String) : Option Nat :=
  (derivedBindings.find? fun d => d.1 == occurrence && d.2.1 == name).map fun d => d.2.2.2.1

/-- **A loop-derived parameter.** The source argument is `index * stride + constant` for the loop's
current index, and the compiled loop keeps the scaled index `index * stride` in `register`. This is
the machine content of `const offset = index * WITHDRAWAL_SIZE; … readU64(data, offset + 8)`.

It is a genuine constraint in both directions: it forces `register` to hold a multiple of `stride`,
and, given that register, it pins the argument to exactly `register + constant`. -/
def DerivedIndexRep (state : State) (register stride constant value : Nat) : Prop :=
  ∃ index, RegisterValueRep state register (index * stride) ∧ value = index * stride + constant

/-- Interpret one effective generated row as a state/value condition. Constants are checked directly;
register, memory and loop-derived locations are checked against the Sail state.

Every kind the generated table can carry has a real case here. A kind falling through to `False` would
make `generatedEntryBinding` unsatisfiable for every occurrence carrying such a row, and any
implication out of that entry binding provable vacuously — see `no_binding_kind_is_impossible`, which
pins that the fallthrough is unreachable for the artifact actually emitted. -/
def bindingRowHolds (row : Nat × String × String × Int × Int)
    (values : ParameterValues) (state : State) : Prop :=
  let (occurrence, name, kind, registerOrAddress, offsetOrValue) := row
  ∃ value, values name = some value ∧
    if kind = "const" then
      value = offsetOrValue.toNat
    else if kind = "reg" then
      RegisterValueRep state registerOrAddress.toNat value
    else if kind = "breg" ∨ kind = "fbreg" then
      ∃ base,
        RegisterValueRep state registerOrAddress.toNat base ∧
        ParameterWordRep state (addSignedOffset base offsetOrValue) value
    else if kind = "bregValue" then
      ∃ base,
        RegisterValueRep state registerOrAddress.toNat base ∧
        value = addSignedOffset base offsetOrValue
    else if kind = "addr" then
      ParameterWordRep state registerOrAddress.toNat value
    else if kind = "addrValue" then
      value = registerOrAddress.toNat
    else if kind = "derived" then
      ∃ stride, derivedStride occurrence name = some stride ∧
        DerivedIndexRep state registerOrAddress.toNat stride offsetOrValue.toNat value
    else False

/-- The kinds `bindingRowHolds` gives a real case. Any other kind reaches the `False` fallthrough. -/
def bindingKindsWithACase : List String :=
  ["const", "reg", "breg", "fbreg", "bregValue", "addrValue", "addr", "derived"]

/-- **No occurrence's entry predicate is impossible merely because of a binding kind.** Every effective
row's kind is one `bindingRowHolds` can satisfy; none reaches the `False` fallthrough. This is the
property the previous `unlocated` kind broke: `generatedEntryBinding` quantifies over an occurrence's
rows, so one unsatisfiable row made the whole predicate `False` and every consequence of it vacuous. -/
theorem no_binding_kind_is_impossible :
    bindings.all (fun r => bindingKindsWithACase.contains r.2.2.1) = true := by native_decide

/-- Every `derived` row has an audited stride, so its case is never satisfied only by the absence of
one. -/
theorem derived_rows_have_strides :
    bindings.all (fun r => r.2.2.1 != "derived" ||
      (derivedBindings.any fun d => d.1 == r.1 && d.2.1 == r.2.1)) = true := by native_decide

/-! ### Every kind's case is satisfiable

One lemma per kind, each of the same shape: the row HOLDS of any machine state that places the
parameter where the row says. Together with `no_binding_kind_is_impossible` (no row reaches the `False`
fallthrough) this is the statement that no occurrence's entry predicate is unsatisfiable because of a
kind. Row C supplies the other half — that the production machine really does place them there. -/

theorem bindingRowHolds_const {occurrence : Nat} {name : String} {reg val : Int}
    {values : ParameterValues} {state : State} (h : values name = some val.toNat) :
    bindingRowHolds (occurrence, name, "const", reg, val) values state :=
  ⟨val.toNat, h, by simp⟩

theorem bindingRowHolds_reg {occurrence : Nat} {name : String} {reg val : Int} {v : Nat}
    {values : ParameterValues} {state : State} (h : values name = some v)
    (hr : RegisterValueRep state reg.toNat v) :
    bindingRowHolds (occurrence, name, "reg", reg, val) values state :=
  ⟨v, h, by simpa using hr⟩

theorem bindingRowHolds_breg {occurrence : Nat} {name : String} {reg val : Int} {v base : Nat}
    {values : ParameterValues} {state : State} (h : values name = some v)
    (hr : RegisterValueRep state reg.toNat base)
    (hm : ParameterWordRep state (addSignedOffset base val) v) :
    bindingRowHolds (occurrence, name, "breg", reg, val) values state :=
  ⟨v, h, by simpa using ⟨base, hr, hm⟩⟩

theorem bindingRowHolds_fbreg {occurrence : Nat} {name : String} {reg val : Int} {v base : Nat}
    {values : ParameterValues} {state : State} (h : values name = some v)
    (hr : RegisterValueRep state reg.toNat base)
    (hm : ParameterWordRep state (addSignedOffset base val) v) :
    bindingRowHolds (occurrence, name, "fbreg", reg, val) values state :=
  ⟨v, h, by simpa using ⟨base, hr, hm⟩⟩

theorem bindingRowHolds_bregValue {occurrence : Nat} {name : String} {reg val : Int} {base : Nat}
    {values : ParameterValues} {state : State}
    (h : values name = some (addSignedOffset base val))
    (hr : RegisterValueRep state reg.toNat base) :
    bindingRowHolds (occurrence, name, "bregValue", reg, val) values state :=
  ⟨addSignedOffset base val, h, by simpa using ⟨base, hr, rfl⟩⟩

theorem bindingRowHolds_addr {occurrence : Nat} {name : String} {reg val : Int} {v : Nat}
    {values : ParameterValues} {state : State} (h : values name = some v)
    (hm : ParameterWordRep state reg.toNat v) :
    bindingRowHolds (occurrence, name, "addr", reg, val) values state :=
  ⟨v, h, by simpa using hm⟩

theorem bindingRowHolds_addrValue {occurrence : Nat} {name : String} {reg val : Int}
    {values : ParameterValues} {state : State} (h : values name = some reg.toNat) :
    bindingRowHolds (occurrence, name, "addrValue", reg, val) values state :=
  ⟨reg.toNat, h, by simp⟩

/-! ### The `derived` case constrains the machine and the argument

`derived_row_constrains_machine` and `derived_row_holds_of_machine` are the two halves of
non-vacuity: the row is satisfied by exactly those states whose loop register carries a multiple of
the stride, with the argument pinned to that register value plus the row's constant. -/

theorem derived_row_constrains_machine {occurrence : Nat} {name : String} {reg val : Int}
    {values : ParameterValues} {state : State}
    (h : bindingRowHolds (occurrence, name, "derived", reg, val) values state) :
    ∃ stride index value,
      derivedStride occurrence name = some stride ∧
      values name = some value ∧
      RegisterValueRep state reg.toNat (index * stride) ∧
      value = index * stride + val.toNat := by
  obtain ⟨value, hv, h⟩ := h
  simp only [reduceIte] at h
  obtain ⟨stride, hs, index, hr, he⟩ := h
  exact ⟨stride, index, value, hs, hv, hr, he⟩

theorem derived_row_holds_of_machine {occurrence : Nat} {name : String} {reg val : Int}
    {values : ParameterValues} {state : State} {stride index : Nat}
    (hs : derivedStride occurrence name = some stride)
    (hr : RegisterValueRep state reg.toNat (index * stride))
    (hv : values name = some (index * stride + val.toNat)) :
    bindingRowHolds (occurrence, name, "derived", reg, val) values state :=
  ⟨index * stride + val.toNat, hv, by
    simp only [reduceIte]
    exact ⟨stride, hs, index, hr, rfl⟩⟩

/-- The complete generated entry placement for one occurrence. This is the machine-placement conjunct
that typed local contracts use; `values` is the small handwritten projection from that routine's
argument structure to its Zig parameter names. -/
def generatedEntryBinding (occurrence : Nat) (values : ParameterValues) (state : State) : Prop :=
  ∀ row ∈ bindings, row.1 = occurrence → bindingRowHolds row values state

/-- Add the generated parameter placement to a typed occurrence binding without changing its exit or
step bound. This is the explicit connection between the generated inventory and local contracts. -/
def withGeneratedEntry {Args Outcome : Type}
    (binding : BinaryFv.RiscV.Elfling.OccurrenceBinding Args Outcome) (occurrence : Nat)
    (values : Args → ParameterValues) :
    BinaryFv.RiscV.Elfling.OccurrenceBinding Args Outcome where
  entry := fun args state => binding.entry args state ∧ generatedEntryBinding occurrence (values args) state
  exit := binding.exit
  stepBound := binding.stepBound

/-! ## Emitted-occurrence ABIs — all 14 pinned exactly

The review noted only two emitted ABIs were pinned. All 14 emitted occurrences are pinned here: the
eight with parameters exactly (mutation- and omission-sensitive), and the six paramless ones as
empty. -/

/-- The 14 emitted occurrences and their exact effective entry parameters. -/
def emittedAbis : List (Nat × List (String × String × Int × Int)) :=
  [(0, [("bytes", "reg", 10, 0), ("alignment", "reg", 11, 0)]),
   (1, [("input", "reg", 10, 0), ("input_len", "reg", 11, 0)]),
   (5, []),
   (6, [("alloc", "breg", 11, 0)]),
   (123, []),
   (124, []),
   (126, [("alloc", "breg", 11, 0), ("max_items", "reg", 14, 0), ("max_item_bytes", "reg", 15, 0)]),
   (134, [("fixed_size", "reg", 11, 0)]),
   (135, []),
   (136, [("len", "reg", 11, 0), ("alignment", "reg", 12, 0)]),
   (137, []),
   (138, []),
   (139, [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "reg", 12, 0)]),
   (140, [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "reg", 12, 0)])]

theorem emitted_occurrence_count : emittedAbis.length = 14 := by native_decide

/-- **Every emitted occurrence's ABI is pinned exactly.** Mutating a register, dropping a parameter,
or adding one to any of the 14 fails `native_decide`. -/
theorem emitted_abis_pinned :
    emittedAbis.all (fun p => occurrenceParams p.1 == p.2) = true := by native_decide

/-- **occ140's absent `n` recovers to the C ABI register.** The raw row stays visible while the
effective binding is `x12`, matching emitted `memcpy`. -/
theorem memmove_n_recovers_to_memcpy_abi :
    (rawOccurrenceParams 140).contains ("n", "callerProvided", -1, 0) = true ∧
      (occurrenceParams 139).contains ("n", "reg", 12, 0) = true ∧
        (occurrenceParams 140).contains ("n", "reg", 12, 0) = true := by native_decide

/-! ## Coverage — all 141 occurrences accounted -/

/-- The number of the 141 occurrences carrying at least one parameter binding. -/
def boundOccurrenceCount : Nat :=
  (List.range 141).countP fun i => !(occurrenceParams i).isEmpty

theorem bound_occurrence_count : boundOccurrenceCount = 117 := by native_decide

/-- The 31 occurrences with no parameters (allocator/accessor bodies, memory-slice-input decoders,
etc.). Listed explicitly so a silently-dropped binding cannot masquerade as a paramless occurrence. -/
def paramlessOccurrences : List Nat :=
  [2, 4, 5, 7, 16, 23, 45, 58, 63, 70, 81, 88, 95, 102, 105, 111, 116, 120, 123, 124, 127, 135, 137,
   138]

/-- **All 141 occurrences are accounted for.** An occurrence is paramless iff it is in the list, so
the 117 bound and 24 paramless occurrences exhaust the program — the "only some occurrences have rows"
gap is closed by naming the rest, not by hiding them. -/
theorem all_occurrences_accounted :
    (List.range 141).all (fun i => (occurrenceParams i).isEmpty == paramlessOccurrences.contains i)
      = true := by native_decide

theorem coverage_partitions_141 :
    boundOccurrenceCount + paramlessOccurrences.length = 141 ∧ paramlessOccurrences.length = 24 := by
  native_decide

/-- The total number of parameter bindings across all occurrences. -/
def totalParamCount : Nat := bindings.length

theorem total_param_count : totalParamCount = 148 := by native_decide

/-- Every recorded parameter carries an explicit kind (the `filterMap` never drops a row). -/
theorem every_binding_has_kind : bindings.all (fun r => r.2.2.1 != "") = true := by native_decide

/-! ## Representative resolved bindings

One register-bound, one stack/base-relative with a recovered constant, and one ABI recovery. -/

/-- **Register-bound.** occ139 (`memcpy`) binds all three parameters in argument registers `x10/x11/x12`
— the real optimized ABI, resolved by DWARF. -/
theorem validate_register_bound :
    occurrenceParams 139 == [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "reg", 12, 0)] := by
  native_decide

/-- **Register-plus-offset value plus constant.** occ73 binds `offset` to `x27 + 48` (DWARF
`stack_value`, so there is no memory load) and resolves `len` from `readArray[32]`. -/
theorem validate_stack_relative :
    rawOccurrenceParams 73 == [("offset", "bregValue", 27, 48), ("len", "callerProvided", -1, 0)] ∧
      occurrenceParams 73 == [("offset", "bregValue", 27, 48), ("len", "const", -1, 32)] := by
  native_decide

/-- **ABI recovery.** occ140 (`memmove`) has no raw DWARF location for `n`, but its effective binding
is the RISC-V C ABI's third integer argument register, `x12`. -/
theorem validate_caller_provided_recovery :
    rawOccurrenceParams 140 ==
        [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "callerProvided", -1, 0)] ∧
      occurrenceParams 140 ==
        [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "reg", 12, 0)] := by
  native_decide

/-- **The withdrawal reader chain is loop-derived, not absent.** Each of the four field reads inside
`decodeWithdrawals`' element loop, and the `bytesAt` each forwards to, binds `offset` to
`x23 + k` where `x23` carries `index * WITHDRAWAL_SIZE`. DWARF gave no location for any of them; the
rows say what the machine actually does instead of leaving the occurrence predicate unsatisfiable. -/
theorem validate_loop_derived_withdrawal_offsets :
    occurrenceParams 46 == [("offset", "derived", 23, 0), ("len", "const", -1, 8)] ∧
      occurrenceParams 47 == [("offset", "derived", 23, 0)] ∧
      occurrenceParams 49 == [("offset", "derived", 23, 8)] ∧
      occurrenceParams 51 == [("offset", "derived", 23, 16)] ∧
      occurrenceParams 53 == [("offset", "derived", 23, 36)] ∧
      (rawOccurrenceParams 47).contains ("offset", "callerProvided", -1, 0) = true := by
  native_decide

/-- **The blob-schedule offsets are concrete.** The three nested reads are fixed at 0, 8, and 16;
none is left as an absent location. -/
theorem blob_schedule_binds_outside_arg_registers :
    occurrenceParams 116 == [] ∧
      occurrenceParams 117 == [("offset", "const", -1, 0)] ∧
      occurrenceParams 118 == [("offset", "const", -1, 8)] ∧
      occurrenceParams 119 == [("offset", "const", -1, 16)] := by native_decide

end BinaryFv.SSZ.Zesu.Elfling
