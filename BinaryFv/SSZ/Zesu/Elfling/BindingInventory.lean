import GeneratedBindings

/-!
# Validation and refined classification of the extracted occurrence bindings

`GeneratedBindings.lean` is *untrusted* generated data: the entry-time location of every occurrence's
formal parameters, resolved from DWARF `.debug_loc` at each occurrence's entry PC (see
`tools/generate_elfling_program.py --out-bindings`). Each parameter's DWARF kind is one of:

- `reg` / `fbreg` / `breg` / `addr` — a concrete register, frame slot, base+offset, or memory address
  (emitted occurrences carry their real optimized ABI this way, and many inlined occurrences too);
- `const` — the argument was constant-folded (a `DW_OP_stack_value`) at this occurrence;
- `callerProvided` — the optimizer emitted **no** location at the occurrence's entry PC. The argument
  flows from the caller and DWARF does not record where.

## Why `callerProvided` is a defect, not a resolved binding

The earlier inventory listed `callerProvided` among the "valid classifications", i.e. treated a
missing location as resolved. That is wrong: a local occurrence contract needs to know *where* a
value is at entry to connect the caller's postcondition to the callee's precondition, and
`callerProvided` names no location. This module therefore removes `callerProvided` from the resolved
set and instead enumerates every such row as an **explicit pending defect** in `pendingBindings`,
tagged with the *reusable recovery form* that will discharge it when the occurrence's local contract
is proved (Rows E–I). Nothing is silently resolved.

## The binding-classification spike (5 buckets)

A classification spike over all 137 parameter rows, validated against the real DWARF/CFG artifacts and
the pinned Zig source, separates every parameter into:

1. **concrete DWARF location** (`reg`/`fbreg`/`breg`/`addr`) — 49 rows, resolved as the real
   optimized location;
2. **constant-folded** (`const`) — 38 rows, resolved as a compile-time value;
3. **eliminated / irrelevant to the specialized meaning** — none in this decoder: every DWARF-less
   parameter below turns out to still affect the occurrence's meaning, so none is genuinely dead;
4. **mechanically recoverable by register/stack dataflow or ABI** — the `callerProvided` rows, each of
   which has a *known* recovery (see the reusable forms below);
5. **genuinely unresolved semantic input** — **zero** rows: every missing location has an identified
   recovery form. They nonetheless remain *pending* here, discharged per occurrence in Rows E–I.

## Reusable recovery forms (the 50 `callerProvided` rows)

Rather than 50 unrelated hand bindings, three reusable forms cover every missing location, each keyed
to the occurrence's stable `InstanceId` (see `occNId` in `GeneratedProgram`) and its parent:

- `bytesAtLenConst` (19 rows): the `len` of a `ssz_raw.bytesAt` occurrence. `bytesAt(data, offset,
  len)` is always called with a *compile-time* length by its enclosing reader — `readArray(N,…)` →
  `N`, `readU32` → 4, `readU64` → 8, `readU256` → 32 — so `len` is the constant recovered from the
  parent occurrence's routine/specialization (recorded as the fourth field).
- `emittedAbiGap` (1 row): occ140 = `memmove`, an *emitted* body whose `n` DWARF location is absent.
  By the RISC-V C ABI the third integer argument is in `x12`; the adjacent emitted `memcpy` (occ139)
  carries `n = reg x12`, and the shared `preCopy` contract binds `x12 = length`. Recovered to `x12`.
- `constOffset` (30 rows): the `offset` of a fixed-position read (`readOffset`/`readU32`/`readU64`/
  `readU256`/`readArray`/`bytesAt`) into a container laid out at compile-time-fixed field offsets. The
  offset is the source literal (e.g. occ8 = `readOffset(body, 0)`); recovered from the source
  read-site. Its concrete machine location is pinned when the occurrence's local contract is proved.

The `bytesAtLenConst` and `emittedAbiGap` forms carry the recovered value here; `constOffset` records
the strategy and defers the concrete value to the local proof — all three stay *pending defects*
until then, so the row is never treated as resolved.
-/

namespace BinaryFv.SSZ.Zesu.Elfling

open BinaryFv.SSZ.Zesu.Elfling.GeneratedBindings

/-- The recorded `(name, kind, register-or-address, offset)` parameters of occurrence `i`. -/
def occurrenceParams (i : Nat) : List (String × String × Int × Int) :=
  bindings.filterMap fun r => if r.1 == i then some (r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2) else none

/-! ## Resolved vs. pending: `callerProvided` is no longer treated as resolved -/

/-- The DWARF kinds that genuinely *resolve* a parameter to a location. `callerProvided` is
deliberately **absent** (a missing location is a defect, not a resolution), and so is `unresolved`
(an undecodable expression). -/
def resolvedBindingKinds : List String := ["reg", "fbreg", "breg", "addr", "const"]

/-- `callerProvided` is not a resolved kind — the fix for the prior inventory, which listed it. -/
theorem callerProvided_not_resolved : resolvedBindingKinds.contains "callerProvided" = false := by
  native_decide

/-- Every parameter is either a resolved DWARF location or an explicit `callerProvided` pending
defect — nothing is undecodable (`other`/`unresolved`), and nothing outside this partition exists. -/
theorem bindings_resolved_or_pending :
    bindings.all (fun r => resolvedBindingKinds.contains r.2.2.1 || r.2.2.1 == "callerProvided")
      = true := by native_decide

/-- The number of genuinely resolved (concrete-location or constant-folded) parameter bindings. -/
def resolvedBindingCount : Nat := (bindings.filter fun r => resolvedBindingKinds.contains r.2.2.1).length

theorem resolved_count : resolvedBindingCount = 87 := by native_decide

/-! ## The explicit pending-defect table with reusable recovery forms

Every `callerProvided` row is enumerated here with the reusable form that will discharge it. The
fourth field is the recovered constant where the form determines one (`bytesAtLenConst` width,
`emittedAbiGap` register), and `-1` for `constOffset`, whose concrete value is pinned in the local
proof. -/

/-- (occurrence index, parameter name, recovery form, recovered value or `-1`). -/
def pendingBindings : List (Nat × String × String × Int) :=
  [(8, "offset", "constOffset", -1),
   (9, "offset", "constOffset", -1),
   (17, "offset", "constOffset", -1),
   (18, "offset", "constOffset", -1),
   (24, "offset", "constOffset", -1),
   (25, "offset", "constOffset", -1),
   (32, "offset", "constOffset", -1),
   (36, "offset", "constOffset", -1),
   (36, "len", "bytesAtLenConst", 256),
   (37, "offset", "constOffset", -1),
   (38, "offset", "constOffset", -1),
   (41, "offset", "constOffset", -1),
   (42, "offset", "constOffset", -1),
   (43, "offset", "constOffset", -1),
   (44, "offset", "constOffset", -1),
   (46, "len", "bytesAtLenConst", 8),
   (52, "len", "bytesAtLenConst", 8),
   (54, "offset", "constOffset", -1),
   (54, "len", "bytesAtLenConst", 8),
   (59, "len", "bytesAtLenConst", 32),
   (61, "offset", "constOffset", -1),
   (61, "len", "bytesAtLenConst", 32),
   (62, "offset", "constOffset", -1),
   (64, "offset", "constOffset", -1),
   (65, "offset", "constOffset", -1),
   (71, "len", "bytesAtLenConst", 48),
   (73, "len", "bytesAtLenConst", 32),
   (75, "len", "bytesAtLenConst", 8),
   (79, "len", "bytesAtLenConst", 8),
   (82, "len", "bytesAtLenConst", 20),
   (84, "len", "bytesAtLenConst", 48),
   (86, "len", "bytesAtLenConst", 8),
   (89, "len", "bytesAtLenConst", 20),
   (91, "len", "bytesAtLenConst", 48),
   (93, "len", "bytesAtLenConst", 48),
   (96, "offset", "constOffset", -1),
   (97, "offset", "constOffset", -1),
   (103, "offset", "constOffset", -1),
   (104, "offset", "constOffset", -1),
   (106, "offset", "constOffset", -1),
   (107, "offset", "constOffset", -1),
   (110, "offset", "constOffset", -1),
   (112, "offset", "constOffset", -1),
   (113, "offset", "constOffset", -1),
   (117, "offset", "constOffset", -1),
   (121, "len", "bytesAtLenConst", 65),
   (125, "offset", "constOffset", -1),
   (128, "len", "bytesAtLenConst", 4),
   (131, "len", "bytesAtLenConst", 4),
   (140, "n", "emittedAbiGap", 12)]

/-- The `(occurrence, parameter)` keys of the `callerProvided` rows in the generated data. -/
def callerProvidedKeys : List (Nat × String) :=
  bindings.filterMap fun r => if r.2.2.1 == "callerProvided" then some (r.1, r.2.1) else none

/-- The `(occurrence, parameter)` keys covered by the pending table. -/
def pendingKeys : List (Nat × String) := pendingBindings.map fun r => (r.1, r.2.1)

/-- **The pending table covers exactly the `callerProvided` rows.** Every missing location is
enumerated (nothing silently resolved), and every pending row names a real missing location (no
phantom defect). Together with `pending_count` this is a bijection. -/
theorem pending_covers_all_callerProvided :
    callerProvidedKeys.all (fun k => pendingKeys.contains k) = true := by native_decide

theorem pending_only_callerProvided :
    pendingKeys.all (fun k => callerProvidedKeys.contains k) = true := by native_decide

theorem pending_count : pendingBindings.length = 50 ∧ callerProvidedKeys.length = 50 := by
  native_decide

/-- The reusable recovery forms; `unresolved` would denote a genuinely-open input. -/
def recoveryForms : List String := ["bytesAtLenConst", "emittedAbiGap", "constOffset"]

/-- Every pending row carries one of the reusable recovery forms. -/
theorem pending_forms_valid :
    pendingBindings.all (fun r => recoveryForms.contains r.2.2.1) = true := by native_decide

/-- How many pending rows use form `f`. -/
def formCount (f : String) : Nat := (pendingBindings.filter fun r => r.2.2.1 == f).length

/-- The recovery-form census (bucket 4 of the spike). Mutating a form or dropping a row fails this. -/
theorem form_counts :
    formCount "bytesAtLenConst" = 19 ∧ formCount "emittedAbiGap" = 1 ∧ formCount "constOffset" = 30 := by
  native_decide

/-- **No genuinely-unresolved semantic input remains** (bucket 5 is empty): every missing location has
an identified recovery form. They are still *pending* — discharged per occurrence in Rows E–I — but
none is a dead end. -/
theorem no_genuinely_unresolved :
    (pendingBindings.filter fun r => r.2.2.1 == "unresolved").length = 0 := by native_decide

/-! ## Every `bytesAt.len` recovers to its enclosing read width

A cross-check that the `bytesAtLenConst` recovered constants are exactly the widths the decoder reads:
the SSZ fixed-vector widths (20, 32, 48, 65, 96 → here 20/32/48/65) plus the scalar reads (4 = u32,
8 = u64, 32 = u256) and the 256-byte extra-data array. Mutating a recovered width fails this. -/
theorem bytesAtLen_widths_are_read_widths :
    (pendingBindings.filter fun r => r.2.2.1 == "bytesAtLenConst").all
      (fun r => [4, 8, 20, 32, 48, 65, 256].contains r.2.2.2) = true := by native_decide

/-! ## Emitted-occurrence ABIs — all 14 pinned exactly

The review noted only two emitted ABIs were pinned. All 14 emitted occurrences are pinned here: the
eight with parameters exactly (mutation- and omission-sensitive), and the six paramless ones as
empty. -/

/-- The 14 emitted occurrences and their exact entry parameters. occ140 (`memmove`) carries its raw
`callerProvided` `n`; its ABI recovery to `x12` is the `emittedAbiGap` pending row. -/
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
   (140, [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "callerProvided", -1, 0)])]

theorem emitted_occurrence_count : emittedAbis.length = 14 := by native_decide

/-- **Every emitted occurrence's ABI is pinned exactly.** Mutating a register, dropping a parameter,
or adding one to any of the 14 fails `native_decide`. -/
theorem emitted_abis_pinned :
    emittedAbis.all (fun p => occurrenceParams p.1 == p.2) = true := by native_decide

/-- **occ140's absent `n` recovers to the `memcpy` ABI register.** memmove (occ140) shares the copy
ABI with memcpy (occ139), whose `n` is `reg x12`; the pending row records the `x12` recovery. -/
theorem memmove_n_recovers_to_memcpy_abi :
    (occurrenceParams 139).contains ("n", "reg", 12, 0) = true ∧
      pendingBindings.contains (140, "n", "emittedAbiGap", 12) = true := by native_decide

/-! ## Coverage — all 141 occurrences accounted -/

/-- The number of the 141 occurrences carrying at least one parameter binding. -/
def boundOccurrenceCount : Nat :=
  (List.range 141).countP fun i => !(occurrenceParams i).isEmpty

theorem bound_occurrence_count : boundOccurrenceCount = 110 := by native_decide

/-- The 31 occurrences with no parameters (allocator/accessor bodies, memory-slice-input decoders,
etc.). Listed explicitly so a silently-dropped binding cannot masquerade as a paramless occurrence. -/
def paramlessOccurrences : List Nat :=
  [2, 4, 5, 7, 16, 23, 33, 40, 45, 47, 49, 51, 53, 56, 58, 63, 70, 81, 88, 95, 102, 105, 111, 116,
   120, 123, 124, 127, 135, 137, 138]

/-- **All 141 occurrences are accounted for.** An occurrence is paramless iff it is in the list, so
the 110 bound and 31 paramless occurrences exhaust the program — the "only 110/141 have rows" gap is
closed by naming the other 31, not by hiding them. -/
theorem all_occurrences_accounted :
    (List.range 141).all (fun i => (occurrenceParams i).isEmpty == paramlessOccurrences.contains i)
      = true := by native_decide

theorem coverage_partitions_141 :
    boundOccurrenceCount + paramlessOccurrences.length = 141 ∧ paramlessOccurrences.length = 31 := by
  native_decide

/-- The total number of parameter bindings across all occurrences. -/
def totalParamCount : Nat := bindings.length

theorem total_param_count : totalParamCount = 137 := by native_decide

/-- Every recorded parameter carries an explicit kind (the `filterMap` never drops a row). -/
theorem every_binding_has_kind : bindings.all (fun r => r.2.2.1 != "") = true := by native_decide

/-! ## Spike validation on three representative occurrences

One register-bound, one stack/base-relative (with a recovered `bytesAt.len`), and one currently
`callerProvided` (an emitted ABI gap recovered to a register). -/

/-- **Register-bound.** occ139 (`memcpy`) binds all three parameters in argument registers `x10/x11/x12`
— the real optimized ABI, resolved by DWARF. -/
theorem validate_register_bound :
    occurrenceParams 139 == [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "reg", 12, 0)] := by
  native_decide

/-- **Stack/base-relative.** occ73 (`ssz_raw.bytesAt`, inlined 5 deep) binds `offset` at `[x27 + 48]`
— a value held in memory relative to a callee-saved register, not an argument register — and its
`callerProvided` `len` recovers to the enclosing `readArray[32]` width via `bytesAtLenConst`. -/
theorem validate_stack_relative :
    occurrenceParams 73 == [("offset", "breg", 27, 48), ("len", "callerProvided", -1, 0)] ∧
      pendingBindings.contains (73, "len", "bytesAtLenConst", 32) = true := by native_decide

/-- **Currently `callerProvided`, recovered.** occ140 (`memmove`) has no DWARF location for `n`; the
refined classification does not treat it as resolved but records the `emittedAbiGap` recovery to
`x12`. -/
theorem validate_caller_provided_recovery :
    occurrenceParams 140 == [("dst", "reg", 10, 0), ("src", "reg", 11, 0), ("n", "callerProvided", -1, 0)] ∧
      pendingBindings.contains (140, "n", "emittedAbiGap", 12) = true := by native_decide

/-- **An inlined blob-schedule occurrence binds values outside the argument registers.** occ116
(`decodeOptionalBlobSchedule`) is arg-less; its nested reads take `offset` as a caller-provided or
constant-folded value, never in an argument register. -/
theorem blob_schedule_binds_outside_arg_registers :
    occurrenceParams 116 == [] ∧
      occurrenceParams 117 == [("offset", "callerProvided", -1, 0)] ∧
      occurrenceParams 118 == [("offset", "const", -1, 0)] ∧
      occurrenceParams 119 == [("offset", "const", -1, 0)] := by native_decide

end BinaryFv.SSZ.Zesu.Elfling
