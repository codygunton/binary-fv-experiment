import GeneratedBindings

/-!
# Validation of the extracted occurrence bindings

`GeneratedBindings.lean` is *untrusted* generated data: the entry-time location of every occurrence's
formal parameters, resolved from DWARF `.debug_loc` at each occurrence's entry PC (see
`tools/generate_elfling_program.py --out-bindings`). Each parameter is classified as:

- `reg` / `fbreg` / `breg` / `addr` — a concrete register, frame slot, base+offset, or memory address
  (emitted occurrences carry their real optimized ABI this way);
- `const` — the argument was constant-folded at this occurrence;
- `callerProvided` — the optimizer emitted no location; the argument flows from the caller and its
  concrete location is pinned when this occurrence's local contract is proved. This is **never** the
  source-function ABI silently assigned.

This module checks that data: every parameter carries a valid classification (nothing undecodable),
and the emitted entry ABIs are pinned exactly so mutation or omission fails `native_decide`.
-/

namespace BinaryFv.SSZ.Zesu.Elfling

open BinaryFv.SSZ.Zesu.Elfling.GeneratedBindings

/-- The recorded `(name, kind, register-or-address, offset)` parameters of occurrence `i`. -/
def occurrenceParams (i : Nat) : List (String × String × Int × Int) :=
  bindings.filterMap fun r => if r.1 == i then some (r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2) else none

/-- The classifications a resolved binding may carry. `unresolved` (an undecodable DWARF location
expression) is deliberately absent, so its presence fails `bindingsClassified`. -/
def validBindingKinds : List String :=
  ["reg", "fbreg", "breg", "addr", "const", "callerProvided"]

/-- Every parameter carries a valid classification — nothing is left undecodable, and nothing is
silently assigned the source ABI. This is the "unresolved binding blocks the row" gate. -/
def allBindingsClassified : Bool := bindings.all fun r => validBindingKinds.contains r.2.2.1

theorem bindingsClassified : allBindingsClassified = true := by native_decide

/-! ## Emitted-occurrence ABI (mutation- and omission-sensitive) -/

/-- **`zesu_decode_raw`'s real C ABI**: the input pointer in `a0` (x10) and the length in `a1` (x11).
Pinned exactly, so mutating a register or dropping a parameter fails `native_decide`. -/
def zesuDecodeRawAbi : Bool :=
  occurrenceParams 1 == [("input", "reg", 10, 0), ("input_len", "reg", 11, 0)]

theorem zesu_decode_raw_abi : zesuDecodeRawAbi = true := by native_decide

/-- **`zesu_raw_alloc`'s ABI**: the byte count in `a0` (x10) and the alignment in `a1` (x11). -/
def zesuRawAllocAbi : Bool :=
  occurrenceParams 0 == [("bytes", "reg", 10, 0), ("alignment", "reg", 11, 0)]

theorem zesu_raw_alloc_abi : zesuRawAllocAbi = true := by native_decide

/-! ## Coverage

Pinning the totals makes an omitted occurrence or parameter fail the build. -/

/-- The number of the 141 occurrences carrying at least one parameter binding. -/
def boundOccurrenceCount : Nat :=
  (List.range 141).countP fun i => !(occurrenceParams i).isEmpty

theorem bound_occurrence_count : boundOccurrenceCount = 110 := by native_decide

/-- The total number of parameter bindings across all occurrences. -/
def totalParamCount : Nat := bindings.length

theorem total_param_count : totalParamCount = 137 := by native_decide

/-- No binding is `callerProvided`-by-omission of the whole row: every recorded parameter is present
with an explicit classification (the `filterMap` above never drops a row). Recorded for clarity. -/
theorem every_binding_has_kind :
    bindings.all (fun r => r.2.2.1 != "") = true := by native_decide

end BinaryFv.SSZ.Zesu.Elfling
