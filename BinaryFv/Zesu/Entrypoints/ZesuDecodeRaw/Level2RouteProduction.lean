import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2ConditionalCapstone

/-!
# Level 2 non-first route production

This module derives the complete failed-first-decode route choice from the two selected Level 2
contracts. It keeps the semantic case split separate from the capstone that converts a chosen route
to the exported wrapper contract.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Elflings.Generated
open BinaryFv.Zesu.MachineExecution
open LeanRV64DExecutable.Functions Register

/-- Every failed first `decodeRaw` result selects one actual wrapper route. `invalidSsz` retries:
the ERE-prefix result selects a retry rejection or success route. The other first errors use the
wrapper's propagation route directly. -/
theorem nonFirstRoutesFromEntry_of_level2
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (memcpy : CompiledMemcpyInstanceContract) :
    NonFirstRoutesFromEntry := by
  intro args stackBase fromStep entry rawError source machine rawResult
  cases raw : meaningDecodeRaw args.bytes with
  | ok value =>
      simp [raw] at rawResult
  | error error =>
      have rawResult' : meaningDecodeRaw args.bytes = .error error := raw
      cases error with
      | invalidSsz =>
          by_cases exactPrefix : meaningHasExactErePrefix args.bytes = true
          · cases decoded : meaningDecode args.bytes with
            | ok value =>
                exact first_invalid_exact_success_route_from_entry allocator decode memcpy source
                  machine rawResult' exactPrefix value decoded
            | error error =>
                exact first_invalid_exact_error_route_from_entry allocator decode source machine
                  rawResult' exactPrefix error decoded
          · exact first_invalid_nonexact_routes_from_entry allocator decode source machine rawResult'
              (by
                cases exact : meaningHasExactErePrefix args.bytes <;> simp_all)
      | unknownFork =>
          exact first_propagated_error_route_from_entry allocator decode source machine .unknownFork
            (by decide) rawResult'
      | outOfMemory =>
          exact first_propagated_error_route_from_entry allocator decode source machine .outOfMemory
            (by decide) rawResult'

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
