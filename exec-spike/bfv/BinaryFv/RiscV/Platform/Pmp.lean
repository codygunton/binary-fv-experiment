import BinaryFv.RiscV.Platform.Fetch

namespace BinaryFv.RiscV

open PreSail
open Sail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

/-- exec-spike repair: the specialised model has no PMP entries, so `pmpCheck` is the pure
constant `none`; the stock loop machinery and the `FetchPmpDisabled` premise were removed.
The Machine-mode PMP check never faults. -/
theorem pmpCheck_machine_of_disabled (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) :
    pmpCheck address width access .Machine = none := rfl

end BinaryFv.RiscV
