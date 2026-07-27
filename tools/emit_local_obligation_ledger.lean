/-
Emit the build-derived local-obligation ledger. The committed output is a reviewable pin:

    lake env lean tools/emit_local_obligation_ledger.lean \
      > targets/ssz/zesu/trace/LOCAL_OBLIGATION_LEDGER.md

`nix/proof.nix` regenerates it and diffs byte-for-byte. A changed classification therefore fails
with the pin-ready diff instead of being normalized away.
-/

import BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger

open BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger

#eval IO.print report
