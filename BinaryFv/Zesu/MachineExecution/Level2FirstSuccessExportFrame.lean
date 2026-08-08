import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts

/-!
# Export frame for the first successful wrapper route

`FirstSuccessExportFrame` is the machine evidence that the first-success route must retain at the
generated wrapper exit.  It is exactly the concrete decomposition of `postZesuDecodeRaw` for the
fresh successful model; it introduces no route or contract assumption.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.RiscV
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.DecodedValue BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open LeanRV64DExecutable.Functions Register

/-- The first successful route's final public binding, kept as individual machine facts so the
route proof visibly establishes the attempted flag, status word, stored-result tag, and payload. -/
structure FirstSuccessExportFrame (args : ZesuDecodeRawArgs) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (entry after : State) : Prop where
  inputMemory : MemoryBytes after args.inputBase args.bytes
  code : canonicalContractParams.env.CodeIntact after
  returnCode : after.regs.get? x10 = some (BitVec.ofNat 64 1)
  platform : Agree platformPreserved entry after
  retired : RetiredCounterPresent after
  attempted : FlagRep after canonicalContractParams.globals.attempted true
  status : Word32LERep after canonicalContractParams.globals.status DecodeStatus.ok.code
  storedTag : DecodedValue.OptionTagRep after
    (canonicalContractParams.globals.storedResult +
      canonicalContractParams.globals.storedResultObject.discriminantOffset) true
  storedValue : canonicalContractParams.repStatelessInput args.inputBase args.bytes value after
    canonicalContractParams.resultBuffer

/-- The named first-success frame is definitionally the exported postcondition after normalizing
the fresh decoder-global model. -/
theorem FirstSuccessExportFrame.postZesuDecodeRaw
    {args : ZesuDecodeRawArgs} {value : BinaryFv.Specs.SSZ.StatelessInput} {entry after : State}
    (frame : FirstSuccessExportFrame args value entry after) :
    postZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args (.ok value) entry after := by
  refine ⟨frame.inputMemory, frame.code, frame.returnCode, frame.platform, frame.retired, ?_⟩
  have globals : resultingGlobals DecoderGlobalsModel.fresh (.ok value) =
      { attempted := true, status := .ok, stored := some value } := by
    simp [resultingGlobals, callOutcome, DecoderGlobalsModel.fresh, DecodeCallOutcome.status,
      DecodeCallOutcome.stored]
  rw [globals]
  exact ⟨⟨frame.attempted, frame.status⟩, ⟨frame.storedTag, frame.storedValue⟩⟩

end BinaryFv.Zesu.MachineExecution
