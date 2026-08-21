import BinaryFv.Zesu.MachineExecution.HLevel3RawEncoderSteps

/-!
# Level 3 returning `Encoder.raw` contracts

Five inlined sites share one exact machine theorem. Four sites set the source from the stack.
One site sets the length first and moves the source from `s2`.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.Zesu.MachineExecution
open BinaryFv.RiscV

abbrev Proposed_ssz_decode_observation_Encoder_raw_fi_1_4045_Contract : Prop :=
  (rawEncoderSetupContract 0x15548 32 0x15558 (RawEncoderStackSource 0x690)).Implements
    EndpointStep EndpointPc (pcInRanges rawEncoder4045ExecutionPcs)
    (pcInList rawEncoder4045ExitPcs)

abbrev Proposed_ssz_decode_observation_Encoder_raw_fi_1_40c3_Contract : Prop :=
  (rawEncoderSetupContract 0x156c0 20 0x156d0 RawEncoderX18Source).Implements
    EndpointStep EndpointPc (pcInRanges rawEncoder40c3ExecutionPcs)
    (pcInList rawEncoder40c3ExitPcs)

abbrev Proposed_ssz_decode_observation_Encoder_raw_fi_1_412a_Contract : Prop :=
  (rawEncoderSetupContract 0x158c4 32 0x158d4 (RawEncoderStackSource 0x6d0)).Implements
    EndpointStep EndpointPc (pcInRanges rawEncoder412aExecutionPcs)
    (pcInList rawEncoder412aExitPcs)

abbrev Proposed_ssz_decode_observation_Encoder_raw_fi_1_42a2_Contract : Prop :=
  (rawEncoderSetupContract 0x15bac 1 0x15bbc (RawEncoderStackSource 7)).Implements
    EndpointStep EndpointPc (pcInRanges rawEncoder42a2ExecutionPcs)
    (pcInList rawEncoder42a2ExitPcs)

abbrev Proposed_ssz_decode_observation_Encoder_raw_fi_1_45f6_Contract : Prop :=
  (rawEncoderSetupContract 0x15d1c 8 0x15d2c (RawEncoderStackSource 0)).Implements
    EndpointStep EndpointPc (pcInRanges rawEncoder45f6ExecutionPcs)
    (pcInList rawEncoder45f6ExitPcs)

theorem proposed_rawEncoder_4045_proved :
    Proposed_ssz_decode_observation_Encoder_raw_fi_1_4045_Contract :=
  rawEncoder4045Contract_implements

theorem proposed_rawEncoder_40c3_proved :
    Proposed_ssz_decode_observation_Encoder_raw_fi_1_40c3_Contract :=
  rawEncoder40c3Contract_implements

theorem proposed_rawEncoder_412a_proved :
    Proposed_ssz_decode_observation_Encoder_raw_fi_1_412a_Contract :=
  rawEncoder412aContract_implements

theorem proposed_rawEncoder_42a2_proved :
    Proposed_ssz_decode_observation_Encoder_raw_fi_1_42a2_Contract :=
  rawEncoder42a2Contract_implements

theorem proposed_rawEncoder_45f6_proved :
    Proposed_ssz_decode_observation_Encoder_raw_fi_1_45f6_Contract :=
  rawEncoder45f6Contract_implements

end BinaryFv.Zesu.Staging
