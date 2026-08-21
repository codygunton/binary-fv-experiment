import BinaryFv.Zesu.MachineExecution.HLevel3WriteOutputSteps

/-!
# Level 3 `extern_io.write_output` contracts

Seven inlined success sites share one exact machine theorem. The eighth source instance uses one
separate shared theorem for its five-step tail-call schedule.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.Zesu.MachineExecution

abbrev Proposed_extern_io_write_output_fi_1_3d8b_Contract : Prop :=
  WriteSuccessParentHashInstanceContract

abbrev Proposed_extern_io_write_output_fi_1_3db4_Contract : Prop :=
  WriteSuccessFeeRecipientInstanceContract

abbrev Proposed_extern_io_write_output_fi_1_3ddd_Contract : Prop :=
  WriteSuccessStateRootInstanceContract

abbrev Proposed_extern_io_write_output_fi_1_3e06_Contract : Prop :=
  WriteSuccessReceiptsRootInstanceContract

abbrev Proposed_extern_io_write_output_fi_1_3e2f_Contract : Prop :=
  WriteSuccessLogsBloomInstanceContract

abbrev Proposed_extern_io_write_output_fi_1_3e81_Contract : Prop :=
  WriteSuccessBlockHashInstanceContract

abbrev Proposed_extern_io_write_output_fi_1_4101_Contract : Prop :=
  WriteSuccessParentBeaconRootInstanceContract

abbrev Proposed_extern_io_write_output_fi_1_49b1_Contract : Prop :=
  WriteFailureRecordInstanceContract

theorem proposed_writeOutput_3d8b_proved : Proposed_extern_io_write_output_fi_1_3d8b_Contract :=
  writeSuccessParentHashInstanceContract

theorem proposed_writeOutput_3db4_proved : Proposed_extern_io_write_output_fi_1_3db4_Contract :=
  writeSuccessFeeRecipientInstanceContract

theorem proposed_writeOutput_3ddd_proved : Proposed_extern_io_write_output_fi_1_3ddd_Contract :=
  writeSuccessStateRootInstanceContract

theorem proposed_writeOutput_3e06_proved : Proposed_extern_io_write_output_fi_1_3e06_Contract :=
  writeSuccessReceiptsRootInstanceContract

theorem proposed_writeOutput_3e2f_proved : Proposed_extern_io_write_output_fi_1_3e2f_Contract :=
  writeSuccessLogsBloomInstanceContract

theorem proposed_writeOutput_3e81_proved : Proposed_extern_io_write_output_fi_1_3e81_Contract :=
  writeSuccessBlockHashInstanceContract

theorem proposed_writeOutput_4101_proved : Proposed_extern_io_write_output_fi_1_4101_Contract :=
  writeSuccessParentBeaconRootInstanceContract

theorem proposed_writeOutput_49b1_proved : Proposed_extern_io_write_output_fi_1_49b1_Contract :=
  writeFailureRecordInstanceContract_of_tailSchedule

end BinaryFv.Zesu.Staging
