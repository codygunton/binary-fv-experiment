import BinaryFv.Zesu.Root

-- Both extracted machine semantics and the SSZ reference model must inhabit one Lean environment.
#check Register
#check Evm.Functions.decode_stateless_input_ref
#check Evm.Functions.decode_stateless_input
#check BinaryFv.Specs.SSZ.SailDecode
#check BinaryFv.Zesu.knownBugs
#check BinaryFv.Zesu.decodeZesuObservation
#check BinaryFv.Zesu.decodedResultRel
#check BinaryFv.Zesu.Level1ContractAssumptions
#check BinaryFv.Zesu.root_compliance
