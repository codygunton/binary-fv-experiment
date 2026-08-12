import BinaryFv.Ssz.Level1Contracts

-- Both extracted machine semantics and the SSZ reference model must inhabit one Lean environment.
#check Register
#check Evm.Functions.decode_stateless_input_ref
#check Evm.Functions.decode_stateless_input
#check BinaryFv.Ssz.SailDecode
#check BinaryFv.Ssz.knownBugs
#check BinaryFv.Ssz.decodeZesuObservation
#check BinaryFv.Ssz.decodedResultRel
#check BinaryFv.Ssz.Level1ContractAssumptions
