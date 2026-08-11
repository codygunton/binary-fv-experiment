import BinaryFv.Ssz.Specification

-- Both extracted machine semantics and the SSZ reference model must inhabit one Lean environment.
#check Register
#check Evm.Functions.decode_stateless_input_ref
#check Evm.Functions.decode_stateless_input
#check BinaryFv.Ssz.SailDecode
#check BinaryFv.Ssz.knownBugs
