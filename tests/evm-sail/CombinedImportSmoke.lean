import BinaryFv
import Evm.Lib.Ssz.StatelessInput

-- Both extracted machine semantics and the SSZ reference model must inhabit one Lean environment.
#check Register
#check Evm.Functions.decode_stateless_input_ref
#check Evm.Functions.decode_stateless_input
