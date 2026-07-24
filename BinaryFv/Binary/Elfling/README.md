# Architecture-independent Elfling data

This directory describes compiled routine function instances without depending on a particular instruction
set. [FunctionInstance.lean](FunctionInstance.lean) defines identities, regions, calls, inlined children, and
excluded routines.

Row D distinguishes two address sets for each function instance:

- the **owned region** contains the function instance's own instructions plus reachable helper routines that
  have no catalog contract and must be absorbed locally;
- the **execution extent** also contains every cataloged child or callee that the function instance may
  enter.

Local proofs retire only owned instructions and may use summaries for cataloged children. Closed
traces expand those summaries and therefore run within the larger extent.
[FunctionInstance.lean](FunctionInstance.lean) computes `ownedRanges` and the transfer-closed `extentRanges` from
program data; target-specific modules prove those computed ranges satisfy their generated checks.
