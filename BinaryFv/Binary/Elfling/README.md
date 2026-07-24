# Architecture-independent Elfling data

This directory describes compiled routine occurrences without depending on a particular instruction
set. `Instance.lean` defines identities, regions, calls, inlined children, and excluded routines.

Row D distinguishes two address sets for each occurrence:

- the **owned region** contains the occurrence's own instructions plus reachable helper routines that
  have no catalog contract and must be absorbed locally;
- the **execution extent** also contains every cataloged child or callee that the occurrence may
  enter.

Local proofs retire only owned instructions and may use summaries for cataloged children. Closed
traces expand those summaries and therefore run within the larger extent. The transfer closure and
range checks in `Instance.lean` compute these sets from generated program data.
