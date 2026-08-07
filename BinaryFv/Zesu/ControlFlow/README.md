# Zesu control flow

This directory derives structural facts about the instructions in the pinned Zesu binary: which words
decode, where functions begin and end, and how their instruction regions are formed. These facts say
how the compiled program is arranged, not what its source functions mean.

`Decode.lean` connects the canonical ELF image to Sail instruction decoding. `FunctionWords.lean`
collects decoded words into function-level regions. `MachineRegions.lean` checks the generated
per-instruction database against that decoding: instruction words, direct edges, ownership, and the
partition into strongly connected components (SCCs). An SCC is a maximal set of instructions that
can all reach one another; a nontrivial SCC marks a possible machine-code loop. The generated
whole-program model in `Elflings/` uses these facts to validate its entries, edges, reachability, and
nesting.

Behavioral requirements remain in `Contracts/`, so a compiler-induced control-flow change does not
silently change the specification being proved.

## Examples of established facts

The following are kernel-checked statements about the pinned production binary:

- `MachineRegions.validates_against_production` checks all 3,369 reachable instruction words against
  Sail decoding, checks every direct control-flow edge in both directions, and checks that ownership
  and strongly connected components each cover exactly those instructions.
- The same theorem checks a forward and reverse spanning tree inside every strongly connected
  component and a strictly increasing rank between components. Thus each proposed component is
  genuinely strongly connected and the graph obtained by collapsing components is acyclic.
- `Elflings.Validation.reachableAddresses_eq_directReachable` proves that the generated address set is
  exactly the set reachable from the exported entry through decoded direct control flow. It is neither
  missing reachable instructions nor padded with unreachable ones.
These statements establish the binary structure on which execution proofs can rely. They do not yet
establish that any function instance implements its Ethereum-spec meaning.
