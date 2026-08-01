# Zesu control flow

This directory derives structural facts about the instructions in the pinned Zesu binary: which words
decode, where functions begin and end, and how their instruction regions are formed. These facts say
how the compiled program is arranged, not what its routines mean.

`Decode.lean` connects the canonical ELF image to Sail instruction decoding. `FunctionWords.lean`
collects decoded words into function-level regions. The generated whole-program model in `Elflings/`
uses these facts to validate its entries, edges, reachability, and nesting.

Behavioral requirements remain in `Contracts/`, so a compiler-induced control-flow change does not
silently change the specification being proved.
