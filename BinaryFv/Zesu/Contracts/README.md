# Contracts

`Machine.lean` defines the target-neutral endpoint trace interface. `DecodedResultRelation.lean`
compares Zesu observations with the EVM-Sail result, and `KnownBugs.lean` fixes the reviewed set of
permitted divergences; callers cannot choose additional exceptions.
