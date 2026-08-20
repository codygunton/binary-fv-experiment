# hLevel3 staging

`HLevel3.lean` contains generated contract-design holes and parent-proof holes. Production modules do
not import this directory. Generate the file through `zesuSszDecodeHLevel3Prework`; do not edit it by
hand.

Each parent theorem comment lists its Level 3 children, earlier Level 2 results, parent-owned glue,
preferred proof APIs, repeated motifs, close proved examples, and frame rules. Contract definitions
remain `sorry` until structural evidence, source review, and empirical evidence support an exact
machine contract.

`HLevel3IdiomChecks.lean` checks every Lean declaration in `hlevel3_proof_idioms.json`. The Nix check
also compares both generated Lean files with these committed copies. This check prevents guidance
and staging from drifting apart.
