import Lake
open Lake DSL

package sha_fv_experiment where

require «cryptography» from "./specs/sha-3"
require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.27.0"

@[default_target]
lean_lib ShaFv where
