import Lake
open Lake DSL

package «expanding-codes-feasibility» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  weakLeanArgs := #["-M6144", "-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Feasibility

lean_lib Definitions

lean_lib Theorems

lean_lib Solutions

@[default_target]
lean_lib ExpandingCodes
