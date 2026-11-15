import Lean
import harness.submission.prune.ScopeCacheB
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let n := mkPrivateNameCore `harness.submission.prune.ScopeCacheA `CacheBoundarySmoke.dispatch_eq
  let simp ← Meta.getSimpTheorems
  let active := simp.isDeclToUnfold n || simp.isLemma (.decl n true false) || simp.isLemma (.decl n false false) ||
    simp.isLemma (.decl n true true) || simp.isLemma (.decl n false true)
  IO.println s!"private helper present={env.contains n}; active simp={active}"
  if active then throwError "Module-public forwarding still exports private simp attribute"
#print axioms CacheBoundarySmoke.endpoint
