import Lean
open Lean Elab Command
set_option autoImplicit false

section FlattenModuleOne
namespace CacheScopeSmoke
private def dispatch (n : Nat) : Nat := n
@[simp] private theorem dispatch_eq (n : Nat) : dispatch n = n := rfl
end CacheScopeSmoke
end FlattenModuleOne

section FlattenModuleTwo
namespace CacheScopeConsumer
open CacheScopeSmoke (dispatch dispatch_eq)
example (n : Nat) : dispatch n = n := dispatch_eq n
example (n : Nat) : CacheScopeSmoke.dispatch n = n := CacheScopeSmoke.dispatch_eq n
end CacheScopeConsumer
end FlattenModuleTwo

run_meta do
  let env ← getEnv
  let n := mkPrivateName env `CacheScopeSmoke.dispatch_eq
  unless env.contains n do throwError "Private helper disappeared across sections"
  let simp ← Meta.getSimpTheorems
  unless simp.isLemma (.decl n true false) || simp.isLemma (.decl n false false) ||
      simp.isLemma (.decl n true true) || simp.isLemma (.decl n false true) do
    throwError "Expected private helper simp attribute is absent"

attribute [-simp] CacheScopeSmoke.dispatch_eq

run_meta do
  let env ← getEnv
  let n := mkPrivateName env `CacheScopeSmoke.dispatch_eq
  let simp ← Meta.getSimpTheorems
  if simp.isLemma (.decl n true false) || simp.isLemma (.decl n false false) ||
      simp.isLemma (.decl n true true) || simp.isLemma (.decl n false true) then
    throwError "Private helper simp attribute was not cleared"
  IO.println "Private aliases survived sections/selective open; fully qualified simp clearing passed"
