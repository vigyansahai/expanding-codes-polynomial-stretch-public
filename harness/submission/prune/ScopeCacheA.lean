import Lean
open Lean Elab Command
set_option autoImplicit false
namespace CacheBoundarySmoke
private def dispatch (n : Nat) : Nat := n
@[simp] private theorem dispatch_eq (n : Nat) : dispatch n = n := rfl
theorem endpoint (n : Nat) : ∃ m : Nat, m = n := ⟨dispatch n, dispatch_eq n⟩
end CacheBoundarySmoke
attribute [-simp] CacheBoundarySmoke.dispatch_eq
