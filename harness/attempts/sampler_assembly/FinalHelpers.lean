import ExpandingCodes.Computation.SamplerAssembly

set_option autoImplicit false
namespace ExpandingCodes.Computation.SamplerAssembly.Concrete
open ExpandingCodes.PolynomialStretch

theorem fieldSize_covers_arity (d n k : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (hkn : k ≤ n) :
    k ≤ fieldSize d n := by
  calc
    k ≤ n := hkn
    _ = n^1 := by simp
    _ ≤ n^(2*d) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ fieldSize d n := fieldSize_lower d n

#print axioms fieldSize_covers_arity
end ExpandingCodes.Computation.SamplerAssembly.Concrete
