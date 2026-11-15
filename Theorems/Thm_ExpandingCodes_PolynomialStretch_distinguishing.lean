import ExpandingCodes.Probability.Distinguishing
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter
open scoped BigOperators
/-- Proposition 2.5. The two exponential constants are instantiated from its proof. -/
theorem distinguishing (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Geometry (dimension ε) n,
      uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε g y = true) ≤
        Real.exp (-(ε ^ 2 / 32) * rowCount (dimension ε) n) ∧
      ∀ (s : Forms g.F (dimension ε) (arity ε))
        (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n),
        (∀ e : Word (rowCount (dimension ε) n),
          (weight e : ℝ) ≤ (1 / 2 - ε) * rowCount (dimension ε) n →
          rankTest ε g ((combined g s h).mulVec x + e) = true) ∧
        (∑ e : Word (rowCount (dimension ε) n),
          bernoulliWord (rowCount (dimension ε) n) (1 / 2 - ε) e *
            (if rankTest ε g ((combined g s h).mulVec x + e) then (1 : ℝ) else 0)) ≥
          1 - Real.exp (-(ε ^ 2 / 2) * rowCount (dimension ε) n) := by
  exact rankTest_distinguishing ε hε

end ExpandingCodes.PolynomialStretch
