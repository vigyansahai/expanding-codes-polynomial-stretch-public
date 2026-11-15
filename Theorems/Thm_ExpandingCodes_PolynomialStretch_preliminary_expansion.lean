import ExpandingCodes.Probability.PreliminaryExpansion
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter
/-- Lemma 2.6. Multiplication by n^(1/ε) retains its little-o assertion. -/
theorem preliminary_expansion (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    Tendsto (fun n =>
      uniformProb (fun s : Forms (g n).F (dimension ε) (arity ε) =>
        ¬ PreliminaryGood ε n (g n) s) * (n : ℝ) ^ (1 / ε))
      atTop (nhds 0) := by
  exact preliminary_expansion_limit ε hε g

end ExpandingCodes.PolynomialStretch
