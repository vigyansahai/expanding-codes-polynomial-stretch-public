import ExpandingCodes.Probability.HashExpansion
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter
/-- Lemma 2.7. The little-o envelope is uniform over all admissible preliminary outputs. -/
theorem hash_expansion (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧
      Tendsto (fun n => δ n * (n : ℝ) ^ (1 / ε)) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ s : Forms (g n).F (dimension ε) (arity ε),
        PreliminaryGood ε n (g n) s →
        uniformProb (fun h : Hashes (g n).F (arity ε) (buckets ε n) =>
          ¬ Expanding (combined (g n) s h) (1 - ε) (arity ε) ((n : ℝ) ^ (1 - ε))) ≤ δ n := by
  exact hash_expansion_envelope ε hε g

end ExpandingCodes.PolynomialStretch
