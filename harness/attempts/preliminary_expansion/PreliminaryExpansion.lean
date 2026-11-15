import ExpandingCodes.Probability.PreliminaryCounting
import ExpandingCodes.Construction.ExpansionParameters

set_option autoImplicit false
open scoped Classical
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

/-- The exact canonical little-o assertion for preliminary expansion, uniformly in public geometry. -/
theorem preliminary_expansion_limit (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    Tendsto (fun n =>
      uniformProb (fun s : Forms (g n).F (dimension ε) (arity ε) =>
        ¬ PreliminaryGood ε n (g n) s) * (n : ℝ) ^ (1 / ε))
      atTop (nhds 0) := by
  have hd : 0 < dimension ε := (by decide : 0 < 4).trans_le (dimension_ge_four ε hε)
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ uniformProb (fun s : Forms (g n).F (dimension ε) (arity ε) =>
        ¬ PreliminaryGood ε n (g n) s) * (n : ℝ) ^ (1 / ε) := by
    apply Eventually.of_forall
    intro n
    rw [uniformProb_eq_card_filter]
    positivity
  have hupper : ∀ᶠ n : ℕ in atTop,
      uniformProb (fun s : Forms (g n).F (dimension ε) (arity ε) =>
        ¬ PreliminaryGood ε n (g n) s) * (n : ℝ) ^ (1 / ε) ≤
      2 * (preliminaryRatio ε n * (n : ℝ) ^ (1 / ε)) := by
    filter_upwards [eventually_preliminary_parameters ε hε] with n hn
    have hfinite := preliminary_bad_prob_le_two_base ε n (g n) hd hn.1 hn.2
    calc
      _ ≤ (2 * preliminaryRatio ε n) * (n : ℝ) ^ (1 / ε) :=
        mul_le_mul_of_nonneg_right hfinite (by positivity)
      _ = _ := mul_assoc _ _ _
  apply squeeze_zero' hnonneg hupper
  simpa only [mul_zero] using (tendsto_preliminaryRatio_scaled ε hε).const_mul 2

end ExpandingCodes.PolynomialStretch
