import ExpandingCodes.Probability.Distinguishing

set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem eventual_uniform_rank_acceptance (ε θ : ℝ)
    (hε : 0 < ε ∧ ε < 1 / 2) (hθ : ε / 2 < θ ∧ θ < ε)
    (g : ∀ n, Geometry (dimension θ) n) :
    ∀ᶠ n : ℕ in atTop,
      uniformProb (fun y : Word (rowCount (dimension θ) n) =>
        rankTest θ (g n) y = true) ≤
          Real.exp (-(ε ^ 2 / 128) * rowCount (dimension θ) n) := by
  have hθrange : 0 < θ ∧ θ < 1/2 :=
    ⟨(half_pos hε.1).trans hθ.1, hθ.2.trans hε.2⟩
  have hsq : ε^2 ≤ 4*θ^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2*θ-ε by linarith [hθ.1])
      (show 0 ≤ 2*θ+ε by linarith [hθrange.1, hε.1])]
  filter_upwards [rankTest_distinguishing θ hθrange] with n hn
  apply ((hn (g n)).1).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)

end ExpandingCodes.PolynomialStretch
