import ExpandingCodes.Algebra.CodewordAnnihilation
import ExpandingCodes.Construction.SamplerSupport

set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem adversarial_rankTest_acceptance (ε θ : ℝ)
    (hθ : 0 < θ ∧ θ < 1 / 2) (hθε : θ ≤ 2 * ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (g : Geometry (dimension θ) n)
      (G : Generator (rowCount (dimension θ) n) n), sampleLaw θ n g G ≠ 0 →
      ∀ (x : Word n) (e : Word (rowCount (dimension θ) n)),
        (weight e : ℝ) ≤ (1 / 2 - ε) * rowCount (dimension θ) n →
          rankTest θ g (G.mulVec x + e) = true := by
  filter_upwards [codeword_annihilation θ hθ] with n hn
  intro g G hG x e he
  obtain ⟨s, h, rfl⟩ := (sampleLaw_ne_zero_iff θ n g G).mp hG
  have hr : ((testMatrix g ((combined g s h).mulVec x + e)).rank : ℝ) ≤ weight e := by
    exact_mod_cast (hn g s h x).2 e
  have hm : (0 : ℝ) ≤ rowCount (dimension θ) n := Nat.cast_nonneg _
  have ht : (1 / 2 - ε) * (rowCount (dimension θ) n : ℝ) ≤
      (1 / 2 - θ / 2) * rowCount (dimension θ) n := by
    exact mul_le_mul_of_nonneg_right (by linarith) hm
  simp only [rankTest, decide_eq_true_eq]
  exact hr.trans (he.trans ht)

end ExpandingCodes.PolynomialStretch
