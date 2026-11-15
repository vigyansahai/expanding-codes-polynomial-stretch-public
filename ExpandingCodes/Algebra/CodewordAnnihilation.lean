import ExpandingCodes.Algebra.CombinedOrthogonality
import ExpandingCodes.Construction.ParameterBounds

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter
/-- Lemma 2.2, with the standing sufficiently-large-n convention of §2. -/
theorem codeword_annihilation (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ (g : Geometry (dimension ε) n)
      (s : Forms g.F (dimension ε) (arity ε))
      (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n),
      testMatrix g ((combined g s h).mulVec x) = 0 ∧
      ∀ e : Word (rowCount (dimension ε) n),
        (testMatrix g ((combined g s h).mulVec x + e)).rank ≤ weight e := by
  apply Filter.Eventually.of_forall
  intro n g s h x
  have hd : 4 ≤ dimension ε := dimension_ge_four ε hε
  have hb : 0 < buckets ε n := by
    unfold buckets
    exact pow_pos (by decide) _
  exact ⟨testMatrix_combined_mulVec_eq_zero g s h x hd hb,
    fun e => testMatrix_combined_corruption_rank_le_weight g s h x e hd hb⟩

end ExpandingCodes.PolynomialStretch
