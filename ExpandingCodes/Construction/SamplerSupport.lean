import ExpandingCodes.Construction.RowWeight
import ExpandingCodes.Construction.ParameterBounds

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

/-- Every choice of forms and hashes has positive sampling mass, and these are
exactly the matrices in the support of the canonical law. -/
theorem sampleLaw_ne_zero_iff (ε : ℝ) (n : ℕ) (g : Geometry (dimension ε) n)
    (G : Generator (rowCount (dimension ε) n) n) :
    sampleLaw ε n g G ≠ 0 ↔
      ∃ (s : Forms g.F (dimension ε) (arity ε))
        (h : Hashes g.F (arity ε) (buckets ε n)), combined g s h = G := by
  classical
  change G ∈ (sampleLaw ε n g).support ↔ _
  simp only [sampleLaw, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨⟨s, h⟩, _, heq⟩
    exact ⟨s, h, heq⟩
  · rintro ⟨s, h, heq⟩
    exact ⟨(s, h), PMF.mem_support_uniformOfFintype _, heq⟩

/-- The rounded-down power-of-two bucket count is always positive. -/
theorem sampler_buckets_pos (ε : ℝ) (n : ℕ) : 0 < buckets ε n := by
  unfold buckets
  exact pow_pos (by decide) _

/-- All layer blocks fit once there are at least as many columns as layers. -/
theorem arity_mul_buckets_le (ε : ℝ) (n : ℕ)
    (hk : 0 < arity ε) (hn : arity ε ≤ n) : arity ε * buckets ε n ≤ n := by
  have hdiv : n / arity ε ≠ 0 := Nat.ne_of_gt ((Nat.one_le_div_iff hk).2 hn)
  unfold buckets
  exact (Nat.mul_le_mul_left (arity ε) (Nat.pow_log_le_self 2 hdiv)).trans
    (by simpa [Nat.mul_comm] using Nat.div_mul_le_self n (arity ε))

private theorem sampler_arity_pos (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    0 < arity ε := by
  have hd : (0 : ℝ) < dimension ε := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four ε hε)
  have he : 0 < ε := hε.1
  unfold arity
  apply Nat.ceil_pos.2
  positivity

/-- Every actual sampler output has exact row weight at all sufficiently large sizes. -/
theorem sampleLaw_output_rowWeight (ε : ℝ) (n : ℕ)
    (hε : 0 < ε ∧ ε < 1 / 2) (hn : arity ε ≤ n)
    (g : Geometry (dimension ε) n)
    (G : Generator (rowCount (dimension ε) n) n)
    (hG : sampleLaw ε n g G ≠ 0) : RowWeight G (arity ε) := by
  obtain ⟨s, h, rfl⟩ := (sampleLaw_ne_zero_iff ε n g G).1 hG
  exact combined_rowWeight g s h (sampler_buckets_pos ε n)
    (arity_mul_buckets_le ε n (sampler_arity_pos ε hε) hn)

/-- The support conclusion is uniform over geometry and every matrix in the law. -/
theorem eventual_sampleLaw_rowWeight (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (g : Geometry (dimension ε) n)
      (G : Generator (rowCount (dimension ε) n) n),
      sampleLaw ε n g G ≠ 0 → RowWeight G (arity ε) := by
  filter_upwards [Filter.eventually_ge_atTop (arity ε)] with n hn
  intro g G hG
  exact sampleLaw_output_rowWeight ε n hε hn g G hG

end ExpandingCodes.PolynomialStretch
