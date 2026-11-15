import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory

namespace ExpandingCodes.PolynomialStretch

/-- Hoeffding's scalar Bernoulli bound, isolated from the detector. -/
theorem bernoulli_two_point_mgf_le (p s : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1-p)*Real.exp (-s*p) + p*Real.exp (s*(1-p)) ≤ Real.exp (s^2/8) := by
  let q : unitInterval := ⟨p, hp, hp'⟩
  let μ := ProbabilityTheory.bernoulliMeasure true false q
  let X : Bool → ℝ := fun b => if b then 1-p else -p
  have hm : AEMeasurable X μ := (measurable_of_countable X).aemeasurable
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc (-p) (1-p) := by
    apply Filter.Eventually.of_forall
    intro b
    cases b <;> dsimp [X] <;> constructor <;> linarith
  have hc : ∫ b, X b ∂μ = 0 := by
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    dsimp [X, q]
    simp only [smul_eq_mul]
    ring
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).mgf_le s
  have hw : (1-p)-(-p) = 1 := by ring
  rw [hw] at h
  simpa [ProbabilityTheory.mgf, μ, ProbabilityTheory.integral_bernoulliMeasure,
    X, q, smul_eq_mul, mul_neg, div_eq_mul_inv, add_comm] using h

end ExpandingCodes.PolynomialStretch
