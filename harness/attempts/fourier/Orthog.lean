import ExpandingCodes.Probability.SharpThreshold.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul

set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]

/-- Bernoulli pattern weights factor into their one-coordinate weights. -/
lemma patternWeight_prod (p : ℝ) (E : Finset I) :
    patternWeight p E = ∏ i : I, if i ∈ E then p else 1-p := by
  classical
  simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter, patternWeight]
  congr 2
  have h : Finset.univ.filter (fun x => x ∉ E) = Eᶜ := by ext; simp
  rw [h, Finset.card_compl]

/-- Summing characters factors into independent one-coordinate kernels. -/
lemma character_kernel (p : ℝ) (E F : Finset I) :
    (∑ S : Finset I, character p S E * character p S F) =
      ∏ i : I, (1 + coordinate p i E * coordinate p i F) := by
  classical
  simp_rw [character, ← Finset.prod_mul_distrib]
  symm
  simpa using (Finset.prod_one_add (f := fun i => coordinate p i E * coordinate p i F) (Finset.univ : Finset I))

omit [Fintype I] in
/-- The weighted one-coordinate character kernel is the delta function. -/
lemma coordinate_kernel (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (i : I) (E F : Finset I) :
    (if i ∈ F then p else 1-p) *
      (1 + coordinate p i E * coordinate p i F) =
      if (i ∈ E ↔ i ∈ F) then 1 else 0 := by
  classical
  have h : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp')
  have hs : Real.sqrt (p * (1-p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
  have hsq := Real.sq_sqrt h.le
  unfold coordinate
  by_cases hiE : i ∈ E <;> by_cases hiF : i ∈ F <;>
    simp only [hiE, hiF, if_true, if_false, iff_true, iff_false, iff_self, not_true_eq_false, zero_sub] <;>
    field_simp [hs] <;> nlinarith [hsq, congrArg (fun t : ℝ => p * t) hsq]

/-- The weighted full character kernel is the delta function. -/
lemma weighted_character_kernel (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (E F : Finset I) :
    patternWeight p F * (∑ S : Finset I, character p S E * character p S F) =
      if E = F then 1 else 0 := by
  classical
  rw [character_kernel, patternWeight_prod, ← Finset.prod_mul_distrib]
  simp_rw [coordinate_kernel p hp hp']
  by_cases hEF : E = F
  · simp [hEF]
  · rw [if_neg hEF]
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => hEF (Finset.ext h))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Distinct biased characters are orthogonal and every character has norm one. -/
lemma character_orthogonality (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (S T : Finset I) :
    expectation p (fun E => character p S E * character p T E) =
      if S = T then 1 else 0 := by
  classical
  let M : Matrix (Finset I) (Finset I) ℝ := fun E S => character p S E
  let N : Matrix (Finset I) (Finset I) ℝ :=
    fun S E => patternWeight p E * character p S E
  have hMN : M * N = 1 := by
    ext E F
    change (∑ S : Finset I, character p S E *
      (patternWeight p F * character p S F)) = if E = F then 1 else 0
    rw [← weighted_character_kernel p hp hp' E F, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  have hNM : N * M = 1 := mul_eq_one_comm.mp hMN
  have h := congrArg (fun A : Matrix (Finset I) (Finset I) ℝ => A S T) hNM
  change (∑ E : Finset I, patternWeight p E * character p S E *
      character p T E) = if S = T then 1 else 0 at h
  simpa only [expectation, mul_assoc] using h

/-- Every Boolean function has its finite biased Fourier expansion. -/
lemma fourier_inversion (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (E : Finset I) :
    (∑ S : Finset I, fourier p f S * character p S E) = f E := by
  classical
  calc
    _ = ∑ F : Finset I, f F * (patternWeight p F *
        ∑ S : Finset I, character p S E * character p S F) := by
      unfold fourier expectation
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro F _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ∑ F : Finset I, if E = F then f F else 0 := by
      apply Finset.sum_congr rfl
      intro F _
      rw [weighted_character_kernel p hp hp']
      split_ifs <;> simp
    _ = f E := by simp

/-- Bilinear Parseval for the explicitly defined biased Fourier coefficients. -/
lemma fourier_inner_product (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f g : Finset I → ℝ) :
    expectation p (fun E => f E * g E) =
      ∑ S : Finset I, fourier p f S * fourier p g S := by
  classical
  symm
  calc
    _ = ∑ E : Finset I, patternWeight p E * f E *
        (∑ S : Finset I, fourier p g S * character p S E) := by
      change (∑ S : Finset I,
        (∑ E : Finset I, patternWeight p E * (f E * character p S E)) *
          fourier p g S) = _
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = expectation p (fun E => f E * g E) := by
      simp_rw [fourier_inversion p hp hp']
      unfold expectation
      apply Finset.sum_congr rfl
      intro E _
      ring

@[simp] lemma fourier_empty (p : ℝ) (f : Finset I → ℝ) :
    fourier p f ∅ = expectation p f := by
  simp [fourier, character]

/-- The variance is the sum of squares of all nonconstant Fourier coefficients. -/
theorem fourier_parseval (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) :
    variance p f = ∑ S : Finset I, if S.Nonempty then fourier p f S ^ 2 else 0 := by
  classical
  have hfull : expectation p (fun E => f E ^ 2) =
      ∑ S : Finset I, fourier p f S ^ 2 := by
    simpa only [pow_two] using fourier_inner_product p hp hp' f f
  have hsplit : (∑ S : Finset I, fourier p f S ^ 2) =
      (∑ S : Finset I, if S.Nonempty then fourier p f S ^ 2 else 0) +
        (expectation p f) ^ 2 := by
    rw [← fourier_empty p f]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset I))]
    congr 1
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext S
      simp [Finset.nonempty_iff_ne_empty]
    · intro S _
      rfl
  unfold variance
  rw [hfull, hsplit]
  ring
end ExpandingCodes.SharpThreshold
