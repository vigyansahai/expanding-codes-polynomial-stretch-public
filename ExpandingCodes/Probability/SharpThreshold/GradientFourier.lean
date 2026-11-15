import ExpandingCodes.Probability.SharpThreshold.FourierBasis

/-! Finite coordinate-gradient and noise identities in the explicit biased Fourier basis. -/

set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma character_insert_of_not_mem (p : ℝ) {i : I} {S : Finset I} (hi : i ∉ S)
    (E : Finset I) : character p S (insert i E) = character p S E := by
  classical
  unfold character
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [coordinate, hji]

omit [Fintype I] in
lemma character_erase_of_not_mem (p : ℝ) {i : I} {S : Finset I} (hi : i ∉ S)
    (E : Finset I) : character p S (E.erase i) = character p S E := by
  classical
  unfold character
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [coordinate, hji]

omit [Fintype I] in
lemma gradient_character (p : ℝ) (i : I) (S E : Finset I) :
    gradient i (character p S) E =
      if i ∈ S then character p (S.erase i) E / Real.sqrt (p * (1-p)) else 0 := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hc (F : Finset I) : character p S F =
        coordinate p i F * character p (S.erase i) F :=
      (Finset.mul_prod_erase S (fun j => coordinate p j F) hi).symm
    simp only [gradient, hc, character_insert_of_not_mem p (Finset.notMem_erase i S),
      character_erase_of_not_mem p (Finset.notMem_erase i S)]
    simp only [coordinate, Finset.mem_insert_self, Finset.notMem_erase, if_true, if_false]
    ring
  · simp [hi, gradient, character_insert_of_not_mem p hi, character_erase_of_not_mem p hi]

lemma fourier_gradient_sum (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (i : I) (T : Finset I) :
    fourier p (gradient i f) T =
      ∑ S : Finset I, if i ∈ S ∧ S.erase i = T then
        fourier p f S / Real.sqrt (p * (1-p)) else 0 := by
  classical
  have hexpand (E : Finset I) : gradient i f E =
      ∑ S : Finset I, fourier p f S * gradient i (character p S) E := by
    unfold gradient
    rw [← fourier_inversion p hp hp' f (insert i E),
      ← fourier_inversion p hp hp' f (E.erase i), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    ring
  calc
    _ = ∑ S : Finset I, fourier p f S *
        expectation p (fun E => gradient i (character p S) E * character p T E) := by
      change expectation p (fun E => gradient i f E * character p T E) = _
      simp_rw [hexpand, Finset.sum_mul]
      rw [expectation_sum]
      unfold expectation
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hi : i ∈ S
      · simp only [gradient_character, if_pos hi]
        have hfactor : expectation p
            (fun E => character p (S.erase i) E / Real.sqrt (p * (1-p)) * character p T E) =
            expectation p (fun E => character p (S.erase i) E * character p T E) /
              Real.sqrt (p * (1-p)) := by
          unfold expectation
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro E _
          ring
        rw [hfactor, character_orthogonality p hp hp']
        by_cases hST : S.erase i = T <;> simp [hi, hST, div_eq_mul_inv]
      · simp [gradient_character, hi]

lemma fourier_gradient (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (i : I) (T : Finset I) :
    fourier p (gradient i f) T =
      if i ∈ T then 0 else fourier p f (insert i T) / Real.sqrt (p * (1-p)) := by
  classical
  rw [fourier_gradient_sum p hp hp']
  by_cases hi : i ∈ T
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro S _
    have hST : ¬ (i ∈ S ∧ S.erase i = T) := by
      rintro ⟨_, h⟩
      exact Finset.notMem_erase i S (h.symm ▸ hi)
    simp [hST]
  · rw [if_neg hi]
    rw [Finset.sum_eq_single (insert i T)]
    · simp [Finset.erase_insert hi]
    · intro S _ hS
      have hST : ¬ (i ∈ S ∧ S.erase i = T) := by
        rintro ⟨hiS, h⟩
        exact hS (by rw [← h, Finset.insert_erase hiS])
      simp [hST]
    · simp


/-- Fourier multipliers are diagonal in the finite character basis. -/
lemma fourier_noise (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (T : Finset I) :
    fourier p (noise p r f) T = r ^ T.card * fourier p f T := by
  classical
  calc
    _ = ∑ S : Finset I, (r ^ S.card * fourier p f S) *
        expectation p (fun E => character p S E * character p T E) := by
      change expectation p (fun E => noise p r f E * character p T E) = _
      simp only [noise, Finset.sum_mul]
      rw [expectation_sum]
      unfold expectation
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := by
      simp_rw [character_orthogonality p hp hp']
      simp

/-- Adding a missing coordinate bijects subsets missing it with subsets containing it. -/
lemma sum_insert_not_mem (i : I) (a : Finset I → ℝ) :
    (∑ T : Finset I, if i ∉ T then a (insert i T) else 0) =
      ∑ S : Finset I, if i ∈ S then a S else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun T _ => insert i T)
  · intro T _
    simp
  · intro T hT U hU h
    have hiT : i ∉ T := (Finset.mem_filter.mp hT).2
    have hiU : i ∉ U := (Finset.mem_filter.mp hU).2
    simpa [Finset.erase_insert hiT, Finset.erase_insert hiU] using
      congrArg (fun S : Finset I => S.erase i) h
  · intro S hS
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
    exact ⟨S.erase i, by simp, Finset.insert_erase hiS⟩
  · intro T _
    rfl

/-- Weighted Parseval of coordinate gradients, before summing incidences. -/
lemma fourier_gradient_weighted (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (w : ℕ → ℝ) (i : I) :
    p * (1-p) * (∑ T : Finset I, w T.card * fourier p (gradient i f) T ^ 2) =
      ∑ S : Finset I, if i ∈ S then w (S.card-1) * fourier p f S ^ 2 else 0 := by
  classical
  have hv : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp')
  calc
    _ = ∑ T : Finset I, if i ∉ T then
        w T.card * fourier p f (insert i T) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [fourier_gradient p hp hp']
      by_cases hi : i ∈ T
      · simp [hi]
      · simp only [hi, if_false, not_false_eq_true, if_true, div_pow,
          Real.sq_sqrt hv.le]
        field_simp [hp.ne', (sub_pos.mpr hp').ne']
    _ = ∑ T : Finset I, if i ∉ T then
        w ((insert i T).card-1) * fourier p f (insert i T) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hi : i ∈ T
      · simp [hi]
      · simp [hi, Finset.card_insert_of_notMem hi]
    _ = _ := sum_insert_not_mem i (fun S => w (S.card-1) * fourier p f S ^ 2)

/-- Each Fourier support contributes once for each of its coordinates. -/
lemma sum_fourier_gradient_weighted (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (w : ℕ → ℝ) :
    p * (1-p) * (∑ i : I, ∑ T : Finset I, w T.card * fourier p (gradient i f) T ^ 2) =
      ∑ S : Finset I, (S.card : ℝ) * w (S.card-1) * fourier p f S ^ 2 := by
  classical
  rw [Finset.mul_sum]
  simp_rw [fourier_gradient_weighted p hp hp' f w]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.sum_filter]
  simp [mul_assoc]

end ExpandingCodes.SharpThreshold
