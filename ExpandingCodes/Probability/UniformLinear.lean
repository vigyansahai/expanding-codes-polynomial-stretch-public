import ExpandingCodes.Probability.FiniteUniform
import Definitions.Def_ExpandingCodes_PolynomialStretch_Sampler

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_sum_mul_eq {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F]
    (z : I → F) (hz : z ≠ 0) (y : F) :
    uniformProb (fun a : I → F => ∑ i, a i * z i = y) =
      1 / (Fintype.card F : ℝ) := by
  classical
  let f : (I → F) →+ F :=
    { toFun := fun a => ∑ i, a i * z i
      map_zero' := by simp
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib] }
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    simpa only [ne_eq, funext_iff, not_forall, Pi.zero_apply] using hz
  have hf : Function.Surjective f := by
    intro t
    refine ⟨Pi.single j (t / z j), ?_⟩
    simp [f, Pi.single_apply, ite_mul, hj]
  exact uniformProb_addHom_eq f hf y

theorem uniformProb_sum_mul_collision {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F]
    (z z' : I → F) (hne : z ≠ z') :
    uniformProb (fun a : I → F => ∑ i, a i * z i = ∑ i, a i * z' i) =
      1 / (Fintype.card F : ℝ) := by
  have hz : z - z' ≠ 0 := sub_ne_zero.mpr hne
  calc
    _ = uniformProb (fun a : I → F => ∑ i, a i * (z - z') i = 0) := by
      apply uniformProb_congr
      intro a
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
    _ = _ := uniformProb_sum_mul_eq (z - z') hz 0

theorem uniformProb_linearForm_collision {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (z z' : Fin d → F) (hne : z ≠ z') :
    uniformProb (fun a : Fin d → F => linearForm a z = linearForm a z') =
      1 / (Fintype.card F : ℝ) := by
  simpa only [linearForm] using uniformProb_sum_mul_collision z z' hne

theorem uniformProb_two_linearForm_collision {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (z z' : Fin d → F) (hne : z ≠ z') :
    uniformProb (fun a : Fin 2 → Fin d → F =>
      linearForm (a 0) z = linearForm (a 0) z' ∧
      linearForm (a 1) z = linearForm (a 1) z') =
      1 / (Fintype.card F : ℝ) ^ 2 := by
  have hp := uniformProb_pi (fun _ : Fin 2 =>
    fun a : Fin d → F => linearForm a z = linearForm a z')
  have he : (fun a : Fin 2 → Fin d → F =>
      ∀ j, linearForm (a j) z = linearForm (a j) z') =
      (fun a => linearForm (a 0) z = linearForm (a 0) z' ∧
        linearForm (a 1) z = linearForm (a 1) z') := by
    funext a
    simp only [Fin.forall_fin_two]
  rw [he] at hp
  calc
    _ = ∏ _j : Fin 2, uniformProb (fun a : Fin d → F =>
        linearForm a z = linearForm a z') := by
      exact hp
    _ = _ := by
      simp [uniformProb_linearForm_collision z z' hne, pow_two]

/-- Re-index the exact canonical sampler forms by independent layer/level pairs. -/
def formsPairEquiv (F : Type*) (d k : ℕ) :
    Forms F d k ≃ ((Fin k × F) → Fin 2 → Fin d → F) where
  toFun s p j := s j p.1 p.2
  invFun s j i a := s (i, a) j
  left_inv _ := rfl
  right_inv _ := rfl

theorem uniformProb_forms_events {F : Type*} [Field F] [Fintype F]
    {d k : ℕ} (A : Finset (Fin k × F))
    (E : (Fin k × F) → (Fin 2 → Fin d → F) → Prop) :
    uniformProb (fun s : Forms F d k =>
      ∀ p ∈ A, E p (fun j => s j p.1 p.2)) =
      ∏ p ∈ A, uniformProb (E p) := by
  rw [← uniformProb_pi_finset A E]
  exact uniformProb_equiv (formsPairEquiv F d k)
    (fun s => ∀ p ∈ A, E p (s p))

theorem uniformProb_forms_collisions {F : Type*} [Field F] [Fintype F]
    {d k : ℕ} (A : Finset (Fin k × F)) (z z' : (Fin k × F) → Fin d → F)
    (hne : ∀ p ∈ A, z p ≠ z' p) :
    uniformProb (fun s : Forms F d k => ∀ p ∈ A,
      linearForm (s 0 p.1 p.2) (z p) = linearForm (s 0 p.1 p.2) (z' p) ∧
      linearForm (s 1 p.1 p.2) (z p) = linearForm (s 1 p.1 p.2) (z' p)) =
      (1 / (Fintype.card F : ℝ) ^ 2) ^ A.card := by
  rw [uniformProb_forms_events A (fun p a =>
    linearForm (a 0) (z p) = linearForm (a 0) (z' p) ∧
    linearForm (a 1) (z p) = linearForm (a 1) (z' p))]
  calc
    _ = ∏ _p ∈ A, 1 / (Fintype.card F : ℝ) ^ 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      exact uniformProb_two_linearForm_collision (z p) (z' p) (hne p hp)
    _ = _ := by simp

end ExpandingCodes.PolynomialStretch
