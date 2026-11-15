import ExpandingCodes.Probability.PreliminaryExpansion
import ExpandingCodes.Probability.HashExpansion
import ExpandingCodes.Probability.GridBand

set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem eventProb_map {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : PMF Ω) (f : Ω → Ξ) (E : Ξ → Prop) :
    eventProb (P.map f) E = eventProb P (fun x => E (f x)) := by
  classical
  have hm (y : Ξ) : ((P.map f) y).toReal =
      ∑ x, if y = f x then (P x).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun x _ => by
      split_ifs
      · exact P.apply_ne_top x
      · simp)]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  unfold eventProb
  simp_rw [hm]
  have hi (y : Ξ) : (if E y then ∑ x, if y = f x then (P x).toReal else 0 else 0) =
      ∑ x, if y = f x then (if E (f x) then (P x).toReal else 0) else 0 := by
    by_cases hy : E y
    · rw [if_pos hy]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxy : y = f x
      · subst y
        simp [hy]
      · simp [hxy]
    · rw [if_neg hy]
      symm
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxy : y = f x
      · subst y
        simp [hy]
      · simp [hxy]
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem uniformProb_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) :
    uniformProb E + uniformProb (fun x => ¬ E x) = 1 := by
  classical
  rw [uniformProb_eq_uniformMean, uniformProb_eq_uniformMean, ← uniformMean_add]
  calc
    _ = uniformMean (fun _ : Ω => (1 : ℝ)) := by
      apply congrArg (uniformMean (Ω := Ω))
      funext x
      by_cases hx : E x <;> simp [hx]
    _ = 1 := uniformMean_const _

theorem uniformProb_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) :
    uniformProb E ≤ 1 := by
  have hh : uniformProb E ≤ uniformProb (fun _ : Ω => True) :=
    uniformProb_mono (E := E) (F := fun _ : Ω => True) (fun _ _ => trivial)
  simpa only [uniformProb_true] using hh

theorem uniformProb_prod_left {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (E : Ω × Ξ → Prop) :
    uniformProb E = uniformMean (fun x => uniformProb (fun y => E (x,y))) := by
  rw [← uniformProb_equiv (Equiv.prodComm Ξ Ω) E, uniformProb_prod]
  rfl

theorem uniformProb_conditional_bad_le {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (Good : Ω → Prop) (Bad : Ω × Ξ → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x, Good x → uniformProb (fun y => Bad (x,y)) ≤ δ) :
    uniformProb Bad ≤ uniformProb (fun x => ¬ Good x) + δ := by
  classical
  rw [uniformProb_prod_left]
  calc
    _ ≤ uniformMean (fun x => (if ¬ Good x then (1 : ℝ) else 0) + δ) := by
      apply uniformMean_mono
      intro x
      by_cases hx : Good x
      · simpa only [not_true_eq_false, if_false, zero_add, hx] using h x hx
      · simpa only [hx, not_false_eq_true, if_true] using
          (uniformProb_le_one (fun y => Bad (x,y))).trans (by linarith : (1 : ℝ) ≤ 1+δ)
    _ = _ := by
      rw [uniformMean_add, uniformMean_const, uniformProb_eq_uniformMean]
      congr 1
      apply congrArg (uniformMean (Ω := Ω))
      funext x
      by_cases hx : Good x <;> simp [hx]

theorem Expanding.mono {I J : Type*} [Fintype I] [Fintype J]
    {G : Matrix I J Bit} {k : ℕ} {γ γ' t t' : ℝ}
    (h : Expanding G γ k t) (hγ : γ' ≤ γ) (ht : t' ≤ t) :
    Expanding G γ' k t' := by
  classical
  rcases h with ⟨hw, he⟩
  refine ⟨hw, ?_⟩
  by_cases hc : Fintype.card I = 0
  · simp [hc]
  · simp only [if_neg hc] at he ⊢
    intro S hs
    have hcp : (0 : ℝ) < Fintype.card I := by exact_mod_cast (Nat.pos_of_ne_zero hc)
    rw [div_mul_cancel₀ _ hcp.ne'] at hs
    have hs' : (S.card : ℝ) ≤ t / Fintype.card I * Fintype.card I := by
      rw [div_mul_cancel₀ _ hcp.ne']
      exact hs.trans ht
    have hh := he S hs'
    simp only [sub_sub_cancel] at hh ⊢
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg k)) (Nat.cast_nonneg S.card)).trans hh

end ExpandingCodes.PolynomialStretch
