import ExpandingCodes.Probability.BinomialInterval
import ExpandingCodes.Probability.BoundedDifferences

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_prod (α β : Type*) [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α × β → Prop) :
    uniformProb E = uniformMean (fun b => uniformProb (fun a => E (a, b))) := by
  classical
  simp_rw [uniformProb_eq_uniformMean]
  unfold uniformMean
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div]
  ring

noncomputable def gridBitEquiv (d q : ℕ) :
    ((Fin d → Bool) × (Fin d → Fin q)) ≃ (Fin d → Fin (2 * q)) :=
  (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => Bool) (fun _ => Fin q)).symm.trans
    (Equiv.piCongrRight (fun _ =>
      (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin q))).trans finProdFinEquiv))

theorem gridBitEquiv_sum (d q : ℕ) (x : Fin d → Bool) (z : Fin d → Fin q) :
    (∑ i, ((gridBitEquiv d q (x,z) i).val : ℝ)) =
      (q : ℝ) * (trueSet x).card + ∑ i, ((z i).val : ℝ) := by
  classical
  have he (i : Fin d) : ((gridBitEquiv d q (x,z) i).val : ℝ) =
      ((z i).val : ℝ) + (q : ℝ) * (if x i then 1 else 0) := by
    cases hx : x i <;> simp [gridBitEquiv, finProdFinEquiv, finTwoEquiv, hx]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc : (∑ i : Fin d, if x i then (1 : ℝ) else 0) = (trueSet x).card := by
    simp [trueSet, Finset.sum_boole]
  rw [hc]
  ring

theorem gridBand_prob_le (s q : ℕ) [NeZero q] (hq : 0 < q) (A D : ℝ) (hAD : D - A ≤ 3 * q) :
    uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      A ≤ ∑ i, ((v i).val : ℝ) ∧ (∑ i, ((v i).val : ℝ)) ≤ D) ≤
        4 / Real.sqrt (2 * s + 1) := by
  classical
  let E : (Fin (2*s) → Fin (2*q)) → Prop := fun v =>
    A ≤ ∑ i, ((v i).val : ℝ) ∧ (∑ i, ((v i).val : ℝ)) ≤ D
  change uniformProb E ≤ _
  rw [← uniformProb_equiv (gridBitEquiv (2*s) q) E,
    uniformProb_prod]
  apply (uniformMean_mono (fun z => ?_)).trans_eq (uniformMean_const _)
  let a := (A - ∑ i, ((z i).val : ℝ)) / (q : ℝ)
  calc
    uniformProb (fun x => E (gridBitEquiv (2*s) q (x,z))) ≤
        uniformProb (fun x : Fin (2*s) → Bool =>
          a ≤ ((trueSet x).card : ℝ) ∧ ((trueSet x).card : ℝ) ≤ a + 3) := by
      apply uniformProb_mono
      intro x hx
      change A ≤ ∑ i, ((gridBitEquiv (2*s) q (x,z) i).val : ℝ) ∧
        (∑ i, ((gridBitEquiv (2*s) q (x,z) i).val : ℝ)) ≤ D at hx
      rw [gridBitEquiv_sum] at hx
      have hqp : (0 : ℝ) < q := by exact_mod_cast hq
      constructor
      · apply (div_le_iff₀ hqp).2
        nlinarith
      · have hh : ((trueSet x).card : ℝ) - 3 ≤
            (A - ∑ i, ((z i).val : ℝ)) / (q : ℝ) := by
          apply (le_div_iff₀ hqp).2
          nlinarith
        dsimp [a]
        linarith
    _ ≤ _ := uniformProb_trueSet_interval_le s a

end ExpandingCodes.PolynomialStretch
