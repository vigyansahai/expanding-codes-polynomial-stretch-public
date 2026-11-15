import ExpandingCodes.Probability.GridBand
import ExpandingCodes.Probability.RateLimit

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_or_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E F : Ω → Prop) :
    uniformProb (fun x => E x ∨ F x) ≤ uniformProb E + uniformProb F := by
  classical
  rw [uniformProb_eq_uniformMean, uniformProb_eq_uniformMean,
    uniformProb_eq_uniformMean, ← uniformMean_add]
  apply uniformMean_mono
  intro x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf]

noncomputable def gridReflect (d q : ℕ) : Equiv.Perm (Fin d → Fin q) :=
  Equiv.piCongrRight (fun _ => Fin.revPerm)

theorem gridReflect_sum (d q : ℕ) (v : Fin d → Fin q) :
    (∑ i, (((gridReflect d q v) i).val : ℝ)) + (∑ i, ((v i).val : ℝ)) =
      (d : ℝ) * (q - 1 : ℕ) := by
  classical
  rw [← Finset.sum_add_distrib]
  have hc (i : Fin d) : (((gridReflect d q v) i).val : ℝ) + ((v i).val : ℝ) =
      (q - 1 : ℕ) := by
    have hv := (v i).isLt
    have hh : (Fin.rev (v i)).val + (v i).val = q - 1 := by
      rw [Fin.val_rev]
      omega
    exact_mod_cast hh
  simp_rw [hc]
  simp

theorem grid_median_prob_ge_half (s q : ℕ) [NeZero q] :
    1 / 2 ≤ uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      (∑ i, ((v i).val : ℝ)) ≤ (s * (2*q-1) : ℕ)) := by
  classical
  let D : ℝ := (s * (2*q-1) : ℕ)
  let E : (Fin (2*s) → Fin (2*q)) → Prop := fun v => (∑ i, ((v i).val : ℝ)) ≤ D
  let F : (Fin (2*s) → Fin (2*q)) → Prop := fun v => D ≤ ∑ i, ((v i).val : ℝ)
  have heq : uniformProb E = uniformProb F := by
    rw [← uniformProb_equiv (gridReflect (2*s) (2*q)) E]
    apply uniformProb_congr
    intro v
    have hh := gridReflect_sum (2*s) (2*q) v
    have hd : ((2*s : ℕ) : ℝ) * (2*q-1 : ℕ) = 2*D := by
      dsimp [D]
      push_cast
      ring
    rw [hd] at hh
    dsimp [E, F]
    constructor <;> intro h <;> linarith
  have hu : uniformProb (fun v => E v ∨ F v) = 1 := by
    have hh : (fun v => E v ∨ F v) = (fun _ => True) := by
      funext v
      apply propext
      exact iff_true_intro (le_total _ _)
    rw [hh, uniformProb_true]
  have hb := uniformProb_or_le E F
  rw [hu] at hb
  change 1 / 2 ≤ uniformProb E
  linarith

/-- For even dimension and alphabet, the exact floor leaves a band shorter
than three half-alphabet steps below the discrete median. -/
theorem auxiliaryDegree_even_band (s q : ℕ) (hs : 2 ≤ s) (hq : 1 ≤ q) :
    ((s * (2*q-1) : ℕ) : ℝ) - auxiliaryDegree (2*q) (2*s) ≤ 3 * (q : ℝ) := by
  have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hp : 0 ≤ ((2*(s : ℤ)-3) * q - s + 1) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ s-2 by omega)
      (show (0 : ℤ) ≤ q-1 by omega)]
  have he : auxiliaryDegree (2*q) (2*s) =
      ((2*(s : ℤ)-3) * q - s + 1).toNat := by
    unfold auxiliaryDegree
    push_cast
    congr 1
    have hh : ((2*(s : ℤ)-3) * (2*(q : ℤ)-1) - 1) =
        2 * ((2*(s : ℤ)-3) * q - s + 1) := by ring
    rw [hh, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
  have hc : (auxiliaryDegree (2*q) (2*s) : ℤ) =
      (2*(s : ℤ)-3) * q - s + 1 := by rw [he, Int.toNat_of_nonneg hp]
  have hsub : ((2*q-1 : ℕ) : ℤ) = 2*(q : ℤ)-1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hb : ((s*(2*q-1) : ℕ) : ℤ) - auxiliaryDegree (2*q) (2*s) ≤ 3*q := by
    rw [Nat.cast_mul, hsub, hc]
    nlinarith
  exact_mod_cast hb

theorem auxiliary_grid_rate_ge (s q : ℕ) [NeZero q] (hs : 2 ≤ s) :
    1 / 2 - 4 / Real.sqrt (2*s+1) ≤
      (Fintype.card (GridIndices (2*q) (2*s) (auxiliaryDegree (2*q) (2*s))) : ℝ) /
        ((2*q : ℕ) : ℝ) ^ (2*s) := by
  classical
  let R := auxiliaryDegree (2*q) (2*s)
  let D := s * (2*q-1)
  let E : (Fin (2*s) → Fin (2*q)) → Prop := fun v => (∑ i, (v i).val) ≤ R
  let F : (Fin (2*s) → Fin (2*q)) → Prop := fun v =>
    (R : ℝ) ≤ ∑ i, ((v i).val : ℝ) ∧ (∑ i, ((v i).val : ℝ)) ≤ D
  have hband : uniformProb F ≤ 4 / Real.sqrt (2*s+1) :=
    gridBand_prob_le s q (NeZero.pos q) R D
      (auxiliaryDegree_even_band s q hs (NeZero.pos q))
  have hmid : 1 / 2 ≤ uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      (∑ i, ((v i).val : ℝ)) ≤ (D : ℝ)) := grid_median_prob_ge_half s q
  have hsub : uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      (∑ i, ((v i).val : ℝ)) ≤ (D : ℝ)) ≤ uniformProb E + uniformProb F := by
    apply (uniformProb_mono (F := fun v => E v ∨ F v) ?_).trans (uniformProb_or_le E F)
    intro v hv
    by_cases he : E v
    · exact Or.inl he
    · right
      dsimp [E] at he
      have hh : (R : ℝ) ≤ ∑ i, ((v i).val : ℝ) := by
        have hn : R ≤ ∑ i, (v i).val := by omega
        exact_mod_cast hn
      exact ⟨hh, hv⟩
  have he : uniformProb E =
      (Fintype.card (GridIndices (2*q) (2*s) R) : ℝ) / ((2*q : ℕ) : ℝ) ^ (2*s) := by
    rw [uniformProb_eq_card_subtype]
    simp only [GridIndices, E, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    congr 1
    norm_cast
    congr 1
    exact Subsingleton.elim _ _
  rw [he] at hsub
  dsimp only [R] at hsub
  linarith

end ExpandingCodes.PolynomialStretch
