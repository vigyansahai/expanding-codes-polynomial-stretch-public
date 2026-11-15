import ExpandingCodes.Probability.BinomialAtom
import ExpandingCodes.Probability.FiniteEvents

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

noncomputable def trueSet {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i = true)

noncomputable def boolFinsetEquiv (d : ℕ) : (Fin d → Bool) ≃ Finset (Fin d) where
  toFun := trueSet
  invFun S i := decide (i ∈ S)
  left_inv x := by
    funext i
    simp [trueSet]
  right_inv S := by
    ext i
    simp [trueSet]

theorem card_trueSet_eq (d j : ℕ) [Fintype {x : Fin d → Bool // (trueSet x).card = j}] :
    Fintype.card {x : Fin d → Bool // (trueSet x).card = j} = d.choose j := by
  classical
  let e : {x : Fin d → Bool // (trueSet x).card = j} ≃
      {S : Finset (Fin d) // S.card = j} :=
    (boolFinsetEquiv d).subtypeEquiv (fun _ => Iff.rfl)
  have h := Fintype.card_congr e
  simpa only [Fintype.card_finset_len, Fintype.card_fin] using h

theorem uniformProb_trueSet_card_le (s j : ℕ) :
    uniformProb (fun x : Fin (2*s) → Bool => (trueSet x).card = j) ≤
      1 / Real.sqrt (2 * s + 1) := by
  rw [uniformProb_eq_card_subtype, card_trueSet_eq]
  have he : Fintype.card (Fin (2*s) → Bool) = 4 ^ s := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [pow_mul]
    rfl
  rw [he, Nat.cast_pow, Nat.cast_ofNat]
  exact binomial_atom_le s j

theorem uniformProb_trueSet_interval_le (s : ℕ) (a : ℝ) :
    uniformProb (fun x : Fin (2*s) → Bool =>
      a ≤ ((trueSet x).card : ℝ) ∧ ((trueSet x).card : ℝ) ≤ a + 3) ≤
        4 / Real.sqrt (2 * s + 1) := by
  classical
  let T := Finset.Icc ⌈a⌉₊ (⌈a⌉₊ + 3)
  have hin (x : Fin (2*s) → Bool)
      (hx : a ≤ ((trueSet x).card : ℝ) ∧ ((trueSet x).card : ℝ) ≤ a + 3) :
      (trueSet x).card ∈ T := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Nat.ceil_le).2 hx.1
    · have h : ((trueSet x).card : ℝ) ≤ (⌈a⌉₊ : ℝ) + 3 := by
        linarith [Nat.le_ceil a]
      exact_mod_cast h
  calc
    _ ≤ uniformProb (fun x : Fin (2*s) → Bool => ∃ j ∈ T, (trueSet x).card = j) :=
      uniformProb_mono (fun x hx => ⟨_, hin x hx, rfl⟩)
    _ ≤ ∑ j ∈ T, uniformProb (fun x : Fin (2*s) → Bool => (trueSet x).card = j) :=
      uniformProb_exists_finset T _
    _ ≤ ∑ _j ∈ T, 1 / Real.sqrt (2 * s + 1) :=
      Finset.sum_le_sum (fun j _ => uniformProb_trueSet_card_le s j)
    _ = _ := by
      have hc : T.card = 4 := by simp only [T, Nat.card_Icc]; omega
      simp [hc]
      ring

end ExpandingCodes.PolynomialStretch
