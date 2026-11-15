import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryModel

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_eq_card_filter {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    uniformProb E = ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  classical
  simp [uniformProb, eventProb, ← Finset.sum_filter, div_eq_mul_inv]

theorem uniformProb_eq_card_subtype {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    uniformProb E = (Fintype.card {ω // E ω} : ℝ) / Fintype.card Ω := by
  classical
  rw [uniformProb_eq_card_filter]
  simp only [Fintype.card_subtype]

theorem uniformProb_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (e : Ω ≃ Ξ) (E : Ξ → Prop) :
    uniformProb (fun ω => E (e ω)) = uniformProb E := by
  classical
  rw [uniformProb_eq_card_subtype, uniformProb_eq_card_subtype]
  have ec : {ω // E (e ω)} ≃ {ξ // E ξ} :=
    { toFun := fun ω => ⟨e ω.val, ω.property⟩
      invFun := fun ξ => ⟨e.symm ξ.val, by simpa using ξ.property⟩
      left_inv := fun ω => by ext; simp
      right_inv := fun ξ => by ext; simp }
  rw [Fintype.card_congr ec, Fintype.card_congr e]

theorem uniformProb_congr {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {E D : Ω → Prop} (h : ∀ ω, E ω ↔ D ω) : uniformProb E = uniformProb D := by
  congr 1
  funext ω
  exact propext (h ω)

theorem uniformProb_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProb (fun _ : Ω => True) = 1 := by
  rw [uniformProb_eq_card_filter]
  simp [Fintype.card_ne_zero]

theorem uniformProb_pi {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (E : ∀ i, Ω i → Prop) :
    uniformProb (fun ω : ∀ i, Ω i => ∀ i, E i (ω i)) =
      ∏ i, uniformProb (E i) := by
  classical
  let ec : {ω : (∀ i, Ω i) // ∀ i, E i (ω i)} ≃ (∀ i, {ω // E i ω}) :=
    { toFun := fun ω i => ⟨ω.val i, ω.property i⟩
      invFun := fun ω => ⟨fun i => (ω i).val, fun i => (ω i).property⟩
      left_inv := fun ω => rfl
      right_inv := fun ω => rfl }
  simp_rw [uniformProb_eq_card_subtype]
  calc
    _ = (Fintype.card (∀ i, {ω // E i ω}) : ℝ) /
        Fintype.card (∀ i, Ω i) := by
      congr 1
      norm_cast
      convert Fintype.card_congr ec using 1
      congr 1
      exact Subsingleton.elim _ _
    _ = _ := by simp [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

theorem uniformProb_pi_finset {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (S : Finset I)
    (E : ∀ i, Ω i → Prop) :
    uniformProb (fun ω : ∀ i, Ω i => ∀ i ∈ S, E i (ω i)) =
      ∏ i ∈ S, uniformProb (E i) := by
  classical
  have h := uniformProb_pi (fun i ω => i ∈ S → E i ω)
  rw [show (fun ω : ∀ i, Ω i => ∀ i ∈ S, E i (ω i)) =
    (fun ω => ∀ i, i ∈ S → E i (ω i)) from rfl, h]
  rw [← Finset.prod_subset (Finset.subset_univ S) (by
    intro i _ hi
    simpa [hi] using (uniformProb_true (Ω := Ω i)))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [hi]

theorem uniformProb_eval {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [Nonempty Ω]
    (i : I) (E : Ω → Prop) :
    uniformProb (fun ω : I → Ω => E (ω i)) = uniformProb E := by
  classical
  simpa using uniformProb_pi_finset (Ω := fun _ : I => Ω) {i} (fun _ => E)

theorem uniformProb_addHom_eq {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    uniformProb (fun x => f x = y) = 1 / (Fintype.card H : ℝ) := by
  classical
  have hsame (z : H) : (Finset.univ.filter fun x => f x = z).card =
      (Finset.univ.filter fun x => f x = y).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter fun x => f x = y).card := by
    calc
      Fintype.card G = ∑ z : H, (Finset.univ.filter fun x => f x = z).card := by
        exact Finset.card_eq_sum_card_fiberwise (by simp)
      _ = _ := by simp_rw [hsame]; simp
  have hpos : 0 < (Finset.univ.filter fun x => f x = y).card := by
    obtain ⟨x, hx⟩ := hf y
    exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩
  rw [uniformProb_eq_card_filter, hcard, Nat.cast_mul]
  have hne : ((Finset.univ.filter fun x => f x = y).card : ℝ) ≠ 0 := by positivity
  field_simp

end ExpandingCodes.PolynomialStretch
