import ExpandingCodes.Probability.FiniteUniform

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {E F : Ω → Prop} (h : ∀ x, E x → F x) : uniformProb E ≤ uniformProb F := by
  classical
  rw [uniformProb_eq_card_filter, uniformProb_eq_card_filter]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show (Finset.univ.filter E) ⊆ Finset.univ.filter F by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h x (Finset.mem_filter.mp hx).2⟩)

theorem uniformProb_exists_finset {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset ι) (E : ι → Ω → Prop) :
    uniformProb (fun x => ∃ i ∈ s, E i x) ≤ ∑ i ∈ s, uniformProb (E i) := by
  classical
  simp_rw [uniformProb_eq_card_filter]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc := Finset.card_biUnion_le (s := s)
    (t := fun i => Finset.univ.filter (E i))
  have hr : ((s.biUnion (fun i => Finset.univ.filter (E i))).card : ℝ) ≤
      ∑ i ∈ s, ((Finset.univ.filter (E i)).card : ℝ) := by exact_mod_cast hc
  convert hr using 1
  · rfl
  · apply congrArg (fun A : Finset Ω => (A.card : ℝ))
    ext x
    simp

end ExpandingCodes.PolynomialStretch
