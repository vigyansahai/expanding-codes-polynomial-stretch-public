import ExpandingCodes.Computation.FieldCertificates

set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.RawIrreducibility
open Polynomial
open ExpandingCodes.PolynomialStretch BinaryPolynomial BinaryField
open FieldConvolution FieldCertificates FieldPrograms

noncomputable def poly (ell : ℕ) (a : Fin (2^ell)) : (ZMod 2)[X] :=
  polynomial (indexEquiv ell a)

theorem poly_coeff (ell : ℕ) (a : Fin (2^ell)) (j : ℕ) :
    (poly ell a).coeff j = bitEquiv (Nat.testBit a.val j) :=
  (bufferCoefficient_eq (indexEquiv ell a) j).symm.trans (bufferCoefficient_bit ell a j)

theorem poly_zero (ell : ℕ) (a : Fin (2^ell)) (ha : a.val = 0) : poly ell a = 0 := by
  ext j
  simp [poly_coeff,ha,bitEquiv_false]

theorem poly_one (ell : ℕ) (a : Fin (2^ell)) (ha : a.val = 1) : poly ell a = 1 := by
  ext j
  rw [poly_coeff,ha]
  cases j <;> simp [Polynomial.coeff_one,Nat.testBit_succ,bitEquiv_false,bitEquiv_true]

theorem val_one_of_poly_one (ell : ℕ) (a : Fin (2^ell)) (ha : poly ell a = 1) : a.val = 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply bitEquiv.injective
  rw [← poly_coeff,ha]
  cases j <;> simp [Polynomial.coeff_one,Nat.testBit_succ,bitEquiv_false,bitEquiv_true]

theorem poly_isUnit_iff (ell : ℕ) (a : Fin (2^ell)) : IsUnit (poly ell a) ↔ a.val = 1 := by
  constructor
  · intro hu
    obtain ⟨c,hc,hcp⟩ := Polynomial.isUnit_iff.mp hu
    have hc₁ : c = 1 := by
      have hcn : c ≠ 0 := hc.ne_zero
      fin_cases c
      · exact (hcn rfl).elim
      · rfl
    apply val_one_of_poly_one ell a
    rw [← hcp,hc₁]
    simp
  · intro ha
    rw [poly_one ell a ha]
    exact isUnit_one

/-- The exact raw coefficient certificate used by the physical q-by-q factor
scan. The target includes its leading monic bit; both extra operands are zero. -/
def FactorMatches (ell : ℕ) (p a b : Fin (2^ell)) : Prop :=
  ∀ j < 3*ell+1, CoefficientMatches a.val b.val (2^ell+p.val) 0 0 j

instance (ell : ℕ) (p a b : Fin (2^ell)) : Decidable (FactorMatches ell p a b) := by
  unfold FactorMatches
  infer_instance

def FactorFree (ell : ℕ) (p : Fin (2^ell)) : Prop :=
  ∀ a b : Fin (2^ell), 1 < a.val → 1 < b.val → ¬ FactorMatches ell p a b

instance (ell : ℕ) (p : Fin (2^ell)) : Decidable (FactorFree ell p) := by
  unfold FactorFree
  infer_instance

theorem factorMatches_iff (ell : ℕ) (hell : 0 < ell) (p a b : Fin (2^ell)) :
    FactorMatches ell p a b ↔ poly ell a * poly ell b = candidate ell p := by
  have hraw (j : ℕ) : CoefficientMatches a.val b.val (2^ell+p.val) 0 0 j ↔
      (poly ell a * poly ell b).coeff j = (candidate ell p).coeff j := by
    have hz : rawConvolution 0 0 j = 0 := by simp [rawConvolution,bitEquiv_false]
    rw [CoefficientMatches,rawConvolution_eq_convolution ell ell a b j,convolution_eq,hz,add_zero,
      ← candidateCoefficient_bit, candidateCoefficient_eq]
    rfl
  constructor
  · intro h
    have ha := natDegree_polynomial_lt hell (indexEquiv ell a)
    have hb := natDegree_polynomial_lt hell (indexEquiv ell b)
    have hl : (poly ell a * poly ell b).natDegree ≤ 3*ell :=
      natDegree_mul_le.trans (by change (polynomial _).natDegree + (polynomial _).natDegree ≤ _; omega)
    have hr : (candidate ell p).natDegree ≤ 3*ell := by rw [candidate_natDegree]; omega
    apply (ext_iff_natDegree_le hl hr).mpr
    intro j hj
    exact (hraw j).mp (h j (by omega))
  · intro h j _
    apply (hraw j).mpr
    rw [h]

theorem factorFree_iff_irreducible (ell : ℕ) (hell : 0 < ell) (p : Fin (2^ell)) :
    FactorFree ell p ↔ Irreducible (candidate ell p) := by
  constructor
  · intro hfree
    refine ⟨fun hu => candidate_ne_one hell p ((candidate_monic ell p).eq_one_of_isUnit hu), ?_⟩
    intro f g hfg
    by_contra hu
    have hf : ¬ IsUnit f := fun h => hu (Or.inl h)
    have hg : ¬ IsUnit g := fun h => hu (Or.inr h)
    have hp0 : candidate ell p ≠ 0 := (candidate_monic ell p).ne_zero
    have hf0 : f ≠ 0 := by intro hh; simp [hh] at hfg; exact hp0 hfg
    have hg0 : g ≠ 0 := by intro hh; simp [hh] at hfg; exact hp0 hfg
    have hfd : 0 < f.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic (candidate_monic ell p) hf ⟨g,hfg⟩
    have hgd : 0 < g.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic (candidate_monic ell p) hg ⟨f,by rw [mul_comm]; exact hfg⟩
    have hsum : f.natDegree+g.natDegree = ell := by
      rw [← natDegree_mul hf0 hg0,← hfg,candidate_natDegree]
    have hflt : f.degree < ell := (natDegree_lt_iff_degree_lt hf0).mp (by omega : f.natDegree < ell)
    have hglt : g.degree < ell := (natDegree_lt_iff_degree_lt hg0).mp (by omega : g.natDegree < ell)
    let a := (indexEquiv ell).symm (fun j : Fin ell => f.coeff j)
    let b := (indexEquiv ell).symm (fun j : Fin ell => g.coeff j)
    have ha : poly ell a = f := by
      rw [poly,show indexEquiv ell a = (fun j : Fin ell => f.coeff j) from Equiv.apply_symm_apply _ _]
      exact polynomial_coefficients f hflt
    have hb : poly ell b = g := by
      rw [poly,show indexEquiv ell b = (fun j : Fin ell => g.coeff j) from Equiv.apply_symm_apply _ _]
      exact polynomial_coefficients g hglt
    have hav : 1 < a.val := by
      have ha₀ : a.val ≠ 0 := by intro he; have hh := poly_zero ell a he; rw [ha] at hh; exact hf0 hh
      have ha₁ : a.val ≠ 1 := by intro he; apply hf; rw [← ha]; exact (poly_isUnit_iff ell a).mpr he
      omega
    have hbv : 1 < b.val := by
      have hb₀ : b.val ≠ 0 := by intro he; have hh := poly_zero ell b he; rw [hb] at hh; exact hg0 hh
      have hb₁ : b.val ≠ 1 := by intro he; apply hg; rw [← hb]; exact (poly_isUnit_iff ell b).mpr he
      omega
    apply hfree a b hav hbv
    apply (factorMatches_iff ell hell p a b).mpr
    rw [ha,hb]
    exact hfg.symm
  · intro hi a b ha hb hm
    have hp := (factorMatches_iff ell hell p a b).mp hm
    rcases hi.isUnit_or_isUnit hp.symm with hu | hu
    · have := (poly_isUnit_iff ell a).mp hu
      omega
    · have := (poly_isUnit_iff ell b).mp hu
      omega

theorem factorFree_iff_canonical (ell : ℕ) (hell : 0 < ell) (p : Fin (2^ell)) :
    FactorFree ell p ↔ BinaryPolynomial.FactorFree ell p :=
  (factorFree_iff_irreducible ell hell p).trans (BinaryPolynomial.factorFree_iff_irreducible hell p).symm

theorem selectedIndex_factorFree (ell : ℕ) (hell : 0 < ell) :
    FactorFree ell (selectedIndex ell hell) :=
  (factorFree_iff_canonical ell hell _).mpr (BinaryPolynomial.selectedIndex_factorFree ell hell)

theorem selectedIndex_le (ell : ℕ) (hell : 0 < ell) (p : Fin (2^ell))
    (hp : FactorFree ell p) : selectedIndex ell hell ≤ p :=
  BinaryPolynomial.selectedIndex_le ell hell p ((factorFree_iff_canonical ell hell p).mp hp)

#print axioms factorMatches_iff
#print axioms factorFree_iff_canonical
#print axioms selectedIndex_factorFree
end ExpandingCodes.Computation.RawIrreducibility
