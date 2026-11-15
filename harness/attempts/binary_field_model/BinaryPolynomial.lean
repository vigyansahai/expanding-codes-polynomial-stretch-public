import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch.BinaryPolynomial

open Polynomial

/-- Coefficients are stored from constant coefficient to highest coefficient. -/
abbrev Coefficients (ell : ℕ) := Fin ell → ZMod 2

/-- Explicit base-two expansion. The library map uses division and remainder,
and its inverse is the sum of coefficient values times powers of two. -/
def indexEquiv (ell : ℕ) : Fin (2 ^ ell) ≃ Coefficients ell :=
  finFunctionFinEquiv.symm.trans
    (Equiv.piCongrRight fun _ => (ZMod.finEquiv 2).toEquiv)

def bitEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun c := decide (c = 1)
  left_inv b := by cases b <;> decide
  right_inv c := by fin_cases c <;> rfl

def bitsEquiv (ell : ℕ) : (Fin ell → Bool) ≃ Coefficients ell :=
  Equiv.piCongrRight fun _ => bitEquiv

theorem bitEquiv_false : bitEquiv false = 0 := rfl

theorem bitEquiv_true : bitEquiv true = 1 := rfl

theorem bitEquiv_xor (a b : Bool) : bitEquiv (a ^^ b) = bitEquiv a + bitEquiv b := by
  cases a <;> cases b <;> rfl

theorem bitEquiv_and (a b : Bool) : bitEquiv (a && b) = bitEquiv a * bitEquiv b := by
  cases a <;> cases b <;> rfl

theorem indexEquiv_inverse_value (ell : ℕ) (c : Coefficients ell) :
    ((indexEquiv ell).symm c).val = ∑ j : Fin ell, (c j).val * 2 ^ j.val := rfl

theorem factorPairCount {ell k : ℕ} (hk : k ≤ ell) :
    2 ^ k * 2 ^ (ell - k) = 2 ^ ell := by
  rw [← pow_add, Nat.add_sub_of_le hk]

noncomputable def polynomial {ell : ℕ} (c : Coefficients ell) : (ZMod 2)[X] :=
  ∑ i : Fin ell, monomial i (c i)

theorem coefficient_polynomial {ell : ℕ} (c : Coefficients ell) (j : Fin ell) :
    (polynomial c).coeff j = c j := by
  simp only [polynomial, finsetSum_coeff, coeff_monomial, Fin.val_eq_val]
  simp

theorem degree_polynomial_lt {ell : ℕ} (c : Coefficients ell) :
    (polynomial c).degree < ell := by
  simpa only [polynomial, C_mul_X_pow_eq_monomial] using degree_sum_fin_lt c

theorem coefficient_polynomial_high {ell : ℕ} (c : Coefficients ell) {j : ℕ}
    (hj : ell ≤ j) : (polynomial c).coeff j = 0 :=
  coeff_eq_zero_of_degree_lt ((degree_polynomial_lt c).trans_le (by exact_mod_cast hj))

theorem polynomial_coefficients {ell : ℕ} (p : (ZMod 2)[X])
    (hp : p.degree < ell) : polynomial (fun i : Fin ell => p.coeff i) = p := by
  ext j
  by_cases hj : j < ell
  · exact coefficient_polynomial _ ⟨j, hj⟩
  · rw [coefficient_polynomial_high _ (by omega), coeff_eq_zero_of_degree_lt]
    exact hp.trans_le (by exact_mod_cast (show ell ≤ j by omega))

/-- The `2^ell` monic polynomials of degree exactly `ell`, in coefficient order. -/
noncomputable def candidate (ell : ℕ) (i : Fin (2 ^ ell)) : (ZMod 2)[X] :=
  X ^ ell + polynomial (indexEquiv ell i)

theorem candidate_monic (ell : ℕ) (i : Fin (2 ^ ell)) : (candidate ell i).Monic :=
  monic_X_pow_add (degree_polynomial_lt _)

theorem candidate_natDegree (ell : ℕ) (i : Fin (2 ^ ell)) :
    (candidate ell i).natDegree = ell := by
  unfold candidate
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa using degree_polynomial_lt (indexEquiv ell i)

theorem candidate_ne_one {ell : ℕ} (h : 0 < ell) (i : Fin (2 ^ ell)) :
    candidate ell i ≠ 1 := by
  intro hi
  have := candidate_natDegree ell i
  rw [hi, natDegree_one] at this
  omega

theorem candidate_surjective {ell : ℕ} (p : (ZMod 2)[X])
    (hm : p.Monic) (hd : p.natDegree = ell) :
    ∃ i : Fin (2 ^ ell), candidate ell i = p := by
  refine ⟨(indexEquiv ell).symm (fun j => p.coeff j), ?_⟩
  simp only [candidate, Equiv.apply_symm_apply]
  ext j
  by_cases hj : j < ell
  · simp only [coeff_add, coeff_X_pow, if_neg (by omega : j ≠ ell), zero_add]
    exact coefficient_polynomial _ ⟨j, hj⟩
  · rw [coeff_add, coefficient_polynomial_high _ (by omega), add_zero]
    by_cases he : ell = j
    · subst j
      simpa [← hd] using hm.coeff_natDegree.symm
    · rw [coeff_X_pow, if_neg (Ne.symm he), coeff_eq_zero_of_natDegree_lt (by omega)]

def candidateCoefficient (ell : ℕ) (i : Fin (2 ^ ell)) (j : ℕ) : ZMod 2 :=
  if j = ell then 1 else if hj : j < ell then indexEquiv ell i ⟨j, hj⟩ else 0

theorem candidateCoefficient_eq (ell : ℕ) (i : Fin (2 ^ ell)) (j : ℕ) :
    candidateCoefficient ell i j = (candidate ell i).coeff j := by
  unfold candidateCoefficient candidate
  rw [coeff_add, coeff_X_pow]
  split_ifs with hj hj
  · subst j
    rw [coefficient_polynomial_high _ le_rfl, add_zero]
  · rw [zero_add]
    exact (coefficient_polynomial _ ⟨j, hj⟩).symm
  · rw [coefficient_polynomial_high _ (by omega), add_zero]

/-- Finite convolution on coefficient buffers. -/
def productCoefficient (r s : ℕ) (a : Fin (2 ^ r)) (b : Fin (2 ^ s)) (j : ℕ) :
    ZMod 2 :=
  ∑ t ∈ Finset.range (j + 1),
    candidateCoefficient r a t * candidateCoefficient s b (j - t)

theorem productCoefficient_eq (r s : ℕ) (a : Fin (2 ^ r)) (b : Fin (2 ^ s))
    (j : ℕ) : productCoefficient r s a b j = (candidate r a * candidate s b).coeff j := by
  simp only [productCoefficient, candidateCoefficient_eq, coeff_mul]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
    (candidate r a).coeff x * (candidate s b).coeff y) j).symm

def ProductMatches (ell k : ℕ) (a : Fin (2 ^ k)) (b : Fin (2 ^ (ell - k)))
    (i : Fin (2 ^ ell)) : Prop :=
  ∀ j : Fin (ell + 1), productCoefficient k (ell - k) a b j = candidateCoefficient ell i j

instance (ell k : ℕ) (a : Fin (2 ^ k)) (b : Fin (2 ^ (ell - k)))
    (i : Fin (2 ^ ell)) : Decidable (ProductMatches ell k a b i) :=
  inferInstanceAs (Decidable (∀ j : Fin (ell + 1),
    productCoefficient k (ell - k) a b j = candidateCoefficient ell i j))

theorem productMatches_iff {ell k : ℕ} (hk : k ≤ ell) (a : Fin (2 ^ k))
    (b : Fin (2 ^ (ell - k))) (i : Fin (2 ^ ell)) :
    ProductMatches ell k a b i ↔ candidate k a * candidate (ell - k) b = candidate ell i := by
  constructor
  · intro hm
    ext j
    by_cases hj : j < ell + 1
    · simpa only [productCoefficient_eq, candidateCoefficient_eq] using hm ⟨j, hj⟩
    · rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
      · rw [candidate_natDegree]; omega
      · rw [(candidate_monic _ _).natDegree_mul (candidate_monic _ _),
          candidate_natDegree, candidate_natDegree]
        omega
  · intro hm j
    rw [productCoefficient_eq, candidateCoefficient_eq, hm]

/-- Check bounded monic factor pairs by coefficient convolution. For each
factor degree the number of pairs is exactly `2^ell`. -/
def FactorFree (ell : ℕ) (i : Fin (2 ^ ell)) : Prop :=
  ∀ k : Fin (ell + 1), 0 < k.val → 2 * k.val ≤ ell →
    ∀ a : Fin (2 ^ k.val), ∀ b : Fin (2 ^ (ell - k.val)), ¬ ProductMatches ell k.val a b i

instance (ell : ℕ) (i : Fin (2 ^ ell)) : Decidable (FactorFree ell i) :=
  inferInstanceAs (Decidable (∀ k : Fin (ell + 1), 0 < k.val → 2 * k.val ≤ ell →
    ∀ a : Fin (2 ^ k.val), ∀ b : Fin (2 ^ (ell - k.val)), ¬ ProductMatches ell k.val a b i))

theorem factorFree_iff_irreducible {ell : ℕ} (h : 0 < ell) (i : Fin (2 ^ ell)) :
    FactorFree ell i ↔ Irreducible (candidate ell i) := by
  rw [(candidate_monic ell i).irreducible_iff_natDegree', and_iff_right (candidate_ne_one h i)]
  constructor
  · intro hf f g hfm hgm hfg hg
    rw [candidate_natDegree] at hg
    simp only [Finset.mem_Ioc] at hg
    have hdeg : g.natDegree < ell + 1 := by omega
    have hsum : g.natDegree + f.natDegree = ell := by
      rw [← hgm.natDegree_mul hfm, mul_comm, hfg, candidate_natDegree]
    obtain ⟨a, ha⟩ := candidate_surjective g hgm rfl
    obtain ⟨b, hb⟩ := candidate_surjective f hfm (by omega : f.natDegree = ell - g.natDegree)
    apply hf ⟨g.natDegree, hdeg⟩ hg.1 (by change 2 * g.natDegree ≤ ell; omega) a b
    apply (productMatches_iff (by omega) a b i).mpr
    rw [ha, hb, mul_comm, hfg]
  · intro hir k hk hhalf a b hm
    apply hir (candidate (ell - k.val) b) (candidate k.val a)
      (candidate_monic _ _) (candidate_monic _ _) ?_ ?_
    · rw [mul_comm]
      exact (productMatches_iff (by omega) a b i).mp hm
    · simp only [candidate_natDegree, Finset.mem_Ioc]
      exact ⟨hk, by omega⟩

theorem exists_irreducible_monic (ell : ℕ) (h : 0 < ell) :
    ∃ p : (ZMod 2)[X], p.Monic ∧ p.natDegree = ell ∧ Irreducible p := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element_of_finite_top
    (ZMod 2) (GaloisField 2 ell)
  have hint : IsIntegral (ZMod 2) a := IsIntegral.of_finite (ZMod 2) a
  refine ⟨minpoly (ZMod 2) a, minpoly.monic hint, ?_, minpoly.irreducible hint⟩
  exact ((Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) a).mp ha).trans
    (GaloisField.finrank 2 h.ne')

theorem exists_factorFree (ell : ℕ) (h : 0 < ell) :
    ∃ i : Fin (2 ^ ell), FactorFree ell i := by
  obtain ⟨p, hm, hd, hi⟩ := exists_irreducible_monic ell h
  obtain ⟨i, rfl⟩ := candidate_surjective p hm hd
  exact ⟨i, (factorFree_iff_irreducible h i).mpr hi⟩

/-- The first successful candidate in the bounded coefficient enumeration.
The existence proof affects no executable data. -/
def selectedIndex (ell : ℕ) (h : 0 < ell) : Fin (2 ^ ell) :=
  (Finset.univ.filter (FactorFree ell)).min' (by
    obtain ⟨i, hi⟩ := exists_factorFree ell h
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩)

theorem selectedIndex_factorFree (ell : ℕ) (h : 0 < ell) :
    FactorFree ell (selectedIndex ell h) := by
  have := Finset.min'_mem (Finset.univ.filter (FactorFree ell))
    (by obtain ⟨i, hi⟩ := exists_factorFree ell h; exact ⟨i, by simpa using hi⟩)
  exact (Finset.mem_filter.mp this).2

theorem selectedIndex_le (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell))
    (hi : FactorFree ell i) : selectedIndex ell h ≤ i := by
  exact Finset.min'_le _ _ (by simpa using hi)

noncomputable def modulus (ell : ℕ) (h : 0 < ell) : (ZMod 2)[X] :=
  candidate ell (selectedIndex ell h)

theorem modulus_monic (ell : ℕ) (h : 0 < ell) : (modulus ell h).Monic :=
  candidate_monic _ _

theorem modulus_natDegree (ell : ℕ) (h : 0 < ell) : (modulus ell h).natDegree = ell :=
  candidate_natDegree _ _

theorem modulus_irreducible (ell : ℕ) (h : 0 < ell) : Irreducible (modulus ell h) :=
  (factorFree_iff_irreducible h _).mp (selectedIndex_factorFree ell h)

end ExpandingCodes.PolynomialStretch.BinaryPolynomial
