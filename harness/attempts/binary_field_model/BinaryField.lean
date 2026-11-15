import ExpandingCodes.Computation.BinaryPolynomial

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Polynomial BinaryPolynomial

abbrev Carrier (ell : ℕ) (h : 0 < ell) := AdjoinRoot (modulus ell h)

instance modulusFact (ell : ℕ) (h : 0 < ell) : Fact (Irreducible (modulus ell h)) :=
  ⟨modulus_irreducible ell h⟩

noncomputable instance field (ell : ℕ) (h : 0 < ell) : Field (Carrier ell h) :=
  inferInstanceAs (Field (AdjoinRoot (modulus ell h)))

instance charTwo (ell : ℕ) (h : 0 < ell) : CharP (Carrier ell h) 2 :=
  (Algebra.charP_iff (ZMod 2) (Carrier ell h) 2).mp inferInstance

/-- Polynomial evaluation in the quotient. This is the mathematical
interpretation of a coefficient buffer, not an executable field operation. -/
noncomputable def decode (ell : ℕ) (h : 0 < ell) (c : Coefficients ell) :
    Carrier ell h :=
  AdjoinRoot.mk (modulus ell h) (polynomial c)

noncomputable def encode (ell : ℕ) (h : 0 < ell) (x : Carrier ell h) :
    Coefficients ell :=
  fun i => (AdjoinRoot.modByMonicHom (modulus_monic ell h) x).coeff i

theorem decode_encode (ell : ℕ) (h : 0 < ell) (x : Carrier ell h) :
    decode ell h (encode ell h x) = x := by
  unfold decode encode
  rw [polynomial_coefficients]
  · exact AdjoinRoot.mk_leftInverse (modulus_monic ell h) x
  · induction x using AdjoinRoot.induction_on with
    | ih p =>
      rw [AdjoinRoot.modByMonicHom_mk]
      have := degree_modByMonic_lt p (modulus_monic ell h)
      simpa only [degree_eq_natDegree (modulus_monic ell h).ne_zero, modulus_natDegree] using this

theorem encode_decode (ell : ℕ) (h : 0 < ell) (c : Coefficients ell) :
    encode ell h (decode ell h c) = c := by
  funext i
  unfold encode decode
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (modulus_monic ell h)).mpr]
  · exact coefficient_polynomial c i
  · simpa only [degree_eq_natDegree (modulus_monic ell h).ne_zero, modulus_natDegree] using
      degree_polynomial_lt c

noncomputable def coefficientEquiv (ell : ℕ) (h : 0 < ell) :
    Coefficients ell ≃ Carrier ell h where
  toFun := decode ell h
  invFun := encode ell h
  left_inv := encode_decode ell h
  right_inv := decode_encode ell h

/-- Every index is evaluated using exactly its explicit binary coefficients. -/
noncomputable def elements (ell : ℕ) (h : 0 < ell) : Fin (2 ^ ell) ≃ Carrier ell h :=
  (indexEquiv ell).trans (coefficientEquiv ell h)

theorem elements_apply (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell)) :
    elements ell h i = AdjoinRoot.mk (modulus ell h) (polynomial (indexEquiv ell i)) := rfl

noncomputable instance finite (ell : ℕ) (h : 0 < ell) : Fintype (Carrier ell h) :=
  Fintype.ofEquiv (Fin (2 ^ ell)) (elements ell h)

theorem card (ell : ℕ) (h : 0 < ell) : Fintype.card (Carrier ell h) = 2 ^ ell := by
  simpa using Fintype.card_congr (elements ell h).symm

/-- Executable coefficientwise field addition. -/
def add {ell : ℕ} (a b : Coefficients ell) : Coefficients ell := fun i => a i + b i

theorem polynomial_add {ell : ℕ} (a b : Coefficients ell) :
    polynomial (add a b) = polynomial a + polynomial b := by
  simp only [polynomial, add, map_add, Finset.sum_add_distrib]

theorem decode_add (ell : ℕ) (h : 0 < ell) (a b : Coefficients ell) :
    decode ell h (add a b) = decode ell h a + decode ell h b := by
  simp only [decode, polynomial_add, map_add]

def bufferCoefficient {ell : ℕ} (c : Coefficients ell) (j : ℕ) : ZMod 2 :=
  if hj : j < ell then c ⟨j, hj⟩ else 0

theorem bufferCoefficient_eq {ell : ℕ} (c : Coefficients ell) (j : ℕ) :
    bufferCoefficient c j = (polynomial c).coeff j := by
  unfold bufferCoefficient
  split_ifs with hj
  · exact (coefficient_polynomial _ ⟨j, hj⟩).symm
  · exact (coefficient_polynomial_high _ (by omega)).symm

def convolution {r s : ℕ} (a : Coefficients r) (b : Coefficients s) (j : ℕ) : ZMod 2 :=
  ∑ t ∈ Finset.range (j + 1), bufferCoefficient a t * bufferCoefficient b (j - t)

theorem convolution_eq {r s : ℕ} (a : Coefficients r) (b : Coefficients s) (j : ℕ) :
    convolution a b j = (polynomial a * polynomial b).coeff j := by
  simp only [convolution, bufferCoefficient_eq, coeff_mul]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
    (polynomial a).coeff x * (polynomial b).coeff y) j).symm

def modulusConvolution (ell : ℕ) (m : Fin (2 ^ ell))
    (s : Coefficients (2 * ell)) (j : ℕ) : ZMod 2 :=
  ∑ t ∈ Finset.range (j + 1), candidateCoefficient ell m t * bufferCoefficient s (j - t)

theorem modulusConvolution_eq (ell : ℕ) (m : Fin (2 ^ ell))
    (s : Coefficients (2 * ell)) (j : ℕ) :
    modulusConvolution ell m s j = (candidate ell m * polynomial s).coeff j := by
  simp only [modulusConvolution, candidateCoefficient_eq, bufferCoefficient_eq, coeff_mul]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
    (candidate ell m).coeff x * (polynomial s).coeff y) j).symm

/-- Bounded quotient/remainder certificate, checked entirely on finite buffers.
The quotient buffer has `2ell` cells; a looser bound simplifies its existence
proof while keeping the search polynomial in `q = 2^ell`. -/
def DivMatches (ell : ℕ) (m : Fin (2 ^ ell)) (x y r : Coefficients ell)
    (s : Coefficients (2 * ell)) : Prop :=
  ∀ j : Fin (3 * ell + 1), convolution x y j =
    bufferCoefficient r j + modulusConvolution ell m s j

instance (ell : ℕ) (m : Fin (2 ^ ell)) (x y r : Coefficients ell)
    (s : Coefficients (2 * ell)) : Decidable (DivMatches ell m x y r s) :=
  inferInstanceAs (Decidable (∀ j : Fin (3 * ell + 1), convolution x y j =
    bufferCoefficient r j + modulusConvolution ell m s j))

theorem natDegree_polynomial_lt {ell : ℕ} (h : 0 < ell) (c : Coefficients ell) :
    (polynomial c).natDegree < ell := by
  by_cases hc : polynomial c = 0
  · simpa only [hc, natDegree_zero] using h
  · exact (natDegree_lt_iff_degree_lt hc).mpr (degree_polynomial_lt c)

theorem divMatches_iff (ell : ℕ) (h : 0 < ell) (m : Fin (2 ^ ell))
    (x y r : Coefficients ell) (s : Coefficients (2 * ell)) :
    DivMatches ell m x y r s ↔
      polynomial x * polynomial y = polynomial r + candidate ell m * polynomial s := by
  constructor
  · intro hm
    have hx := natDegree_polynomial_lt h x
    have hy := natDegree_polynomial_lt h y
    have hr := natDegree_polynomial_lt h r
    have hs := natDegree_polynomial_lt (by omega : 0 < 2 * ell) s
    have hleft : (polynomial x * polynomial y).natDegree ≤ 3 * ell :=
      natDegree_mul_le.trans (by omega)
    have hmul : (candidate ell m * polynomial s).natDegree ≤ 3 * ell :=
      natDegree_mul_le.trans (by rw [candidate_natDegree]; omega)
    have hrle : (polynomial r).natDegree ≤ 3 * ell := by omega
    have hright : (polynomial r + candidate ell m * polynomial s).natDegree ≤ 3 * ell :=
      by simpa only [max_self] using natDegree_add_le_of_le hrle hmul
    apply (ext_iff_natDegree_le hleft hright).mpr
    intro j hj
    simpa only [convolution_eq, bufferCoefficient_eq, modulusConvolution_eq, coeff_add] using
      hm ⟨j, by omega⟩
  · intro hm j
    simp only [convolution_eq, bufferCoefficient_eq, modulusConvolution_eq, hm, coeff_add]

theorem exists_divMatches (ell : ℕ) (h : 0 < ell) (m : Fin (2 ^ ell))
    (x y : Coefficients ell) :
    ∃ r : Fin (2 ^ ell), ∃ s : Fin (2 ^ (2 * ell)),
      DivMatches ell m x y (indexEquiv ell r) (indexEquiv (2 * ell) s) := by
  let p := polynomial x * polynomial y
  let r := p %ₘ candidate ell m
  let s := p /ₘ candidate ell m
  have hr : r.degree < ell := by
    simpa only [r, degree_eq_natDegree (candidate_monic ell m).ne_zero,
      candidate_natDegree] using degree_modByMonic_lt p (candidate_monic ell m)
  have hs : s.degree < (2 * ell : ℕ) := by
    apply (degree_divByMonic_le p (candidate ell m)).trans_lt
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show p.natDegree < 2 * ell by
      have hx := natDegree_polynomial_lt h x
      have hy := natDegree_polynomial_lt h y
      have hp := natDegree_mul_le (p := polynomial x) (q := polynomial y)
      change (polynomial x * polynomial y).natDegree < 2 * ell
      omega)
  refine ⟨(indexEquiv ell).symm (fun i => r.coeff i),
    (indexEquiv (2 * ell)).symm (fun i => s.coeff i), ?_⟩
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, divMatches_iff ell h,
    polynomial_coefficients (ell := ell) r hr, polynomial_coefficients (ell := 2 * ell) s hs]
  exact (modByMonic_add_div p (candidate ell m)).symm

/-- Exhaustive bounded buffer search. There are at most `q^3` pairs of
remainder and quotient buffers, with no field-table enumeration. -/
def multiplyIndex (ell : ℕ) (h : 0 < ell) (m : Fin (2 ^ ell))
    (x y : Coefficients ell) : Fin (2 ^ ell) :=
  (Finset.univ.filter (fun r : Fin (2 ^ ell) => ∃ s : Fin (2 ^ (2 * ell)),
    DivMatches ell m x y (indexEquiv ell r) (indexEquiv (2 * ell) s))).min' (by
      obtain ⟨r, s, hrs⟩ := exists_divMatches ell h m x y
      exact ⟨r, by simpa using (show ∃ s : Fin (2 ^ (2 * ell)),
        DivMatches ell m x y (indexEquiv ell r) (indexEquiv (2 * ell) s) from ⟨s, hrs⟩)⟩)

def multiply (ell : ℕ) (h : 0 < ell) (m : Fin (2 ^ ell))
    (x y : Coefficients ell) : Coefficients ell :=
  indexEquiv ell (multiplyIndex ell h m x y)

theorem multiply_certificate (ell : ℕ) (h : 0 < ell) (m : Fin (2 ^ ell))
    (x y : Coefficients ell) :
    ∃ s : Coefficients (2 * ell), DivMatches ell m x y (multiply ell h m x y) s := by
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun r : Fin (2 ^ ell) => ∃ s : Fin (2 ^ (2 * ell)),
      DivMatches ell m x y (indexEquiv ell r) (indexEquiv (2 * ell) s)))
    (by
      obtain ⟨r, s, hrs⟩ := exists_divMatches ell h m x y
      exact ⟨r, by simpa using (show ∃ s : Fin (2 ^ (2 * ell)),
        DivMatches ell m x y (indexEquiv ell r) (indexEquiv (2 * ell) s) from ⟨s, hrs⟩)⟩)
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hmem).2
  exact ⟨indexEquiv (2 * ell) s, hs⟩

theorem multiply_remainder (ell : ℕ) (h : 0 < ell) (m : Fin (2 ^ ell))
    (x y : Coefficients ell) :
    polynomial (multiply ell h m x y) = (polynomial x * polynomial y) %ₘ candidate ell m := by
  obtain ⟨s, hs⟩ := multiply_certificate ell h m x y
  have he := (divMatches_iff ell h m x y _ s).mp hs
  have hrem : (polynomial (multiply ell h m x y)).degree < (candidate ell m).degree := by
    simpa only [degree_eq_natDegree (candidate_monic ell m).ne_zero, candidate_natDegree] using
      degree_polynomial_lt (multiply ell h m x y)
  exact ((div_modByMonic_unique (polynomial s) (polynomial (multiply ell h m x y))
    (candidate_monic ell m) ⟨he.symm, hrem⟩).2).symm

theorem decode_multiply (ell : ℕ) (h : 0 < ell) (x y : Coefficients ell) :
    decode ell h (multiply ell h (selectedIndex ell h) x y) = decode ell h x * decode ell h y := by
  obtain ⟨s, hs⟩ := multiply_certificate ell h (selectedIndex ell h) x y
  have he := (divMatches_iff ell h (selectedIndex ell h) x y _ s).mp hs
  have hm := congrArg (AdjoinRoot.mk (modulus ell h)) he
  change AdjoinRoot.mk (modulus ell h) (polynomial x * polynomial y) =
    AdjoinRoot.mk (modulus ell h)
      (polynomial (multiply ell h (selectedIndex ell h) x y) + modulus ell h * polynomial s) at hm
  simp only [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero] at hm
  exact hm.symm

def zero (ell : ℕ) : Coefficients ell := fun _ => 0

def one (ell : ℕ) : Coefficients ell := fun i => if i.val = 0 then 1 else 0

theorem polynomial_zero (ell : ℕ) : polynomial (zero ell) = 0 := by
  simp only [polynomial, zero, map_zero, Finset.sum_const_zero]

theorem polynomial_one (ell : ℕ) (h : 0 < ell) : polynomial (one ell) = 1 := by
  unfold polynomial
  rw [Finset.sum_eq_single (⟨0, h⟩ : Fin ell)]
  · simp [one]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := by
      intro he
      apply hj
      exact Fin.ext he
    simp only [one, if_neg hj0, map_zero]
  · simp

theorem decode_zero (ell : ℕ) (h : 0 < ell) : decode ell h (zero ell) = 0 := by
  rw [decode, polynomial_zero, map_zero]

theorem decode_one (ell : ℕ) (h : 0 < ell) : decode ell h (one ell) = 1 := by
  rw [decode, polynomial_one ell h, map_one]

theorem exists_inverseIndex (ell : ℕ) (h : 0 < ell) (x : Coefficients ell)
    (hx : x ≠ zero ell) :
    ∃ i : Fin (2 ^ ell),
      multiply ell h (selectedIndex ell h) x (indexEquiv ell i) = one ell := by
  have hdx : decode ell h x ≠ 0 := by
    intro hz
    apply hx
    apply (coefficientEquiv ell h).injective
    exact hz.trans (decode_zero ell h).symm
  obtain ⟨y, hy⟩ := (coefficientEquiv ell h).surjective ((decode ell h x)⁻¹)
  refine ⟨(indexEquiv ell).symm y, ?_⟩
  rw [Equiv.apply_symm_apply]
  apply (coefficientEquiv ell h).injective
  change decode ell h (multiply ell h (selectedIndex ell h) x y) = decode ell h (one ell)
  rw [decode_multiply, decode_one, show decode ell h y = (decode ell h x)⁻¹ from hy,
    mul_inv_cancel₀ hdx]

/-- Search at most `q` encoded values for the inverse, reusing the bounded
multiplication algorithm. Zero is handled explicitly. -/
def inverse (ell : ℕ) (h : 0 < ell) (x : Coefficients ell) : Coefficients ell :=
  if hx : x = zero ell then zero ell
  else indexEquiv ell ((Finset.univ.filter (fun i : Fin (2 ^ ell) =>
    multiply ell h (selectedIndex ell h) x (indexEquiv ell i) = one ell)).min' (by
      obtain ⟨i, hi⟩ := exists_inverseIndex ell h x hx
      exact ⟨i, by simpa using hi⟩))

theorem multiply_inverse (ell : ℕ) (h : 0 < ell) (x : Coefficients ell)
    (hx : x ≠ zero ell) :
    multiply ell h (selectedIndex ell h) x (inverse ell h x) = one ell := by
  unfold inverse
  rw [dif_neg hx]
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun i : Fin (2 ^ ell) =>
      multiply ell h (selectedIndex ell h) x (indexEquiv ell i) = one ell))
    (by
      obtain ⟨i, hi⟩ := exists_inverseIndex ell h x hx
      exact ⟨i, by simpa using hi⟩)
  exact (Finset.mem_filter.mp hmem).2

theorem decode_inverse (ell : ℕ) (h : 0 < ell) (x : Coefficients ell) :
    decode ell h (inverse ell h x) = (decode ell h x)⁻¹ := by
  by_cases hx : x = zero ell
  · subst x
    simp [inverse, decode_zero]
  · have hm := congrArg (decode ell h) (multiply_inverse ell h x hx)
    rw [decode_multiply, decode_one] at hm
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)

def addIndex (ell : ℕ) (i j : Fin (2 ^ ell)) : Fin (2 ^ ell) :=
  (indexEquiv ell).symm (add (indexEquiv ell i) (indexEquiv ell j))

def inverseIndex (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell)) : Fin (2 ^ ell) :=
  (indexEquiv ell).symm (inverse ell h (indexEquiv ell i))

theorem elements_addIndex (ell : ℕ) (h : 0 < ell) (i j : Fin (2 ^ ell)) :
    elements ell h (addIndex ell i j) = elements ell h i + elements ell h j := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm
    (add (indexEquiv ell i) (indexEquiv ell j)))) = _
  rw [Equiv.apply_symm_apply, decode_add]
  rfl

theorem elements_multiplyIndex (ell : ℕ) (h : 0 < ell) (i j : Fin (2 ^ ell)) :
    elements ell h (multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell i)
      (indexEquiv ell j)) = elements ell h i * elements ell h j := by
  exact decode_multiply ell h (indexEquiv ell i) (indexEquiv ell j)

theorem elements_inverseIndex (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell)) :
    elements ell h (inverseIndex ell h i) = (elements ell h i)⁻¹ := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm
    (inverse ell h (indexEquiv ell i)))) = _
  rw [Equiv.apply_symm_apply]
  exact decode_inverse ell h (indexEquiv ell i)

def multiplicationCandidateCount (ell : ℕ) : ℕ := 2 ^ ell * 2 ^ (2 * ell)

theorem multiplicationCandidateCount_eq (ell : ℕ) :
    multiplicationCandidateCount ell = (2 ^ ell) ^ 3 := by
  unfold multiplicationCandidateCount
  rw [← pow_add, ← pow_mul]
  congr 1
  omega

/-- A loose count of coefficient additions/multiplications/comparisons for
the complete bounded multiplication search, excluding later tape movement.
Each certificate checks `3ell+1` positions and two convolutions per position. -/
def multiplicationCoefficientBudget (ell : ℕ) : ℕ :=
  multiplicationCandidateCount ell * (3 * ell + 1) * (4 * (3 * ell + 1) + 2)

theorem exponent_le_fieldSize (ell : ℕ) : ell ≤ 2 ^ ell := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ ell := pow_pos (by decide) ell
    omega

theorem multiplicationCoefficientBudget_le (ell : ℕ) :
    multiplicationCoefficientBudget ell ≤ 64 * (2 ^ ell + 1) ^ 5 := by
  have he := exponent_le_fieldSize ell
  have hfirst : 3 * ell + 1 ≤ 4 * (2 ^ ell + 1) := by omega
  have hsecond : 4 * (3 * ell + 1) + 2 ≤ 16 * (2 ^ ell + 1) := by omega
  unfold multiplicationCoefficientBudget
  rw [multiplicationCandidateCount_eq]
  calc
    (2 ^ ell) ^ 3 * (3 * ell + 1) * (4 * (3 * ell + 1) + 2)
      ≤ (2 ^ ell + 1) ^ 3 * (4 * (2 ^ ell + 1)) * (16 * (2 ^ ell + 1)) := by
        gcongr
        omega
    _ = 64 * (2 ^ ell + 1) ^ 5 := by ring

def inverseCoefficientBudget (ell : ℕ) : ℕ :=
  2 ^ ell * (multiplicationCoefficientBudget ell + 2 * ell + 1)

theorem inverseCoefficientBudget_le (ell : ℕ) :
    inverseCoefficientBudget ell ≤ 67 * (2 ^ ell + 1) ^ 6 := by
  have he := exponent_le_fieldSize ell
  have hpow : 2 ^ ell + 1 ≤ (2 ^ ell + 1) ^ 5 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (by omega : 0 < 2 ^ ell + 1) (by decide : 1 ≤ 5))
  have hcmp : 2 * ell + 1 ≤ 3 * (2 ^ ell + 1) ^ 5 := by omega
  unfold inverseCoefficientBudget
  calc
    2 ^ ell * (multiplicationCoefficientBudget ell + 2 * ell + 1)
      ≤ (2 ^ ell + 1) * (64 * (2 ^ ell + 1) ^ 5 + 3 * (2 ^ ell + 1) ^ 5) := by
        apply Nat.mul_le_mul (by omega)
        have hm := multiplicationCoefficientBudget_le ell
        omega
    _ = 67 * (2 ^ ell + 1) ^ 6 := by ring

end ExpandingCodes.PolynomialStretch.BinaryField
