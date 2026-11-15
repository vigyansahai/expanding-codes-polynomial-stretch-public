import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily

set_option autoImplicit false

/-! Inlined whole module: ExpandingCodes.Construction.Implementation -/
section FlattenModule0


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

/-- The two exact sampling clauses of `EfficientFamily`, with one fixed finite
transition table and polynomial bound before the size and random tape. -/
noncomputable def SamplerImplementation (θ : ℚ)
    (g : ∀ n, Geometry (dimension (θ : ℝ)) n) : Prop :=
  ∃ (sampler : NKtLB.Machine) (A a N : ℕ), 0 < A ∧ 2 ≤ N ∧ ∀ n ≥ N,
    (∀ ω : Fin (A * (n + 1) ^ a) → Bool,
      ∃ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
        sampledRun sampler n (A * (n + 1) ^ a) (A * (n + 1) ^ a) ω (matrixBits G)) ∧
    (∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
      uniformProb (fun ω : Fin (A * (n + 1) ^ a) → Bool =>
        sampledRun sampler n (A * (n + 1) ^ a) (A * (n + 1) ^ a) ω (matrixBits G)) =
          (sampleLaw (θ : ℝ) n (g n) G).toReal)

/-- The exact deterministic transition-table clause of `EfficientFamily`.
Rational θ is the parameter embedded in the finite tester program. -/
noncomputable def TesterImplementation (θ : ℚ)
    (g : ∀ n, Geometry (dimension (θ : ℝ)) n) : Prop :=
  ∃ (tester : NKtLB.Machine) (B b N : ℕ), 0 < B ∧ 2 ≤ N ∧ ∀ n ≥ N,
    ∀ y : Word (rowCount (dimension (θ : ℝ)) n),
      tester.Computes (B * (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b)
        (sizeInput n ++ wordBits y) [rankTest (θ : ℝ) (g n) y]

end ExpandingCodes.PolynomialStretch

end FlattenModule0

/-! Inlined whole module: ExpandingCodes.Computation.BinaryPolynomial -/
section FlattenModule1





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





noncomputable def modulus (ell : ℕ) (h : 0 < ell) : (ZMod 2)[X] :=
  candidate ell (selectedIndex ell h)

theorem modulus_monic (ell : ℕ) (h : 0 < ell) : (modulus ell h).Monic :=
  candidate_monic _ _

theorem modulus_natDegree (ell : ℕ) (h : 0 < ell) : (modulus ell h).natDegree = ell :=
  candidate_natDegree _ _

theorem modulus_irreducible (ell : ℕ) (h : 0 < ell) : Irreducible (modulus ell h) :=
  (factorFree_iff_irreducible h _).mp (selectedIndex_factorFree ell h)

end ExpandingCodes.PolynomialStretch.BinaryPolynomial

end FlattenModule1

/-! Inlined whole module: ExpandingCodes.Computation.BinaryField -/
section FlattenModule2


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




noncomputable instance finite (ell : ℕ) (h : 0 < ell) : Fintype (Carrier ell h) :=
  Fintype.ofEquiv (Fin (2 ^ ell)) (elements ell h)




/-- Executable coefficientwise field addition. -/
def add {ell : ℕ} (a b : Coefficients ell) : Coefficients ell := fun i => a i + b i









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























def addIndex (ell : ℕ) (i j : Fin (2 ^ ell)) : Fin (2 ^ ell) :=
  (indexEquiv ell).symm (add (indexEquiv ell i) (indexEquiv ell j))

def inverseIndex (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell)) : Fin (2 ^ ell) :=
  (indexEquiv ell).symm (inverse ell h (indexEquiv ell i))












































































end ExpandingCodes.PolynomialStretch.BinaryField

end FlattenModule2

/-! Inlined whole module: ExpandingCodes.Construction.Geometry -/
section FlattenModule3



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

theorem fieldExponent_pos (d n : ℕ) : 0 < fieldExponent d n := by
  unfold fieldExponent
  omega











theorem geometry_card {d n : ℕ} (g : Geometry d n) :
    Fintype.card g.F = fieldSize d n := by
  simpa using Fintype.card_congr g.elements.symm























end ExpandingCodes.PolynomialStretch

end FlattenModule3

/-! Inlined whole module: ExpandingCodes.Construction.BinaryGeometry -/
section FlattenModule4



set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

/-- Finite-field geometry using the least successful explicit binary modulus.
Rows are enumerated by base-`q` digits, each interpreted by its binary
coefficient vector. No cardinality-choice enumeration enters either map. -/
noncomputable def binaryGeometry (d n : ℕ) : Geometry d n where
  F := BinaryField.Carrier (fieldExponent d n) (fieldExponent_pos d n)
  field := inferInstance
  finite := inferInstance
  charTwo := inferInstance
  elements := BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n)
  rowOrder := finFunctionFinEquiv.symm.trans
    (Equiv.piCongrRight fun _ => BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n))









end ExpandingCodes.PolynomialStretch

end FlattenModule4

/-! Inlined whole module: ExpandingCodes.Computation.TapeProgram -/
section FlattenModule5


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Finite unary-counter programs with explicit symbol work buffers. Each buffer
operation inspects only the cell under its head; there are no whole-array or arithmetic oracles. -/
inductive TapeInstr (registers buffers labels : ℕ) where
  | halt
  | jump (next : Fin labels)
  | inc (reg : Fin registers) (next : Fin labels)
  | dec (reg : Fin registers) (zero positive : Fin labels)
  | emit (bit : Bool) (next : Fin labels)
  | read (tape : Fin 4) (next : Sym → Fin labels)
  /-- A four-entry table. One scanned cell determines one written symbol, one
  unit head movement, and one finite next label; the rest of the tape is inaccessible. -/
  | buffer (tape : Fin buffers) (action : Sym → Sym × Move × Fin labels)

structure TapeProgram (registers buffers labels : ℕ) where
  entry : Fin labels
  code : Fin labels → TapeInstr registers buffers labels

structure TapeCfg (registers buffers labels : ℕ) where
  pc : Fin labels
  reg : Fin registers → ℕ
  roHead : Fin 4 → ℕ
  output : List Bool
  bufferTape : Fin buffers → List Sym
  bufferHead : Fin buffers → ℕ

namespace TapeProgram
variable {R B L : ℕ}

def init (P : TapeProgram R B L) : TapeCfg R B L :=
  ⟨P.entry, fun _ => 0, fun _ => 0, [], fun _ => [], fun _ => 0⟩

def halted (P : TapeProgram R B L) (c : TapeCfg R B L) : Prop :=
  P.code c.pc = .halt

instance (P : TapeProgram R B L) (c : TapeCfg R B L) : Decidable (P.halted c) := by
  unfold halted
  cases P.code c.pc
  · exact isTrue rfl
  all_goals exact isFalse (by intro h; cases h)

/-- Exact source semantics. Buffer contents are explicit finite symbol lists,
not arrays packed into a unary natural register. -/
def step (P : TapeProgram R B L) (inp : Inputs) (c : TapeCfg R B L) : TapeCfg R B L :=
  match P.code c.pc with
  | .halt => c
  | .jump j => { c with pc := j }
  | .inc r j => { c with pc := j, reg := Function.update c.reg r (c.reg r + 1) }
  | .dec r z p =>
    if c.reg r = 0 then { c with pc := z }
    else { c with pc := p, reg := Function.update c.reg r (c.reg r - 1) }
  | .emit b j => { c with pc := j, output := (c.output ++ [b]) }
  | .read r next =>
    { c with
      pc := next (Machine.readRO (inp.get r) (c.roHead r))
      roHead := Function.update c.roHead r (c.roHead r + 1) }
  | .buffer b action =>
    let a := action ((c.bufferTape b).getD (c.bufferHead b) .blank)
    { c with
      pc := a.2.2
      bufferTape := Function.update c.bufferTape b
        (Machine.writeAt (c.bufferTape b) (c.bufferHead b) a.1)
      bufferHead := Function.update c.bufferHead b (Machine.moveHead a.2.1 (c.bufferHead b)) }

/-- Number of target transitions used by the compiler for a single instruction.
Halting configurations are already represented by the target's halting state. -/
def cost (P : TapeProgram R B L) (c : TapeCfg R B L) : ℕ :=
  match P.code c.pc with
  | .halt => 0
  | .inc _ _ => 2
  | _ => 1

def run (P : TapeProgram R B L) (inp : Inputs) (t : ℕ) : TapeCfg R B L :=
  (P.step inp)^[t] P.init

def time (P : TapeProgram R B L) (inp : Inputs) : ℕ → ℕ
  | 0 => 0
  | t+1 => P.time inp t + P.cost (P.run inp t)

 



 








 



 





end TapeProgram
end ExpandingCodes.Computation

end FlattenModule5


section FlattenModule6


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB





















namespace CounterProgram
variable {R L : ℕ}











































 



 








 



 





end CounterProgram
end ExpandingCodes.Computation

end FlattenModule6

/-! Inlined whole module: ExpandingCodes.Computation.CounterTape -/
section FlattenModule7


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Tape equality ignores the finite list's trailing blank storage. -/
def TapeRep (l : List Sym) (f : ℕ → Sym) : Prop :=
  ∀ k, l.getD k Sym.blank = f k

 



















 





 



/-- A counter occupies one tape, with a bottom marker at zero and its head at its value. -/
def unary (n k : ℕ) : Sym :=
  if k = 0 then .bot else if k ≤ n then .one else .blank





 







 







 


























































 





 












end ExpandingCodes.Computation

end FlattenModule7


section FlattenModule8


set_option autoImplicit false
open scoped Classical

namespace NKtLB.Machine















































end NKtLB.Machine

end FlattenModule8

/-! Inlined whole module: ExpandingCodes.Computation.CounterCompiler -/
section FlattenModule9




set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Two banks of instruction labels (ordinary and increment completion), plus
start, halt, and an unreachable oracle-query state. -/
abbrev CounterControl (L : ℕ) := (Fin L ⊕ Fin L) ⊕ Fin 3

namespace CounterCompiler
variable {R L : ℕ}

def controlEquiv (L : ℕ) : CounterControl L ≃ Fin (L+L+3) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 3))).trans finSumFinEquiv

def startControl : CounterControl L := .inr 0
def haltControl : CounterControl L := .inr 1
def queryControl : CounterControl L := .inr 2
def normal (j : Fin L) : CounterControl L := .inl (.inl j)
def finish (j : Fin L) : CounterControl L := .inl (.inr j)



























































 




 










 



 































 




 












 












































 







 



























 




























 





 


 theorem getD_append_singleton (l : List Sym) (a : Sym) (k : ℕ) :
    (l ++ [a]).getD k .blank = if k = l.length then a else l.getD k .blank := by
  by_cases hk : k < l.length
  · rw [List.getD_append _ _ _ _ hk, if_neg (by omega)]
  · by_cases he : k = l.length
    · subst k
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · rw [List.getD_eq_default (l ++ [a]) .blank (by simp; omega), if_neg he,
        List.getD_eq_default l .blank (by omega)]

 































 






























 











































 

















 




 




































 












































 








end CounterCompiler
end ExpandingCodes.Computation

end FlattenModule9

/-! Inlined whole module: ExpandingCodes.Computation.TapeCompiler -/
section FlattenModule10



set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeCompiler
open CounterCompiler (controlEquiv startControl haltControl queryControl normal finish
  getD_append_singleton )
variable {R B L : ℕ}

def workIdx (B : ℕ) (r : Fin R) : Fin (R+B+2) := ⟨r.val, by omega⟩
def outIdx (R B : ℕ) : Fin (R+B+2) := ⟨R+B, by omega⟩

/-- Buffer cells have distinct physical tapes after the unary counter tapes. -/
def bufferIdx (R : ℕ) (b : Fin B) : Fin (R+B+2) := ⟨R+b.val, by omega⟩

 





 


 





 





def target (P : TapeProgram R B L) (j : Fin L) : CounterControl L :=
  match P.code j with
  | .halt => haltControl
  | _ => normal j

def idle (rw : Fin (R+B+2) → Sym) : Fin (R+B+2) → Sym × Move :=
  fun k => (rw k, .stay)

def roIdle : Fin 4 → Move := fun _ => .stay

/-- A literal finite transition table over the four scanned symbols. The
`next : Sym → Fin L` field of a read instruction is just a four-entry branch table. -/
def transition (P : TapeProgram R B L) (q : CounterControl L)
    (ro : Fin 4 → Sym) (rw : Fin (R+B+2) → Sym) :
    CounterControl L × (Fin 4 → Move) × (Fin (R+B+2) → Sym × Move) :=
  match q with
  | .inr s =>
    if s = 0 then
      (target P P.entry, roIdle, fun k =>
        if k.val < R then (.bot, .stay) else (rw k, .stay))
    else (haltControl, roIdle, idle rw)
  | .inl (.inr j) =>
    match P.code j with
    | .inc r next => (target P next, roIdle,
        Function.update (idle rw) (workIdx B r) (.one, .stay))
    | _ => (haltControl, roIdle, idle rw)
  | .inl (.inl j) =>
    match P.code j with
    | .halt => (haltControl, roIdle, idle rw)
    | .jump next => (target P next, roIdle, idle rw)
    | .inc r _ => (finish j, roIdle,
        Function.update (idle rw) (workIdx B r) (rw (workIdx B r), .right))
    | .dec r zero positive =>
      if rw (workIdx B r) = .bot then (target P zero, roIdle, idle rw)
      else (target P positive, roIdle,
        Function.update (idle rw) (workIdx B r) (.blank, .left))
    | .emit b next => (target P next, roIdle,
        Function.update (idle rw) (outIdx R B) (Sym.ofBool b, .right))
    | .read r next =>
      (target P (next (ro r)), Function.update roIdle r .right, idle rw)
    | .buffer b action =>
      let a := action (rw (bufferIdx R b))
      (target P a.2.2, roIdle,
        Function.update (idle rw) (bufferIdx R b) (a.1, a.2.1))

/-- Compiles every finite tape program to the exact canonical NKtLB machine.
No oracle, arithmetic, or unbounded memory action occurs in its transition table. -/
abbrev compile (P : TapeProgram R B L) : Machine where
  nStates := L+L+3
  start := controlEquiv L startControl
  halt := controlEquiv L haltControl
  query := controlEquiv L queryControl
  qyes := controlEquiv L haltControl
  qno := controlEquiv L haltControl
  works := R+B
  δ := fun q ro rw =>
    let a := transition P ((controlEquiv L).symm q) ro rw
    (controlEquiv L a.1, a.2)

 




 










 



 




















/-- The exact relation required at instruction boundaries. Work tapes use the
proved unary invariant; buffers and output are represented extensionally, so
trailing-blank storage never changes the represented data. -/
structure Represents (P : TapeProgram R B L) (c : TapeCfg R B L)
    (m : Machine.Cfg (compile P)) : Prop where
  state : m.state = controlEquiv L (target P c.pc)
  roHead : m.roHead = c.roHead
  workHead : ∀ r, m.rwHead (workIdx B r) = c.reg r
  workTape : ∀ r, TapeRep (m.rwTape (workIdx B r)) (unary (c.reg r))
  outHead : m.rwHead (outIdx R B) = c.output.length
  outTape : TapeRep (m.rwTape (outIdx R B)) (fun k => (bitsSym c.output).getD k .blank)
  bufferHead : ∀ b, m.rwHead (bufferIdx R b) = c.bufferHead b
  bufferTape : ∀ b, TapeRep (m.rwTape (bufferIdx R b)) (fun k => (c.bufferTape b).getD k .blank)

 




 




/-- A finite local proof obligation: simulate each of the seven instruction forms,
with the two-action increment distinguished from the one-action instructions. -/
def LocalSimulation (P : TapeProgram R B L) : Prop :=
  ∀ (O : Set (List Bool)) (inp : Inputs) (c : TapeCfg R B L)
    (m : Machine.Cfg (compile P)),
    Represents P c m →
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m)

 

















































 







 
































 

































 





 


 




































 



































 
















































 

















 
























































































 













































 








end TapeCompiler
end ExpandingCodes.Computation

end FlattenModule10

/-! Inlined whole module: ExpandingCodes.Computation.TapeLoops -/
section FlattenModule11


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Data carried between finite source-program fragments. -/
structure TapeStore (R B : ℕ) where
  reg : Fin R → ℕ
  roHead : Fin 4 → ℕ
  output : List Bool
  bufferTape : Fin B → List Sym
  bufferHead : Fin B → ℕ

namespace TapeCfg
variable {R B L K : ℕ}

abbrev store (c : TapeCfg R B L) : TapeStore R B := ⟨c.reg, c.roHead, c.output, c.bufferTape, c.bufferHead⟩

abbrev mapPC (f : Fin L → Fin K) (c : TapeCfg R B L) : TapeCfg R B K :=
  ⟨f c.pc, c.reg, c.roHead, c.output, c.bufferTape, c.bufferHead⟩
end TapeCfg

namespace TapeStore
variable {R B L : ℕ}

abbrev toCfg (d : TapeStore R B) (j : Fin L) : TapeCfg R B L :=
  ⟨j, d.reg, d.roHead, d.output, d.bufferTape, d.bufferHead⟩




end TapeStore

namespace TapeInstr
variable {R B L K : ℕ}

/-- Relabels finite jump destinations; it adds no machine operation. -/
def relabel (f : Fin L → Fin K) : TapeInstr R B L → TapeInstr R B K
  | .halt => .halt
  | .jump j => .jump (f j)
  | .inc r j => .inc r (f j)
  | .dec r z p => .dec r (f z) (f p)
  | .emit b j => .emit b (f j)
  | .read r next => .read r (f ∘ next)
  | .buffer b action => .buffer b (fun x => let a := action x; (a.1, a.2.1, f a.2.2))

 


end TapeInstr

namespace TapeProgram
variable {R B L K : ℕ}

/-- A finite active execution prefix. It records exactly the actual instructions
executed, excluding extra repetitions of the source's absorbing halt. -/
inductive Exec (P : TapeProgram R B L) (inp : Inputs) :
    TapeCfg R B L → ℕ → TapeCfg R B L → Prop where
  | refl (c) : Exec P inp c 0 c
  | step {c d e t} (active : ¬ P.halted c) (next : P.step inp c = d)
      (tail : Exec P inp d t e) : Exec P inp c (t+1) e

/-- An active source execution ending at a halt instruction. -/
structure Stops (P : TapeProgram R B L) (inp : Inputs)
    (c : TapeCfg R B L) (t : ℕ) (d : TapeCfg R B L) : Prop where
  exec : P.Exec inp c t d
  halted : P.halted d

 








 



 







 


































/-- Constructive inclusions into the disjoint union of two finite code tables. -/
def leftLabel (K : ℕ) (j : Fin L) : Fin (L+K) := finSumFinEquiv (.inl j)
def rightLabel (L : ℕ) (j : Fin K) : Fin (L+K) := finSumFinEquiv (.inr j)

/-- Finite program sequencing. Each halt in the first fragment becomes one jump
into the second fragment; all other instructions are copied with relabeled targets. -/
def seq (P : TapeProgram R B L) (Q : TapeProgram R B K) : TapeProgram R B (L+K) where
  entry := leftLabel K P.entry
  code := fun j => match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (rightLabel L Q.entry)
      | a => a.relabel (leftLabel K)
    | .inr i => (Q.code i).relabel (rightLabel L)

 




 




 
























/-- A syntactic sufficient condition for an instruction to preserve a register. -/
def preservesRegister (r : Fin R) : TapeInstr R B L → Prop
  | .inc s _ => s ≠ r
  | .dec s _ _ => s ≠ r
  | _ => True

/-- A loop counter is fresh when the body never increments or decrements it. -/
def Fresh (P : TapeProgram R B L) (r : Fin R) : Prop :=
  ∀ j, preservesRegister r (P.code j)

 








 








/-- The body occupies the first L labels, followed by a decrement/test header and halt exit. -/
def loopHeader (L : ℕ) : Fin (L+2) := rightLabel L (0 : Fin 2)
def loopExit (L : ℕ) : Fin (L+2) := rightLabel L (1 : Fin 2)

def countedLoop (P : TapeProgram R B L) (r : Fin R) : TapeProgram R B (L+2) where
  entry := loopHeader L
  code := fun j => match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (loopHeader L)
      | a => a.relabel (leftLabel 2)
    | .inr i => if i = 0 then .dec r (loopExit L) (leftLabel 2 P.entry) else .halt

 




 




 



 



/-- Store after the loop's positive decrement instruction. -/
abbrev decStore (r : Fin R) (d : TapeStore R B) : TapeStore R B :=
  { d with reg := Function.update d.reg r (d.reg r - 1) }

 










 









 









































end TapeProgram
end ExpandingCodes.Computation

end FlattenModule11

/-! Inlined whole module: ExpandingCodes.Computation.TapeMacros -/
section FlattenModule12


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeStore
variable {R B : ℕ}

/-- Update one bounded unary counter, carrying all tapes and heads unchanged. -/
def setReg (d : TapeStore R B) (r : Fin R) (n : ℕ) : TapeStore R B :=
  { d with reg := Function.update d.reg r n }





end TapeStore

namespace TapeMacros
variable {R B : ℕ}

/-- One actual increment instruction followed by a halt. -/
def increment (r : Fin R) : TapeProgram R B 2 where
  entry := 0
  code j := if j = 0 then .inc r 1 else .halt

 







/-- Repeated decrement/tests erase a unary counter. -/
def clear (r : Fin R) : TapeProgram R B 2 where
  entry := 0
  code j := if j = 0 then .dec r 1 0 else .halt

 






















/-- Destructive unary addition: each unit of src is decremented and then added
to dst. The entire variable-length data payload remains on explicit buffers. -/
def transfer (src dst : Fin R) : TapeProgram R B 3 where
  entry := 0
  code j := if j = 0 then .dec src 2 1 else if j = 1 then .inc dst 0 else .halt

/-- Exact transfer post-store, including the zeroed source. -/
def transferStore (d : TapeStore R B) (src dst : Fin R) : TapeStore R B :=
  (d.setReg src 0).setReg dst (d.reg dst + d.reg src)

 
















 

































/-- Move each source unit to two distinct destinations using three instructions. -/
def distribute (src dst tmp : Fin R) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .dec src 3 1 else if j = 1 then .inc dst 2
    else if j = 2 then .inc tmp 0 else .halt

def distributeStore (d : TapeStore R B) (src dst tmp : Fin R) : TapeStore R B :=
  ((d.setReg src 0).setReg dst (d.reg dst + d.reg src)).setReg tmp (d.reg tmp + d.reg src)

 






















 







































/-- Copy through a scratch unary counter. Destination and scratch are first
cleared; all four phases are finite code tables, joined by three actual jumps. -/
def copy (src dst tmp : Fin R) : TapeProgram R B 11 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (clear dst) (clear tmp))
    (distribute src dst tmp)) (transfer tmp src)

 

















 























/-- Unary addition preserving its source, using one scratch counter. -/
def addPreserving (src dst tmp : Fin R) : TapeProgram R B 9 :=
  TapeProgram.seq (TapeProgram.seq (clear tmp) (distribute src dst tmp)) (transfer tmp src)

 

















 



















/-- A finite one-cell table followed by halt. This exposes no whole-buffer access. -/
def cell (b : Fin B) (action : Sym → Sym × Move) : TapeProgram R B 2 where
  entry := 0
  code j := if j = 0 then .buffer b (fun s => ((action s).1, (action s).2, 1)) else .halt

def cellStore (d : TapeStore R B) (b : Fin B) (action : Sym → Sym × Move) : TapeStore R B :=
  let a := action ((d.bufferTape b).getD (d.bufferHead b) .blank)
  { d with
    bufferTape := Function.update d.bufferTape b
      (Machine.writeAt (d.bufferTape b) (d.bufferHead b) a.1)
    bufferHead := Function.update d.bufferHead b (Machine.moveHead a.2 (d.bufferHead b)) }

 











/-- One explicit constant-symbol write and unit head move. -/
def write (b : Fin B) (s : Sym) (m : Move := .stay) : TapeProgram R B 2 :=
  cell b (fun _ => (s,m))







end TapeMacros
end ExpandingCodes.Computation

end FlattenModule12

/-! Inlined whole module: ExpandingCodes.Computation.UnaryArithmetic -/
section FlattenModule13


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace UnaryArithmetic
variable {R B : ℕ}
















/-- The code table has eleven labels regardless of the runtime operands. -/
def mulLoop (a dst tmp count : Fin R) : TapeProgram R B 11 :=
  TapeProgram.countedLoop (TapeMacros.addPreserving a dst tmp) count

def mulLoopStore (d : TapeStore R B) (a dst tmp count : Fin R) (n : ℕ) : TapeStore R B :=
  ((d.setReg count 0).setReg dst (d.reg dst + n*d.reg a)).setReg tmp 0























































































/-- Uniform multiplication by repeated addition, with operands preserved. Scratch
registers hold only single unary values, and all buffer contents are unchanged. -/
def multiply (a b dst tmp count : Fin R) : TapeProgram R B 24 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear dst) (TapeMacros.copy b count tmp))
    (mulLoop a dst tmp count)

def multiplyStore (d : TapeStore R B) (a b dst tmp count : Fin R) : TapeStore R B :=
  ((d.setReg dst (d.reg a*d.reg b)).setReg tmp 0).setReg count 0





































































/-- Peel pairs from one unary counter. This is a fixed five-label code table;
the two outputs accumulate quotient and parity, respectively. -/
def halveLoop (src quotient parity : Fin R) : TapeProgram R B 5 where
  entry := 0
  code j := if j = 0 then .dec src 4 1 else if j = 1 then .dec src 3 2
    else if j = 2 then .inc quotient 0 else if j = 3 then .inc parity 4 else .halt

def halveStore (d : TapeStore R B) (src quotient parity : Fin R) (n : ℕ) : TapeStore R B :=
  ((d.setReg src 0).setReg quotient (d.reg quotient+n/2)).setReg parity (d.reg parity+n%2)





















































































end UnaryArithmetic
end ExpandingCodes.Computation

end FlattenModule13

/-! Inlined whole module: ExpandingCodes.Computation.TapeArrays -/
section FlattenModule14



set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeStore
variable {R B : ℕ}

/-- Payload equality is extensional: physical finite lists may acquire trailing
blank cells during an idle write without changing any observable tape symbol. -/
structure SamePayload (d e : TapeStore R B) : Prop where
  roHead : d.roHead = e.roHead
  output : d.output = e.output
  symbol : ∀ b k, (d.bufferTape b).getD k .blank = (e.bufferTape b).getD k .blank

 


 



 

end TapeStore

namespace TapeArrays
variable {R B : ℕ}
open TapeMacros

/-- One preserving-symbol move, including the actual finite-list write performed
by the source instruction. -/
abbrev moved (d : TapeStore R B) (b : Fin B) (m : Move) : TapeStore R B :=
  cellStore d b (fun s => (s,m))

 


















/-- A real charged right seek. Every unit consumes one counter decrement and
one cell move. It does not assume constant-time indexing. -/
def seekRight (r : Fin R) (b : Fin B) : TapeProgram R B 3 where
  entry := 0
  code j := if j = 0 then .dec r 2 1 else if j = 1 then
    .buffer b (fun s => (s, .right, 0)) else .halt

 



































/-- Reset scans left until the reserved bottom marker, with no lookahead or
whole-buffer primitive. The marker is inspected once before halting. -/
def reset (b : Fin B) : TapeProgram R B 2 where
  entry := 0
  code j := if j = 0 then .buffer b (fun s => if s = .bot then (s,.stay,1) else (s,.left,0))
    else .halt

/-- The active prefix down to cell zero contains exactly one bottom marker. -/
def Marked (d : TapeStore R B) (b : Fin B) : Prop :=
  (d.bufferTape b).getD 0 .blank = .bot ∧
    ∀ k, 0 < k → k ≤ d.bufferHead b → (d.bufferTape b).getD k .blank ≠ .bot

 





























































 





























 






















 








 









 










 










































/-- One physical constant write and right move. -/
abbrev painted (d : TapeStore R B) (b : Fin B) (s : Sym) : TapeStore R B :=
  cellStore d b (fun _ => (s,.right))

/-- Repeated writes, used only as a data specification of the finite programs. -/
def fillStore (b : Fin B) (s : Sym) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => fillStore b s n (painted d b s)

 





 





 





 







 




























/-- Write as many identical cells as the unary counter specifies. -/
def writeRun (r : Fin R) (b : Fin B) (s : Sym) : TapeProgram R B 3 where
  entry := 0
  code j := if j = 0 then .dec r 2 1 else if j = 1 then .buffer b (fun _ => (s,.right,0))
    else .halt

 




























/-- Each written cell additionally decrements a distinct width counter. The
width decrement saturates at zero, so the code has total semantics for all stores. -/
def writeDebit (value width : Fin R) (b : Fin B) (s : Sym) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .dec value 3 1 else if j = 1 then .dec width 2 2
    else if j = 2 then .buffer b (fun _ => (s,.right,0)) else .halt

 



















































/-- q-cell thermometer write: the first value cells are one, and the remaining
width-value cells are zero. Both unary input counters are consumed. -/
def writeBlock (value width : Fin R) (b : Fin B) : TapeProgram R B 7 :=
  TapeProgram.seq (writeDebit value width b .one) (writeRun width b .zero)

def writeBlockStore (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) : TapeStore R B :=
  fillStore b .zero (w-v) ((fillStore b .one v
    ((d.setReg value 0).setReg width (w-v))).setReg width 0)

 














/-- One field/hash value occupies a fixed width of physical bit cells. -/
def ThermometerAt (d : TapeStore R B) (b : Fin B) (start width value : ℕ) : Prop :=
  value ≤ width ∧ ∀ j, j < width →
    (d.bufferTape b).getD (start+j) .blank = if j < value then .one else .zero

 




 






 



 



 













 

























/-- Read a fixed-width thermometer entry by explicitly scanning every cell and
incrementing the value counter once for each one. -/
def readBlock (width value : Fin R) (b : Fin B) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .dec width 3 1
    else if j = 1 then .buffer b (fun s => (s,.right, if s = .one then 2 else 0))
    else if j = 2 then .inc value 0 else .halt

/-- Value added by the one scanned symbol in a read iteration. -/
def readDelta (d : TapeStore R B) (b : Fin B) : ℕ :=
  if (d.bufferTape b).getD (d.bufferHead b) .blank = .one then 1 else 0

def readTickStore (width value : Fin R) (b : Fin B) (d : TapeStore R B) : TapeStore R B :=
  let e := moved (TapeProgram.decStore width d) b .right
  if (d.bufferTape b).getD (d.bufferHead b) .blank = .one then
    e.setReg value (d.reg value+1) else e

 








 





 









 































 























































/-- Physical entries begin after the reserved bottom marker. The offset is an
individual bounded unary register; construction of 1+i*width is charged separately. -/
def entryOffset (i width : ℕ) : ℕ := 1+i*width

/-- Reset and then traverse exactly the supplied unary offset. -/
def seekEntry (offset : Fin R) (b : Fin B) : TapeProgram R B 5 :=
  TapeProgram.seq (reset b) (seekRight offset b)

 


















/-- A table is physically present in successive fixed-width bit blocks. This
is a specification over explicit buffer cells, not a new array instruction. -/
def ThermometerTable {N : ℕ} (d : TapeStore R B) (b : Fin B) (width : ℕ)
    (values : Fin N → ℕ) : Prop :=
  ∀ i, ThermometerAt d b (entryOffset i.val width) width (values i)

 







/-- Full physical indexing: multiply individual index/width counters, add the
marker offset, reset, and traverse. There is no uncharged random-access operation. -/
def positionEntry (index width offset tmp count : Fin R) (b : Fin B) : TapeProgram R B 31 :=
  TapeProgram.seq (TapeProgram.seq
    (UnaryArithmetic.multiply index width offset tmp count) (TapeMacros.increment offset))
    (seekEntry offset b)

 




































































 





















/-- Proved source-step budget for multiplication, marker offset and charged seek. -/
def positionBound (d : TapeStore R B) (index width offset tmp count : Fin R) (b : Fin B) : ℕ :=
  d.reg offset+d.reg count+d.reg tmp+5*d.reg width+
    d.reg width*(5*d.reg index+7)+11+d.bufferHead b+
    2*entryOffset (d.reg index) (d.reg width)+6

/-- A common loose budget for either complete indexed read or indexed write. -/
def entryAccessBound (d : TapeStore R B) (index width offset tmp count : Fin R) (b : Fin B) : ℕ :=
  positionBound d index width offset tmp count b+3*d.reg width+4

 









/-- A complete physical array read. The width register is consumed and the
value accumulator must start at zero; every indexed traversal is real code. -/
def readEntry (index width offset tmp count value : Fin R) (b : Fin B) : TapeProgram R B 35 :=
  TapeProgram.seq (positionEntry index width offset tmp count b) (readBlock width value b)

 















































/-- Complete extensional effect of one physical field/hash entry overwrite. -/
structure EntryWritten (d e : TapeStore R B) (b : Fin B) (start width value : ℕ) : Prop where
  roHead : e.roHead = d.roHead
  output : e.output = d.output
  head : e.bufferHead = Function.update d.bufferHead b (start+width)
  symbol : ∀ c k, (e.bufferTape c).getD k .blank =
    if c = b ∧ start ≤ k ∧ k < start+width then
      if k < start+value then .one else .zero
    else (d.bufferTape c).getD k .blank

/-- A complete physical indexed array write, including offset multiplication. -/
def writeEntry (index width offset tmp count value : Fin R) (b : Fin B) : TapeProgram R B 38 :=
  TapeProgram.seq (positionEntry index width offset tmp count b) (writeBlock value width b)

 



















































/-- A reserved bottom marker with no other bottom symbols on this buffer. This
invariant permits reset after arbitrary indexed reads and thermometer writes. -/
def BottomMarked (d : TapeStore R B) (b : Fin B) : Prop :=
  (d.bufferTape b).getD 0 .blank = .bot ∧
    ∀ k, 0 < k → (d.bufferTape b).getD k .blank ≠ .bot

 


 








 












/-- Install the reserved marker using one actual cell write. -/
def initializeBuffer (b : Fin B) : TapeProgram R B 2 := TapeMacros.write b .bot .right

 


















































end TapeArrays
end ExpandingCodes.Computation





















end FlattenModule14

/-! Inlined whole module: ExpandingCodes.Computation.TapeControl -/
section FlattenModule15


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace TapeProgram
variable {R B L K : ℕ}

def branchLeft (K : ℕ) (i : Fin L) : Fin (L+K+2) := leftLabel 2 (leftLabel K i)
def branchRight (L : ℕ) (i : Fin K) : Fin (L+K+2) := leftLabel 2 (rightLabel L i)
def branchTest (L K : ℕ) : Fin (L+K+2) := rightLabel (L+K) (0 : Fin 2)
def branchRestore (L K : ℕ) : Fin (L+K+2) := rightLabel (L+K) (1 : Fin 2)

/-- A physical zero test followed by one of two finite programs. A positive
counter is restored by an actual increment before entering its branch. -/
def branchZero (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    TapeProgram R B (L+K+2) where
  entry := branchTest L K
  code j := match finSumFinEquiv.symm j with
    | .inl p => match finSumFinEquiv.symm p with
      | .inl i => (P.code i).relabel (branchLeft K)
      | .inr i => (Q.code i).relabel (branchRight L)
    | .inr c => if c = 0 then
        .dec r (branchLeft K P.entry) (branchRestore L K)
      else .inc r (branchRight L Q.entry)















































































def skip : TapeProgram R B 1 where
  entry := 0
  code _ := .halt








end TapeProgram
end ExpandingCodes.Computation

end FlattenModule15

/-! Inlined whole module: ExpandingCodes.Computation.FieldPrograms -/
section FlattenModule16


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace FieldPrograms
open UnaryArithmetic
variable {R B : ℕ}

/-- Destructive division by two and parity. All operands and bounds are runtime
counter values; this nine-label table is independent of field size. -/
def halve (src quotient parity : Fin R) : TapeProgram R B 9 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear quotient) (TapeMacros.clear parity))
    (halveLoop src quotient parity)

def halfStore (d : TapeStore R B) (src quotient parity : Fin R) : TapeStore R B :=
  ((d.setReg src 0).setReg quotient (d.reg src/2)).setReg parity (d.reg src%2)






































/-- One right shift: pair peeling followed by actual unary transfer of its
quotient into the input counter. -/
def halfStep (src quotient parity : Fin R) : TapeProgram R B 12 :=
  TapeProgram.seq (halve src quotient parity) (TapeMacros.transfer quotient src)

def halfStepStore (d : TapeStore R B) (src quotient parity : Fin R) : TapeStore R B :=
  ((d.setReg src (d.reg src/2)).setReg quotient 0).setReg parity (d.reg src%2)






































def shiftRight (src quotient parity count : Fin R) : TapeProgram R B 14 :=
  TapeProgram.countedLoop (halfStep src quotient parity) count

/-- Exact store semantics of the finite pair-peeling loop. This recursive value
is used only in the specification; the machine code above is a fixed table. -/
def shiftStore (src quotient parity count : Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d.setReg count 0
  | n+1, d => shiftStore src quotient parity count n
      (halfStepStore (d.setReg count n) src quotient parity)























































































































/-- Registers 0 and 1 contain the preserved input and bit index; register 4 is
the output bit. Registers 2,3,5,6 are unary scratch, never packed arrays. -/
def testBit (r : Fin 7 → Fin R) : TapeProgram R B 45 :=
  TapeProgram.seq
    (TapeProgram.seq
      (TapeProgram.seq (TapeMacros.copy (r 0) (r 2) (r 6)) (TapeMacros.copy (r 1) (r 5) (r 6)))
      (shiftRight (r 2) (r 3) (r 4) (r 5)))
    (halve (r 2) (r 3) (r 4))

def bitPrepare (r : Fin 7 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 2) (d.reg (r 0))).setReg (r 6) 0
  (d₁.setReg (r 5) (d₁.reg (r 1))).setReg (r 6) 0

def testBitStore (r : Fin 7 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  halfStore
    (shiftStore (r 2) (r 3) (r 4) (r 5) (d.reg (r 1)) (bitPrepare r d))
    (r 2) (r 3) (r 4)




























































































end FieldPrograms
end ExpandingCodes.Computation

end FlattenModule16

/-! Inlined whole module: ExpandingCodes.Computation.ParameterPrograms -/
section FlattenModule17


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- A fixed string of increments. Its length depends only on the program's
static parameter, never on a runtime input or field size. -/
def raiseLabels : ℕ → ℕ
  | 0 => 1
  | c+1 => 2 + raiseLabels c

def raise (r : Fin R) : (c : ℕ) → TapeProgram R B (raiseLabels c)
  | 0 => { entry := ⟨0, by simp [raiseLabels]⟩, code := fun _ => .halt }
  | c+1 => TapeProgram.seq (TapeMacros.increment r) (raise r c)



















/-- Clear followed by a statically fixed number of actual increments. -/
def loadConstant (r : Fin R) (c : ℕ) : TapeProgram R B (2+raiseLabels c) :=
  TapeProgram.seq (TapeMacros.clear r) (raise r c)













/-- Destructive comparison of two unary counters. The destination receives one
exactly when the original first counter is smaller than the second counter. -/
def ltLoop (a b dst : Fin R) : TapeProgram R B 5 where
  entry := 0
  code j := if j = 0 then .dec b 4 1 else if j = 1 then .dec a 3 0
    else if j = 3 then .inc dst 4 else .halt

def ltLoopStore (a b dst : Fin R) (m n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg a (m-n)).setReg b (n-(m+1))).setReg dst
    (d.reg dst + if m<n then 1 else 0)





















































































/-- Preserving comparison: registers 0,1 are inputs; 2 is the output; 3,4,5
are scratch. Every scratch register is zero at return. This 33-label code table
is independent of the runtime operand values. -/
def lessThan (r : Fin 6 → Fin R) : TapeProgram R B 33 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (TapeMacros.copy (r 0) (r 3) (r 5))
      (TapeMacros.copy (r 1) (r 4) (r 5))) (TapeMacros.clear (r 2)))
      (ltLoop (r 3) (r 4) (r 2))) (TapeMacros.clear (r 3)))
      (TapeMacros.clear (r 4))









def lessPrepare (r : Fin 6 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 3) (d.reg (r 0))).setReg (r 5) 0
  let d₂ := (d₁.setReg (r 4) (d₁.reg (r 1))).setReg (r 5) 0
  d₂.setReg (r 2) 0

def lessCore (r : Fin 6 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ltLoopStore (r 3) (r 4) (r 2) (d.reg (r 0)) (d.reg (r 1)) (lessPrepare r d)

def lessThanStore (r : Fin 6 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((lessCore r d).setReg (r 3) 0).setReg (r 4) 0



























































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule17


section FlattenModule18


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch
































































end ExpandingCodes.PolynomialStretch

end FlattenModule18


section FlattenModule19



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch






























































end ExpandingCodes.PolynomialStretch

end FlattenModule19


section FlattenModule20


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





































































































end ExpandingCodes.PolynomialStretch

end FlattenModule20

/-! Inlined whole module: ExpandingCodes.Computation.RandomBits -/
section FlattenModule21




set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ExpandingCodes.Computation
open NKtLB

namespace RandomBits
variable {R B : ℕ}

/-- Six fixed source registers. Their contents, including ell and q, are runtime data. -/
structure Layout (R : ℕ) where
  reg : Fin 6 ↪ Fin R

abbrev Layout.ell (l : Layout R) := l.reg 0
abbrev Layout.q (l : Layout R) := l.reg 1
abbrev Layout.acc (l : Layout R) := l.reg 2
abbrev Layout.count (l : Layout R) := l.reg 3
abbrev Layout.tmp (l : Layout R) := l.reg 4
abbrev Layout.scratch (l : Layout R) := l.reg 5




/-- A symbol outside the fair-bit pre is interpreted as zero. The read is
still an actual single-cell read and advances the RO randomness head once. -/
def bitAt (inp : Inputs) (h : ℕ) : Bool :=
  decide (Machine.readRO inp.rand h = .one)

def bitNat (b : Bool) : ℕ := if b then 1 else 0

/-- Constant two-instruction read, with one branch adding one and the other
executing a jump. No input size enters the code table. -/
def readBit (a : Fin R) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .read 3 (fun s => if s = .one then 1 else 2)
    else if j = 1 then .inc a 3 else if j = 2 then .jump 3 else .halt

def readBitStore (a : Fin R) (inp : Inputs) (d : TapeStore R B) : TapeStore R B :=
  { d.setReg a (d.reg a + bitNat (bitAt inp (d.roHead 3))) with
    roHead := Function.update d.roHead 3 (d.roHead 3 + 1) }

 




















/-- Actual unary doubling: copy accumulator into a temporary, then transfer it
back. The preserving-copy macro uses the third unary scratch register. -/
def double (l : Layout R) : TapeProgram R B 14 :=
  TapeProgram.seq (TapeMacros.copy l.acc l.tmp l.scratch) (TapeMacros.transfer l.tmp l.acc)

def doubleStore (l : Layout R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg l.acc (2*d.reg l.acc)).setReg l.tmp 0).setReg l.scratch 0

 




















 


















/-- One binary Horner step a := 2*a + nextBit. -/
def nextBit (l : Layout R) : TapeProgram R B 18 :=
  TapeProgram.seq (double l) (readBit l.acc)

def nextBitStore (l : Layout R) (inp : Inputs) (d : TapeStore R B) : TapeStore R B :=
  readBitStore l.acc inp (doubleStore l d)

 












/-- Explicit numerical semantics of successive most-significant-first reads. -/
def value (inp : Inputs) : ℕ → ℕ → ℕ → ℕ
  | 0, _, a => a
  | n+1, h, a => value inp n (h+1) (2*a+bitNat (bitAt inp h))

 theorem value_lt (inp : Inputs) (n h a : ℕ) :
    value inp n h a < 2^n*(a+1) := by
  induction n generalizing h a with
  | zero => simp [value]
  | succ n ih =>
    have hi := ih (h+1) (2*a+bitNat (bitAt inp h))
    have hb : bitNat (bitAt inp h) ≤ 1 := by unfold bitNat; split <;> omega
    rw [value]
    apply hi.trans_le
    rw [pow_succ]
    nlinarith

/-- Exact data semantics of a counted sequence of finite Horner steps. -/
def bitsStore (l : Layout R) (inp : Inputs) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => bitsStore l inp n (nextBitStore l inp (TapeProgram.decStore l.count d))

def bitsTime (l : Layout R) (inp : Inputs) : ℕ → TapeStore R B → ℕ
  | 0, _ => 1
  | n+1, d => d.reg l.tmp+d.reg l.scratch+7*d.reg l.acc+14 +
      bitsTime l inp n (nextBitStore l inp (TapeProgram.decStore l.count d))

/-- Fixed finite random-read loop; its number of labels is independent of ell. -/
def readBits (l : Layout R) : TapeProgram R B 20 :=
  TapeProgram.countedLoop (nextBit l) l.count

 



















 







 































 








 
















 









 







 








 








 






























/-- Clear the accumulator and doubling temporary after copying runtime ell
into the loop counter. The original ell and q registers are preserved. -/
def prepare (l : Layout R) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy l.ell l.count l.scratch)
    (TapeMacros.clear l.acc)) (TapeMacros.clear l.tmp)

def prepareStore (l : Layout R) (d : TapeStore R B) : TapeStore R B :=
  (((d.setReg l.count (d.reg l.ell)).setReg l.scratch 0).setReg l.acc 0).setReg l.tmp 0

 

























/-- The complete finite random-index routine (35 labels). All variable sizes
are stored in runtime registers; only six register addresses enter the code. -/
def randomIndex (l : Layout R) : TapeProgram R B 35 :=
  TapeProgram.seq (prepare l) (readBits l)

def indexStore (l : Layout R) (inp : Inputs) (d : TapeStore R B) : TapeStore R B :=
  bitsStore l inp (d.reg l.ell) (prepareStore l d)

 





























 




 




 




 





 





 




 




 




 



















open scoped BigOperators
open ExpandingCodes.PolynomialStretch

/-- A finite equivalence from the read order of ell fair coins to the index
order of the explicit binary-polynomial coefficient representation. -/
def reverseBits (ell : ℕ) : (Fin ell → Bool) ≃ (Fin ell → Bool) where
  toFun x j := x j.rev
  invFun x j := x j.rev
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

def bitsIndexEquiv (ell : ℕ) : (Fin ell → Bool) ≃ Fin (2^ell) :=
  (reverseBits ell).trans
    ((BinaryPolynomial.bitsEquiv ell).trans (BinaryPolynomial.indexEquiv ell).symm)

 














 


























 












 


































 

































end RandomBits
end ExpandingCodes.Computation

end FlattenModule21

/-! Inlined whole module: ExpandingCodes.Computation.RandomTables -/
section FlattenModule22



set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ExpandingCodes.Computation
open NKtLB
namespace RandomTables
variable {R B : ℕ}

/-- One more runtime register supplies the number of table entries. -/
structure Layout (R : ℕ) where
  random : RandomBits.Layout R
  count : Fin R
  fresh : ∀ j, random.reg j ≠ count

/-- One actual random index, an actual preserving copy of q, then a physical
q-cell thermometer write. All sizes remain data in unary registers. -/
def entry (l : RandomBits.Layout R) (b : Fin B) : TapeProgram R B 53 :=
  TapeProgram.seq (TapeProgram.seq (RandomBits.randomIndex l)
    (TapeMacros.copy l.q l.count l.scratch)) (TapeArrays.writeBlock l.acc l.count b)

def entryStore (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) : TapeStore R B :=
  let c := RandomBits.indexStore l inp d
  TapeArrays.writeBlockStore l.acc l.count b (c.reg l.acc) (d.reg l.q)
    ((c.setReg l.count (d.reg l.q)).setReg l.scratch 0)

def entryBound (q : ℕ) : ℕ := (q+1)*(7*q+30)+8*q+12

 








































/-- The source loop has 55 labels for every runtime table length and width. -/
def fill (l : Layout R) (b : Fin B) : TapeProgram R B 55 :=
  TapeProgram.countedLoop (entry l.random b) l.count

























 





 









 




 












/-- The mutable sampler scratch is empty at table-entry boundaries. -/
def Clean (l : RandomBits.Layout R) (d : TapeStore R B) : Prop :=
  d.reg l.acc = 0 ∧ d.reg l.count = 0 ∧ d.reg l.tmp = 0 ∧ d.reg l.scratch = 0

 



/-- Explicit data semantics of the runtime-length physical table fill. -/
def fillStore (l : Layout R) (b : Fin B) (inp : Inputs) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => fillStore l b inp n (entryStore l.random b inp (TapeProgram.decStore l.count d))

 































































 





 





 





 





 





 











 



















 




















































































open ExpandingCodes.PolynomialStretch

/-- Canonical contiguous blocking of the K*ell fair coins. -/
def blocksEquiv (K ell : ℕ) : (Fin (K*ell) → Bool) ≃ (Fin K → Fin ell → Bool) where
  toFun x i j := x (finProdFinEquiv (i,j))
  invFun x z := x (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2
  left_inv x := by
    funext z
    change x (finProdFinEquiv (finProdFinEquiv.symm z)) = x z
    exact congrArg x (finProdFinEquiv.apply_symm_apply z)
  right_inv x := by
    funext i j
    change x (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = x i j
    simp only [Equiv.symm_apply_apply]

/-- Each physical table entry is an independent exact binary index. -/
def tableIndexEquiv (K ell : ℕ) : (Fin (K*ell) → Bool) ≃ (Fin K → Fin (2^ell)) :=
  (blocksEquiv K ell).trans (Equiv.piCongrRight fun _ => RandomBits.bitsIndexEquiv ell)

 



 










def sampledValues (inp : Inputs) (K ell h : ℕ) : Fin K → Fin (2^ell) :=
  fun i => ⟨RandomBits.value inp ell (h+i.val*ell) 0,
    by simpa using RandomBits.value_lt inp ell (h+i.val*ell) 0⟩

 

























 



















end RandomTables
end ExpandingCodes.Computation

end FlattenModule22


section FlattenModule23



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch




























end ExpandingCodes.PolynomialStretch

end FlattenModule23


section FlattenModule24


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch




























































end ExpandingCodes.PolynomialStretch

end FlattenModule24


section FlattenModule25


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





































































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule25


section FlattenModule26



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch































































































end ExpandingCodes.PolynomialStretch

end FlattenModule26


section FlattenModule27


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch



























end ExpandingCodes.PolynomialStretch

end FlattenModule27


section FlattenModule28





set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch



































































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule28


section FlattenModule29





set_option autoImplicit false

open scoped BigOperators Topology Pointwise
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch



























































































































end ExpandingCodes.PolynomialStretch

end FlattenModule29


section FlattenModule30


set_option autoImplicit false

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch
























































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule30


section FlattenModule31



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

universe u







































































































end ExpandingCodes.PolynomialStretch

end FlattenModule31


section FlattenModule32




set_option autoImplicit false

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch







































































end ExpandingCodes.PolynomialStretch

end FlattenModule32


section FlattenModule33



set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch


























































































end ExpandingCodes.PolynomialStretch

end FlattenModule33


section FlattenModule34



set_option autoImplicit false
open scoped Classical
open Filter Topology

namespace ExpandingCodes.PolynomialStretch





























end ExpandingCodes.PolynomialStretch

end FlattenModule34


section FlattenModule35


set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

























































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule35


section FlattenModule36


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch













































































end ExpandingCodes.PolynomialStretch

end FlattenModule36


section FlattenModule37



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch



































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule37


section FlattenModule38



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch


























































end ExpandingCodes.PolynomialStretch

end FlattenModule38


section FlattenModule39



set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch















































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule39


section FlattenModule40





set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators
open Filter Topology

namespace ExpandingCodes.PolynomialStretch


























































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule40


section FlattenModule41




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
















































end ExpandingCodes.PolynomialStretch

end FlattenModule41


section FlattenModule42



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





























































end ExpandingCodes.PolynomialStretch

end FlattenModule42

/-! Inlined whole module: ExpandingCodes.Probability.BoundedDifferences -/
section FlattenModule43



/-!
# Sharp finite bounded differences on the uniform Boolean cube

The probability in the final theorem is the mission's canonical `uniformProb`.
`uniformMean` and `HasUnitBoundedDifferences` are local helper interfaces. The
proof uses exact finite sums, splits coordinates by `Fin.consEquiv`, and proves
the centered MGF bound by induction. The two-point estimate is Mathlib's
`Real.cosh_le_exp_half_sq`; finite exponential Markov and optimization give the
sharp exponent `-2 * t^2 / m`. No measure-theoretic martingale is required.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace ExpandingCodes.PolynomialStretch

/-- Exact expectation under the uniform law on a nonempty finite space. -/
noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

section Mean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]










































end Mean







































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule43


section FlattenModule44



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

































































end ExpandingCodes.PolynomialStretch

end FlattenModule44


section FlattenModule45




set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch










































































































end ExpandingCodes.PolynomialStretch

end FlattenModule45

/-! Inlined whole module: ExpandingCodes.Computation.SamplerTables -/
section FlattenModule46



set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch
namespace SamplerTables

/-- Row-major four-dimensional layout. The last coordinate changes fastest. -/
def flatFour (a b c d : ℕ) :
    (((Fin a × Fin b) × Fin c) × Fin d) ≃ Fin (a*b*c*d) :=
  (Equiv.prodCongr (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin c)))
    (Equiv.refl (Fin d))).trans
    ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin d))).trans finProdFinEquiv)






def quadTableEquiv (a b c d : ℕ) (X : Type*) :
    (Fin (a*b*c*d) → X) ≃ (Fin a → Fin b → Fin c → Fin d → X) where
  toFun t i j u v := t (flatFour a b c d (((i,j),u),v))
  invFun f z :=
    let p := (flatFour a b c d).symm z
    f p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv t := by
    funext z
    change t (flatFour a b c d ((flatFour a b c d).symm z)) = t z
    rw [Equiv.apply_symm_apply]
  right_inv f := by
    funext i j u v
    change f ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).1.1.1
      ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).1.1.2
      ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).1.2
      ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).2 = _
    rw [Equiv.symm_apply_apply]

def formEntries (d n k : ℕ) : ℕ := 2*k*fieldSize d n*d
def hashEntries (d n k : ℕ) : ℕ := k*fieldSize d n*fieldSize d n*fieldSize d n
def entropy (d n k beta : ℕ) : ℕ :=
  formEntries d n k * fieldExponent d n + hashEntries d n k * beta

/-- Explicit coefficient-table decoding; both field arguments and values use the
geometry's given enumeration, rather than any fresh choice of enumeration. -/
noncomputable def formsEquiv {d n : ℕ} (g : Geometry d n) (k : ℕ) :
    (Fin (formEntries d n k) → Fin (fieldSize d n)) ≃ Forms g.F d k :=
  (quadTableEquiv 2 k (fieldSize d n) d (Fin (fieldSize d n))).trans
    (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ =>
      Equiv.arrowCongr g.elements
        (Equiv.arrowCongr (Equiv.refl (Fin d)) g.elements))







/-- Flat hash-table decoding, with index order (layer,a,u,v). -/
noncomputable def hashesEquiv {d n : ℕ} (g : Geometry d n) (k b : ℕ) :
    (Fin (hashEntries d n k) → Fin b) ≃ Hashes g.F k b :=
  (quadTableEquiv k (fieldSize d n) (fieldSize d n) (fieldSize d n) (Fin b)).trans
    (Equiv.piCongrRight fun _ =>
      ((Equiv.piCongrRight fun _ =>
        (Equiv.curry (Fin (fieldSize d n)) (Fin (fieldSize d n)) (Fin b)).symm).trans
      ((Equiv.curry (Fin (fieldSize d n))
        (Fin (fieldSize d n) × Fin (fieldSize d n)) (Fin b)).symm.trans
        (Equiv.arrowCongr
          (Equiv.prodCongr g.elements (Equiv.prodCongr g.elements g.elements))
          (Equiv.refl (Fin b))))))







def splitBits (a b : ℕ) :
    (Fin (a+b) → Bool) ≃ ((Fin a → Bool) × (Fin b → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)








def indexCoinsEquiv (K ell H beta extra : ℕ) :
    (Fin (K*ell+H*beta+extra) → Bool) ≃
      (((Fin K → Fin (2^ell)) × (Fin H → Fin (2^beta))) × (Fin extra → Bool)) :=
  (splitBits (K*ell+H*beta) extra).trans
    (Equiv.prodCongr
      ((splitBits (K*ell) (H*beta)).trans
        (Equiv.prodCongr (Computation.RandomTables.tableIndexEquiv K ell)
          (Computation.RandomTables.tableIndexEquiv H beta)))
      (Equiv.refl (Fin extra → Bool)))

noncomputable def coinsEquiv {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ) :
    (Fin (entropy d n k beta + extra) → Bool) ≃
      ((Forms g.F d k × Hashes g.F k (2^beta)) × (Fin extra → Bool)) :=
  (indexCoinsEquiv (formEntries d n k) (fieldExponent d n)
    (hashEntries d n k) beta extra).trans
      (Equiv.prodCongr (Equiv.prodCongr (formsEquiv g k) (hashesEquiv g k (2^beta)))
        (Equiv.refl (Fin extra → Bool)))

noncomputable def decodeCoins {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ)
    (ω : Fin (entropy d n k beta+extra) → Bool) :
    Forms g.F d k × Hashes g.F k (2^beta) := (coinsEquiv g k beta extra ω).1










































/-- Full matrix determined by the two independent decoded tables. -/
noncomputable def generator {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ)
    (ω : Fin (entropy d n k beta+extra) → Bool) : Generator (rowCount d n) n :=
  combined g (decodeCoins g k beta extra ω).1 (decodeCoins g k beta extra ω).2
























/-- Transport a sufficiently long actual random tape to the entropy plus padding
layout. This cast changes no bit positions. -/
def padEquiv (E T : ℕ) (h : E ≤ T) :
    (Fin T → Bool) ≃ (Fin (E+(T-E)) → Bool) :=
  Equiv.arrowCongr (finCongr (Nat.add_sub_of_le h).symm) (Equiv.refl Bool)











noncomputable def fromTape (θ : ℝ) (n T : ℕ) (g : Geometry (dimension θ) n)
    (h : entropy (dimension θ) n (arity θ) (Nat.log 2 (n/arity θ)) ≤ T)
    (ω : Fin T → Bool) : Generator (rowCount (dimension θ) n) n :=
  generator g (arity θ) (Nat.log 2 (n/arity θ))
    (T-entropy (dimension θ) n (arity θ) (Nat.log 2 (n/arity θ)))
    (padEquiv _ T h ω)





















end SamplerTables
end ExpandingCodes.PolynomialStretch

end FlattenModule46

/-! Inlined whole module: ExpandingCodes.Computation.PolynomialBounds -/
section FlattenModule47



set_option autoImplicit false

namespace ExpandingCodes.Computation

/-- A uniform numerical envelope. This predicate bounds a specified function;
it says nothing about an algorithm unless a source execution theorem supplies
that function as its actual step count or counter bound. -/
def PolynomialBound (f : ℕ → ℕ) : Prop :=
  ∃ C a : ℕ, ∀ n ≥ 2, f n ≤ C*(n+1)^a

namespace PolynomialBound
variable {f g : ℕ → ℕ}




















































end PolynomialBound
end ExpandingCodes.Computation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation










































end ExpandingCodes.PolynomialStretch

end FlattenModule47


section FlattenModule48



set_option autoImplicit false

namespace ExpandingCodes.Computation.FieldPrograms
open NKtLB
open ExpandingCodes.PolynomialStretch.BinaryPolynomial

































































end ExpandingCodes.Computation.FieldPrograms

end FlattenModule48

/-! Inlined whole module: ExpandingCodes.Computation.FieldConvolution -/
section FlattenModule49



set_option autoImplicit false

namespace ExpandingCodes.Computation.FieldConvolution
open NKtLB FieldPrograms
open ExpandingCodes.PolynomialStretch
open BinaryPolynomial
variable {R B : ℕ}

/-- A five-label bit-product parity update. The two tested bits are disposable.
It uses only decrement/zero branches and one increment. -/
def toggle (x y p : Fin R) : TapeProgram R B 5 where
  entry := 0
  code i := if i = 0 then .dec x 4 1 else if i = 1 then .dec y 4 2
    else if i = 2 then .dec p 3 4 else if i = 3 then .inc p 4 else .halt

def toggleStore (x y p : Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg x = 0 then d else
    let d₁ := d.setReg x (d.reg x-1)
    if d.reg y = 0 then d₁ else
      let d₂ := d₁.setReg y (d.reg y-1)
      d₂.setReg p (if d.reg p = 0 then 1 else d.reg p-1)





















































































/-- Shared scratch for the two actual coefficient extractions. -/
def leftLayout (r : Fin 12 → Fin R) : Fin 7 → Fin R :=
  fun i => r (![0,4,8,9,6,10,11] i)
def rightLayout (r : Fin 12 → Fin R) : Fin 7 → Fin R :=
  fun i => r (![1,5,8,9,7,10,11] i)













/-- One convolution summand: read both bits, conditionally toggle parity, and
advance the first index. The second index is the runtime loop counter. -/
def body (r : Fin 12 → Fin R) : TapeProgram R B 97 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (testBit (leftLayout r)) (testBit (rightLayout r)))
    (toggle (r 6) (r 7) (r 3))) (TapeMacros.increment (r 4))

def bodyStore (r : Fin 12 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := testBitStore (leftLayout r) d
  let d₂ := testBitStore (rightLayout r) d₁
  let d₃ := toggleStore (r 6) (r 7) (r 3) d₂
  d₃.setReg (r 4) (d₃.reg (r 4)+1)
























































/-- Ordinary raw binary convolution. This is only the specification of the
finite source program and is never an instruction or oracle. -/
def rawConvolution (a b k : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.range (k+1), bitEquiv (Nat.testBit a j) * bitEquiv (Nat.testBit b (k-j))

def bitValue (a j : ℕ) : ℕ := if Nat.testBit a j then 1 else 0







































































/-- The finite runtime counted loop. It has ninety-nine labels for every
input and every field size. -/
def loop (r : Fin 12 → Fin R) : TapeProgram R B 99 :=
  TapeProgram.countedLoop (body r) (r 5)

def loopStore (r : Fin 12 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => loopStore r n (bodyStore r (d.setReg (r 5) n))





















































































































/-- Initialization uses only actual unary counter macros. -/
def prepare (r : Fin 12 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 3))
    (TapeMacros.clear (r 4))) (TapeMacros.copy (r 2) (r 5) (r 11)))
    (TapeMacros.increment (r 5))

def prepareStore (r : Fin 12 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 3) 0).setReg (r 4) 0
  let d₂ := (d₁.setReg (r 5) (d₁.reg (r 2))).setReg (r 11) 0
  d₂.setReg (r 5) (d₂.reg (r 5)+1)










































/-- Fixed 116-label convolution coefficient source program. Its field-size
parameters are data in runtime registers, never source-code indices. -/
def convolution (r : Fin 12 → Fin R) : TapeProgram R B 116 :=
  TapeProgram.seq (prepare r) (loop r)

def convolutionStore (r : Fin 12 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  loopStore r (d.reg (r 2)+1) (prepareStore r d)







































































/-- All read-only heads, output bits, explicit buffer contents and heads. -/
def tapeData (d : TapeStore R B) :
    (Fin 4 → ℕ) × List Bool × (Fin B → List Sym) × (Fin B → ℕ) :=
  (d.roHead, d.output, d.bufferTape, d.bufferHead)












































































































































end ExpandingCodes.Computation.FieldConvolution

end FlattenModule49

/-! Inlined whole module: ExpandingCodes.Computation.FieldCertificates -/
section FlattenModule50


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.FieldCertificates
open NKtLB FieldPrograms FieldConvolution
open ExpandingCodes.PolynomialStretch
open BinaryPolynomial
variable {R B : ℕ}

/-- Exclusive-or into a bit register, using a disposable unit scratch and the
checked actual conditional toggle. The code has nine labels. -/
def xorInto (x unit p : Fin R) : TapeProgram R B 9 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear unit) (TapeMacros.increment unit))
    (toggle x unit p)

def xorStore (x unit p : Fin R) (d : TapeStore R B) : TapeStore R B :=
  toggleStore x unit p (d.setReg unit 1)










































/-- Clear a success bit if a disposable parity bit is nonzero. -/
def requireZero (x flag : Fin R) : TapeProgram R B 3 where
  entry := 0
  code i := if i = 0 then .dec x 2 1 else if i = 1 then .dec flag 2 2 else .halt

def requireStore (x flag : Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg x = 0 then d else (d.setReg x (d.reg x-1)).setReg flag (d.reg flag-1)

















































/-- Runtime register layout: inputs a,b,r,monic(m),s,k; success flag; three
coefficient bits; and eight shared convolution scratch counters. -/
def leftLayout (r : Fin 18 → Fin R) : Fin 12 → Fin R :=
  fun i => r (![0,1,5,7,10,11,12,13,14,15,16,17] i)
def rightLayout (r : Fin 18 → Fin R) : Fin 12 → Fin R :=
  fun i => r (![3,4,5,8,10,11,12,13,14,15,16,17] i)
def remainderLayout (r : Fin 18 → Fin R) : Fin 7 → Fin R :=
  fun i => r (![2,5,14,15,9,16,17] i)



















/-- One actual coefficient equation test, accumulating its answer in a bit
flag. Neither Polynomial nor arithmetic oracles occur in this finite source. -/
def coefficient (r : Fin 18 → Fin R) : TapeProgram R B 298 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (convolution (leftLayout r)) (convolution (rightLayout r)))
    (testBit (remainderLayout r))) (xorInto (r 8) (r 16) (r 7)))
    (xorInto (r 9) (r 16) (r 7))) (requireZero (r 7) (r 6))

def coefficientStore (r : Fin 18 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := convolutionStore (leftLayout r) d
  let d₂ := convolutionStore (rightLayout r) d₁
  let d₃ := testBitStore (remainderLayout r) d₂
  let d₄ := xorStore (r 8) (r 16) (r 7) d₃
  let d₅ := xorStore (r 9) (r 16) (r 7) d₄
  requireStore (r 7) (r 6) d₅
















































































































/-- The coefficient equation checked by the finite code, for ordinary binary
indices of all five polynomial buffers. -/
def CoefficientMatches (a b rem monic quotient k : ℕ) : Prop :=
  rawConvolution a b k = bitEquiv (Nat.testBit rem k) + rawConvolution monic quotient k

instance (a b rem monic quotient k : ℕ) : Decidable (CoefficientMatches a b rem monic quotient k) :=
  inferInstanceAs (Decidable (rawConvolution a b k = bitEquiv (Nat.testBit rem k) + rawConvolution monic quotient k))

















































































































/-- The nineteenth register is an outer runtime coefficient count. -/
def restrict (r : Fin 19 → Fin R) : Fin 18 → Fin R := fun i => r i.castSucc














/-- One actual coefficient certificate check followed by one unit position
increment. It has three hundred labels independently of the runtime bound. -/
def step (r : Fin 19 → Fin R) : TapeProgram R B 300 :=
  TapeProgram.seq (coefficient (restrict r)) (TapeMacros.increment (r 5))

def stepStore (r : Fin 19 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := coefficientStore (restrict r) d
  c.setReg (r 5) (c.reg (r 5)+1)




































































/-- Actual bounded coefficient certificate loop. The caller initializes
position=0, success=1, and the outer counter to its runtime bound. -/
def certificateLoop (r : Fin 19 → Fin R) : TapeProgram R B 302 :=
  TapeProgram.countedLoop (step r) (r 18)

def certificateStore (r : Fin 19 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => certificateStore r n (stepStore r (d.setReg (r 18) n))

































































































































































































































/-- Add one preserved runtime bound register to the coefficient loop. -/
def restrict19 (r : Fin 20 → Fin R) : Fin 19 → Fin R := fun i => r i.castSucc














/-- Clear the coefficient position, initialize success to one and copy the
preserved runtime bound into the actual loop counter. -/
def prepare (r : Fin 20 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 5))
    (TapeMacros.clear (r 6))) (TapeMacros.increment (r 6)))
      (TapeMacros.copy (r 19) (r 18) (r 17))

def prepareStore (r : Fin 20 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 5) 0).setReg (r 6) 1
  (d₁.setReg (r 18) (d₁.reg (r 19))).setReg (r 17) 0







































/-- Fully initialized 319-label source certificate. Five runtime input words
are preserved; register 19 contains a preserved runtime coefficient bound. -/
def certificate (r : Fin 20 → Fin R) : TapeProgram R B 319 :=
  TapeProgram.seq (prepare r) (certificateLoop (restrict19 r))

def certificateResult (r : Fin 20 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  certificateStore (restrict19 r) (d.reg (r 19)) (prepareStore r d)






















































































































end ExpandingCodes.Computation.FieldCertificates

end FlattenModule50

/-! Inlined whole module: ExpandingCodes.Computation.SourceFieldArithmetic -/
section FlattenModule51


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldArithmetic
open NKtLB FieldPrograms FieldConvolution FieldCertificates
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B L : ℕ}

/-- Execute a finite source fragment only when a disposable runtime flag is
positive. The zero branch halts in one actual instruction. -/
def onPositive (P : TapeProgram R B L) (flag : Fin R) : TapeProgram R B (L+2) where
  entry := TapeProgram.loopHeader L
  code j := match finSumFinEquiv.symm j with
    | .inl i => (P.code i).relabel (TapeProgram.leftLabel 2)
    | .inr i => if i = 0 then .dec flag (TapeProgram.loopExit L)
        (TapeProgram.leftLabel 2 P.entry) else .halt



































/-- Conditional search commit: copy an accepted candidate into the answer
counter and set a found bit to one. Its five registers are pairwise distinct. -/
def commitBody (r : Fin 5 → Fin R) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 0) (r 1) (r 2))
    (TapeMacros.clear (r 3))) (TapeMacros.increment (r 3))

def commitBodyStore (r : Fin 5 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg (r 1) (d.reg (r 0))).setReg (r 2) 0).setReg (r 3) 1






























def commit (r : Fin 5 → Fin R) : TapeProgram R B 17 :=
  onPositive (commitBody r) (r 4)

def commitStore (r : Fin 5 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg (r 4) = 0 then d else
    commitBodyStore r (d.setReg (r 4) (d.reg (r 4)-1))


















































































/-- A semantic fold of a finite loop body. This records post-stores only; the
source program is always the separate finite `countedLoop P counter`. -/
def loopResult (counter : Fin R) (F : TapeStore R B → TapeStore R B) :
    ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => loopResult counter F n (F (d.setReg counter n))












































































/-- Static multiplication-search register layout. Registers 0..19 are the
certificate interface; 20=answer,21=copy scratch,22=found,23=q,24=q²,
25=outer counter and26=inner counter. -/
def certificateLayout (r : Fin 27 → Fin R) : Fin 20 → Fin R :=
  fun i => r ⟨i.val, by have := i.isLt; omega⟩
def commitLayout (r : Fin 27 → Fin R) : Fin 5 → Fin R :=
  fun i => r (![2,20,21,22,6] i)







































/-- One successful-pair scan step. This invokes the actual319-label certificate,
conditionally commits its remainder, and increments the quotient candidate. -/
def innerBody (r : Fin 27 → Fin R) : TapeProgram R B 338 :=
  TapeProgram.seq (TapeProgram.seq (certificate (certificateLayout r))
    (commit (commitLayout r))) (TapeMacros.increment (r 4))

def innerBodyStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := commitStore (commitLayout r) (certificateResult (certificateLayout r) d)
  c.setReg (r 4) (c.reg (r 4)+1)





























































def innerLoop (r : Fin 27 → Fin R) : TapeProgram R B 340 :=
  TapeProgram.countedLoop (innerBody r) (r 26)
def innerResult (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  loopResult (r 26) (innerBodyStore r) n d




























































def innerPrepare (r : Fin 27 → Fin R) : TapeProgram R B 13 :=
  TapeProgram.seq (TapeMacros.clear (r 4)) (TapeMacros.copy (r 24) (r 26) (r 21))
def innerPrepareStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := d.setReg (r 4) 0
  (c.setReg (r 26) (c.reg (r 24))).setReg (r 21) 0




























def outerBody (r : Fin 27 → Fin R) : TapeProgram R B 355 :=
  TapeProgram.seq (TapeProgram.seq (innerPrepare r) (innerLoop r)) (TapeMacros.increment (r 2))
def outerBodyStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := innerResult r (d.reg (r 24)) (innerPrepareStore r d)
  c.setReg (r 2) (c.reg (r 2)+1)











































































def outerLoop (r : Fin 27 → Fin R) : TapeProgram R B 357 :=
  TapeProgram.countedLoop (outerBody r) (r 25)
def outerResult (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  loopResult (r 25) (outerBodyStore r) n d













































def multiplyPrepare (r : Fin 27 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 20))
    (TapeMacros.clear (r 22))) (TapeMacros.clear (r 2))) (TapeMacros.copy (r 23) (r 25) (r 21))
def multiplyPrepareStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := ((d.setReg (r 20) 0).setReg (r 22) 0).setReg (r 2) 0
  (c.setReg (r 25) (c.reg (r 23))).setReg (r 21) 0


































/-- Uniform actual finite multiplication search: every runtime remainder below
q is paired with every runtime quotient below q². No code depends on q or ell. -/
def multiply (r : Fin 27 → Fin R) : TapeProgram R B 374 :=
  TapeProgram.seq (multiplyPrepare r) (outerLoop r)

def multiplyResult (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  outerResult r (d.reg (r 23)) (multiplyPrepareStore r d)











































/-- Projection used only to prove the source search's semantics. -/
def environment (r : Fin 27 → Fin R) (d : TapeStore R B) : Fin 4 → ℕ :=
  ![d.reg (r 0),d.reg (r 1),d.reg (r 3),d.reg (r 19)]
def accept (env : Fin 4 → ℕ) (rem quotient : ℕ) : Bool :=
  decide (∀ j : Fin (env 3), CoefficientMatches (env 0) (env 1) rem (env 2) quotient j.val)
def answer (r : Fin 27 → Fin R) (d : TapeStore R B) : Option ℕ :=
  if d.reg (r 22) = 0 then none else some (d.reg (r 20))





















































/-- A mathematical scan model used only after the actual source execution has
been proved. Each Boolean test is refined by the319-label source certificate. -/
def scanRow (test : ℕ → ℕ → Bool) (rem : ℕ) : ℕ → ℕ → Option ℕ → Option ℕ
  | 0, _, state => state
  | n+1, s, state => scanRow test rem n (s+1) (if test rem s then some rem else state)
def scanRect (test : ℕ → ℕ → Bool) (Q : ℕ) : ℕ → ℕ → Option ℕ → Option ℕ
  | 0, _, state => state
  | n+1, r, state => scanRect test Q n (r+1) (scanRow test r Q 0 state)






































































def Correct (target : ℕ) (state : Option ℕ) : Prop := ∀ v, state = some v → v = target



































































































































































































































/-- Initialize one unary register to one by actual clear/increment code. -/
def setOne (x : Fin R) : TapeProgram R B 4 := TapeProgram.seq (TapeMacros.clear x) (TapeMacros.increment x)











/-- Addition checks `a*1 = r+b*1` using the same actual coefficient certificate.
Only the candidate remainder is incremented after each check. -/
def additionBody (r : Fin 27 → Fin R) : TapeProgram R B 338 :=
  TapeProgram.seq (TapeProgram.seq (certificate (certificateLayout r)) (commit (commitLayout r)))
    (TapeMacros.increment (r 2))
def additionBodyStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := commitStore (commitLayout r) (certificateResult (certificateLayout r) d)
  c.setReg (r 2) (c.reg (r 2)+1)



















































def additionLoop (r : Fin 27 → Fin R) : TapeProgram R B 340 := TapeProgram.countedLoop (additionBody r) (r 25)
def additionFold (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 25) (additionBodyStore r) n d


























def additionPrepare (r : Fin 27 → Fin R) : TapeProgram R B 25 :=
  TapeProgram.seq (TapeProgram.seq (multiplyPrepare r) (setOne (r 1))) (setOne (r 4))
def additionPrepareStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((multiplyPrepareStore r d).setReg (r 1) 1).setReg (r 4) 1




























def addition (r : Fin 27 → Fin R) : TapeProgram R B 365 := TapeProgram.seq (additionPrepare r) (additionLoop r)
def additionResult (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  additionFold r (d.reg (r 23)) (additionPrepareStore r d)
























































































































































































































/-- Four-label destructive test for the unary constant one. -/
def oneTest (x flag : Fin R) : TapeProgram R B 4 where
  entry := 0
  code i := if i = 0 then .dec x 3 1 else if i = 1 then .dec x 2 3
    else if i = 2 then .inc flag 3 else .halt

def oneTestStore (x flag : Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg x = 0 then d else if d.reg x = 1 then (d.setReg x 0).setReg flag (d.reg flag+1)
  else d.setReg x (d.reg x-2)
































def isOne (x flag : Fin R) : TapeProgram R B 6 := TapeProgram.seq (TapeMacros.clear flag) (oneTest x flag)
def isOneStore (x flag : Fin R) (d : TapeStore R B) : TapeStore R B := oneTestStore x flag (d.setReg flag 0)






































































def inverseMultiplyLayout (r : Fin 31 → Fin R) : Fin 27 → Fin R :=
  fun i => r ⟨i.val,by have := i.isLt;omega⟩
def inverseCommitLayout (r : Fin 31 → Fin R) : Fin 5 → Fin R := fun i => r (![1,27,28,29,6] i)












































def inverseBody (r : Fin 31 → Fin R) : TapeProgram R B 399 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (multiply (inverseMultiplyLayout r)) (isOne (r 20) (r 6)))
    (commit (inverseCommitLayout r))) (TapeMacros.increment (r 1))
def inverseBodyStore (r : Fin 31 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₁ := multiplyResult (inverseMultiplyLayout r) d
  let c₂ := isOneStore (r 20) (r 6) c₁
  let c₃ := commitStore (inverseCommitLayout r) c₂
  c₃.setReg (r 1) (c₃.reg (r 1)+1)



























































def inverseLoop (r : Fin 31 → Fin R) : TapeProgram R B 401 := TapeProgram.countedLoop (inverseBody r) (r 30)
def inverseFold (r : Fin 31 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 30) (inverseBodyStore r) n d











def inversePrepare (r : Fin 31 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 27)) (TapeMacros.clear (r 29)))
    (TapeMacros.clear (r 1))) (TapeMacros.copy (r 23) (r 30) (r 28))
def inversePrepareStore (r : Fin 31 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := ((d.setReg (r 27) 0).setReg (r 29) 0).setReg (r 1) 0
  (c.setReg (r 30) (c.reg (r 23))).setReg (r 28) 0



























/-- Actual fixed418-label q-candidate inverse scan. -/
def inverse (r : Fin 31 → Fin R) : TapeProgram R B 418 := TapeProgram.seq (inversePrepare r) (inverseLoop r)
def inverseResult (r : Fin 31 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  inverseFold r (d.reg (r 23)) (inversePrepareStore r d)





























































def inverseTest (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (b : ℕ) : Bool :=
  if hb : b < 2^ell then decide ((BinaryField.multiplyIndex ell h (selectedIndex ell h)
    (indexEquiv ell a) (indexEquiv ell ⟨b,hb⟩)).val = 1) else false

def InverseSetup (r : Fin 31 → Fin R) (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (d : TapeStore R B) : Prop :=
  d.reg (r 0) = a.val ∧ d.reg (r 3) = 2^ell+(selectedIndex ell h).val ∧
    d.reg (r 19) = 3*ell+1 ∧ d.reg (r 23) = 2^ell ∧ d.reg (r 24) = 2^(2*ell)
def inverseAnswer (r : Fin 31 → Fin R) (d : TapeStore R B) : Option ℕ :=
  if d.reg (r 29) = 0 then none else some (d.reg (r 27))






















































































































































































































































































end ExpandingCodes.Computation.SourceFieldArithmetic

end FlattenModule51

/-! Inlined whole module: ExpandingCodes.Computation.SamplerEvaluation -/
section FlattenModule52







set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace SamplerEvaluation
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}






















/-- Indexed field/hash table read preserving the caller's runtime width.
Layout: index0, width1, consumed-width2, offset3, tmp4, count5, value6,
copy-scratch7. All operations are the physical TapeArrays routines. -/
def lookup (r : Fin 8 → Fin R) (b : Fin B) : TapeProgram R B 48 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 1) (r 2) (r 7))
    (TapeMacros.clear (r 6))) (TapeArrays.readEntry (r 0) (r 2) (r 3) (r 4) (r 5) (r 6) b)

def lookupPrepare (r : Fin 8 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg (r 2) (s.reg (r 1))).setReg (r 7) 0).setReg (r 6) 0

def lookupRegisters (r : Fin 8 → Fin R) (v : ℕ) (s : TapeStore R B) : Fin R → ℕ :=
  ((((((s.setReg (r 2) 0).setReg (r 3) 0).setReg (r 4) 0).setReg (r 5) 0).setReg (r 6) v).setReg (r 7) 0).reg





























































































/-- Shared physical field workspace occupies 0..26. External operands are27,28
and output29. Addition remaps its preserved second-input register directly to
external operand28, leaving the multiplication modulus in register3 untouched. -/
def fieldLayout (r : Fin 30 → Fin R) (i : Fin 27) : Fin R :=
  r ⟨i.val,by omega⟩

def additionLayout (r : Fin 30 → Fin R) (i : Fin 27) : Fin R :=
  if i=3 then r 28 else fieldLayout r i

























/-- Actual finite field addition into an external register. Runtime field size,
bit length and polynomial modulus never occur in this source code table. -/
def addFrom (r : Fin 30 → Fin R) : TapeProgram R B 387 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 27) (r 0) (r 2))
    (SourceFieldArithmetic.addition (additionLayout r))) (TapeMacros.copy (r 20) (r 29) (r 2))


























































































/-- Actual finite field multiplication into an external register. -/
def multiplyFrom (r : Fin 30 → Fin R) : TapeProgram R B 407 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 27) (r 0) (r 2)) (TapeMacros.copy (r 28) (r 1) (r 2)))
      (SourceFieldArithmetic.multiply (fieldLayout r))) (TapeMacros.copy (r 20) (r 29) (r 2))

























































































def scaleLabels : ℕ → ℕ
  | 0 => 1
  | c+1 => 9+scaleLabels c

/-- A statically fixed number of preserving unary additions. Runtime radix or
address values never occur in this finite code table. -/
def scaleAdd (src dst tmp : Fin R) : (c : ℕ) → TapeProgram R B (scaleLabels c)
  | 0 => TapeProgram.skip
  | c+1 => TapeProgram.seq (TapeMacros.addPreserving src dst tmp) (scaleAdd src dst tmp c)

def scaleStore (src dst tmp : Fin R) (c : ℕ) (s : TapeStore R B) : TapeStore R B :=
  (s.setReg dst (s.reg dst+c*s.reg src)).setReg tmp 0

















































def formIndexLabels (c d j : ℕ) : ℕ :=
  (((11+scaleLabels c)+2)+scaleLabels d)+ParameterPrograms.raiseLabels j

/-- Physical flat-form address j+d*(a+q*c), with c=i+k*row statically fixed.
Only preserving unary additions and static increments are executed. -/
def formIndex (r : Fin 5 → Fin R) (c d j : ℕ) : TapeProgram R B (formIndexLabels c d j) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 0) (r 2) (r 4)) (scaleAdd (r 1) (r 2) (r 4) c))
      (TapeMacros.clear (r 3))) (scaleAdd (r 2) (r 3) (r 4) d)) (ParameterPrograms.raise (r 3) j)

def formIndexStore (r : Fin 5 → Fin R) (c d j : ℕ) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg (r 2) (s.reg (r 0)+c*s.reg (r 1))).setReg (r 3)
    (d*(s.reg (r 0)+c*s.reg (r 1))+j)).setReg (r 4) 0

def formIndexTime (r : Fin 5 → Fin R) (c d j : ℕ) (s : TapeStore R B) : ℕ :=
  s.reg (r 2)+s.reg (r 4)+5*s.reg (r 0)+c*(5*s.reg (r 1)+6)+s.reg (r 3)+
    d*(5*(s.reg (r 0)+c*s.reg (r 1))+6)+2*j+12




























































/-- Runtime unary Horner arithmetic acc := radix*acc+digit. Layout radix0,
acc1,digit2,product3,tmp4,count5. All work is explicit unary multiplication,
preserving copy and preserving addition. -/
def hornerStep (r : Fin 6 → Fin R) : TapeProgram R B 44 :=
  TapeProgram.seq (TapeProgram.seq (UnaryArithmetic.multiply (r 1) (r 0) (r 3) (r 4) (r 5))
    (TapeMacros.copy (r 3) (r 1) (r 4))) (TapeMacros.addPreserving (r 2) (r 1) (r 4))

def hornerStore (r : Fin 6 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  ((((s.setReg (r 3) (s.reg (r 1)*s.reg (r 0))).setReg (r 4) 0).setReg (r 5) 0).setReg (r 1) (s.reg (r 1)*s.reg (r 0)+s.reg (r 2)))

def hornerTime (r : Fin 6 → Fin R) (s : TapeStore R B) : ℕ :=
  s.reg (r 3)+s.reg (r 5)+s.reg (r 4)+10*s.reg (r 1)*s.reg (r 0)+12*s.reg (r 0)+
    s.reg (r 1)+5*s.reg (r 2)+25

































































def hashLayout (r : Fin 8 → Fin R) (t : Fin 3) : Fin 6 → Fin R :=
  ![r 0,r 4,r ⟨t.val+1,by omega⟩,r 5,r 6,r 7]






def hashIndexLabels (i : ℕ) : ℕ := (((2+ParameterPrograms.raiseLabels i)+44)+44)+44

/-- Exact physical base-q flattening v+q*(u+q*(a+q*i)), with layer i a static
program parameter. The runtime q multiplications are all actual unary loops. -/
def hashIndex (r : Fin 8 → Fin R) (i : ℕ) : TapeProgram R B (hashIndexLabels i) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (ParameterPrograms.loadConstant (r 4) i)
    (hornerStep (hashLayout r 0))) (hornerStep (hashLayout r 1))) (hornerStep (hashLayout r 2))

def hashIndexStore (r : Fin 8 → Fin R) (i : ℕ) (s : TapeStore R B) : TapeStore R B :=
  hornerStore (hashLayout r 2) (hornerStore (hashLayout r 1)
    (hornerStore (hashLayout r 0) (s.setReg (r 4) i)))

def hashEnvelope (i M : ℕ) : ℕ → ℕ
  | 0 => M+i+1
  | t+1 => (hashEnvelope i M t+1)^2

def hashIndexTimeBound (i M : ℕ) : ℕ :=
  M+2*i+5+32*hashEnvelope i M 1+32*hashEnvelope i M 2+32*hashEnvelope i M 3





























































































































def coefficientIndexLayout (r : Fin 12 → Fin R) : Fin 5 → Fin R := ![r 0,r 1,r 2,r 3,r 4]
def coefficientReadLayout (r : Fin 12 → Fin R) : Fin 8 → Fin R :=
  ![r 3,r 1,r 5,r 6,r 7,r 8,r 9,r 10]











def coefficientLoadLabels (c d j : ℕ) : ℕ := (formIndexLabels c d j+48)+11

/-- Actual form-table coefficient load, including physical address arithmetic,
indexed seek/read, and copying the scalar coefficient into its caller register.
Layout a0,q1,scratch2..10,coefficient destination11. -/
def coefficientLoad (r : Fin 12 → Fin R) (b : Fin B) (c d j : ℕ) :
    TapeProgram R B (coefficientLoadLabels c d j) :=
  TapeProgram.seq (TapeProgram.seq (formIndex (coefficientIndexLayout r) c d j)
    (lookup (coefficientReadLayout r) b)) (TapeMacros.copy (r 9) (r 11) (r 10))

def coefficientAddress (r : Fin 12 → Fin R) (c d j : ℕ) (s : TapeStore R B) : ℕ :=
  d*(s.reg (r 0)+c*s.reg (r 1))+j






































































































def hashAddress (r : Fin 8 → Fin R) (i : ℕ) (s : TapeStore R B) : ℕ :=
  s.reg (r 3)+s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*(s.reg (r 1)+s.reg (r 0)*i))

def hashedColumnLabels (i : ℕ) : ℕ := ((hashIndexLabels i+48)+11)+scaleLabels i

/-- Actual hash-table read and block-column offset. The layer number i is
static, while field size, bucket width, address digits and bucket are runtime
counter/buffer data. -/
def hashedColumn (h r : Fin 8 → Fin R) (column tmp : Fin R) (b : Fin B) (i : ℕ) :
    TapeProgram R B (hashedColumnLabels i) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (hashIndex h i) (lookup r b))
    (TapeMacros.copy (r 6) column tmp)) (scaleAdd (r 1) column tmp i)

def hashedColumnTimeBound (i M : ℕ) : ℕ :=
  hashIndexTimeBound i M+64*(M+1)^2+7*M+10+i*(5*M+6)






























































































































end SamplerEvaluation
end ExpandingCodes.Computation

end FlattenModule52

/-! Inlined whole module: ExpandingCodes.Computation.SamplerOdometer -/
section FlattenModule53



set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
open scoped BigOperators
namespace SamplerOdometer
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- One physical decrement/test. Both outcomes halt after one transition. -/
def decrement (r : Fin R) : TapeProgram R B 2 where
  entry := 0
  code j := if j=0 then .dec r 1 1 else .halt













/-- A digit is stored together with its countdown q-1-digit. All digits have
separate unary counters; no tuple is packed into a unary number. -/
abbrev Digit (R : ℕ) := Fin R × Fin R

def used : List (Digit R) → List (Fin R)
  | [] => []
  | p::ps => p.1::p.2::used ps

def reset (q tmp : Fin R) (p : Digit R) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear p.1)
    (TapeMacros.copy q p.2 tmp)) (decrement p.2)

def resetStore (q tmp : Fin R) (p : Digit R) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg p.1 0).setReg p.2 (s.reg q-1)).setReg tmp 0

def advance (p : Digit R) : TapeProgram R B 4 :=
  TapeProgram.seq (decrement p.2) (TapeMacros.increment p.1)

def advanceStore (p : Digit R) (s : TapeStore R B) : TapeStore R B :=
  (s.setReg p.2 (s.reg p.2-1)).setReg p.1 (s.reg p.1+1)

def labels : List (Digit R) → ℕ
  | [] => 1
  | _::ps => (15+labels ps)+4+2

/-- Fixed-dimensional little-endian odometer. Each stage performs a physical
countdown test, an increment, or a physical reset followed by carry. The finite
code table depends only on the list of digit registers, never runtime q. -/
def program (q tmp : Fin R) : (ps : List (Digit R)) → TapeProgram R B (labels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.branchZero p.2
      (TapeProgram.seq (reset q tmp p) (program q tmp ps)) (advance p)

def nextStore (q tmp : Fin R) : List (Digit R) → TapeStore R B → TapeStore R B
  | [],s => s
  | p::ps,s => if s.reg p.2=0 then nextStore q tmp ps (resetStore q tmp p s)
      else advanceStore p s




























































































































/-- The ordinary little-endian digit list represented by the separate counters. -/
def readings (ps : List (Digit R)) (s : TapeStore R B) : List ℕ := ps.map (fun p => s.reg p.1)

def successor (q : ℕ) : List ℕ → List ℕ
  | [] => []
  | x::xs => if x+1=q then 0::successor q xs else (x+1)::xs

/-- Runtime invariant linking a digit with its unary countdown. -/
def Valid (q : Fin R) (ps : List (Digit R)) (s : TapeStore R B) : Prop :=
  ∀ p∈ps,s.reg p.1+s.reg p.2+1=s.reg q

























































































def initializeLabels : List (Digit R) → ℕ
  | [] => 1
  | _::ps => 15+initializeLabels ps

/-- Initialize every separate digit to zero and every countdown to runtime q-1
using copies of the runtime radix. This is finite code for any fixed dimension. -/
def initDigits (q tmp : Fin R) : (ps : List (Digit R)) → TapeProgram R B (initializeLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (reset q tmp p) (initDigits q tmp ps)

def initializeStore (q tmp : Fin R) : List (Digit R) → TapeStore R B → TapeStore R B
  | [],s => s
  | p::ps,s => initializeStore q tmp ps (resetStore q tmp p s)








































































































































































































































































































































end SamplerOdometer
end ExpandingCodes.Computation

end FlattenModule53

/-! Inlined whole module: ExpandingCodes.Computation.GaussianElimination -/
section FlattenModule54





set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

variable {F : Type*} [Field F] [DecidableEq F]

/-- Eager, explicitly indexed storage. No whole table is packed into a natural. -/
abbrev Table (F : Type*) (m n : ℕ) := Vector (Vector F n) m

def toMatrix {m n : ℕ} (A : Table F m n) : Matrix (Fin m) (Fin n) F :=
  fun i j => A[i.val][j.val]

def ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : Table F m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j







/-- Deterministic row-major list of cells, of length exactly m*n. -/
def cells (m n : ℕ) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => (i,j)







/-- Bounded search, inspecting at most m*n entries. -/
def pivot {m n : ℕ} (A : Table F m n) : Option (Fin m × Fin n) :=
  (cells m n).find? fun p => toMatrix A p.1 p.2 != 0












/-- Swap a chosen row and column to the origin, then eliminate both. This
eagerly writes exactly m*n entries, using one inverse and three field
operations per entry. The inverse is shared outside the materialization. -/
def schur {m n : ℕ} (A : Table F (m+1) (n+1))
    (p : Fin (m+1) × Fin (n+1)) : Table F m n :=
  let B := toMatrix A
  let aInv := (B p.1 p.2)⁻¹
  ofMatrix fun i j =>
    B (p.1.succAbove i) (p.2.succAbove j) -
      B (p.1.succAbove i) p.2 * aInv * B p.1 (p.2.succAbove j)

/-- Actual deterministic elimination, recursing on a strictly smaller table.
The result is the number of successful nonzero pivots. -/
def rank : {m n : ℕ} → Table F m n → ℕ
  | 0, _, _ => 0
  | _+1, 0, _ => 0
  | _m+1, _n+1, A =>
      match pivot A with
      | none => 0
      | some p => rank (schur A p) + 1














/-- The same finite search, returning the exact number of field comparisons.
The pair is computed in one traversal. -/
def scan {m n : ℕ} (A : Table F m n) :
    List (Fin m × Fin n) → Option (Fin m × Fin n) × ℕ
  | [] => (none, 0)
  | p :: ps =>
      if toMatrix A p.1 p.2 != 0 then (some p, 1)
      else let r := scan A ps; (r.1, r.2+1)
















/-- Abstract resource counters. Field arithmetic consists of one inverse per
pivot and two multiplications and one subtraction per new Schur entry.
Array reads/writes count field entries, not physical bit cells. `enumerated`
also charges every cell of the row-major index list, including unused suffixes.
Refinement to encoded arithmetic, bit buffers, and counter moves is required. -/
structure Work where
  comparisons : ℕ := 0
  inverses : ℕ := 0
  arithmetic : ℕ := 0
  reads : ℕ := 0
  writes : ℕ := 0
  enumerated : ℕ := 0
  deriving Repr, DecidableEq




def Work.add (a b : Work) : Work :=
  ⟨a.comparisons+b.comparisons, a.inverses+b.inverses,
    a.arithmetic+b.arithmetic, a.reads+b.reads,
    a.writes+b.writes, a.enumerated+b.enumerated⟩





def zeroWork (s cells : ℕ) : Work := ⟨s, 0, 0, s, 0, cells⟩

def pivotWork (m n s : ℕ) : Work :=
  ⟨s, 1, 3*m*n, s+3*m*n+1, m*n, (m+1)*(n+1)⟩

/-- Resource-instrumented executable elimination. Its search result, reduced
table, rank, and resource record are all explicit deterministic data. -/
def run : {m n : ℕ} → Table F m n → ℕ × Work
  | 0, _, _ => (0, {})
  | _+1, 0, _ => (0, {})
  | m+1, n+1, A =>
      let s := scan A (cells (m+1) (n+1))
      match s.1 with
      | none => (0, zeroWork s.2 ((m+1)*(n+1)))
      | some p =>
          let r := run (schur A p)
          (r.1+1, (pivotWork m n s.2).add r.2)

























































end ExpandingCodes.Computation.Gaussian

end FlattenModule54

/-! Inlined whole module: ExpandingCodes.Computation.GaussianCorrectness -/
section FlattenModule55







set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

open Matrix Module LinearMap
open scoped Matrix

variable {F : Type*} [Field F]

 def prodSubmoduleEquiv {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    (p : Submodule F M) (q : Submodule F N) : p.prod q ≃ₗ[F] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1,x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl















































/-- Explicit reindexing that puts the selected pivot at the distinguished
singleton. All other indices occur in their original order. -/
def pivotEquiv {m : ℕ} (p : Fin (m+1)) : PUnit.{1} ⊕ Fin m ≃ Fin (m+1) :=
  (Equiv.sumComm PUnit.{1} (Fin m)).trans
    ((Equiv.optionEquivSumPUnit (Fin m)).symm.trans (finSuccEquiv' p).symm)












































































end ExpandingCodes.Computation.Gaussian

end FlattenModule55

/-! Inlined whole module: ExpandingCodes.Computation.EncodedGaussian -/
section FlattenModule56




set_option autoImplicit false

namespace ExpandingCodes.Computation.EncodedGaussian

open Gaussian

/-- Executable operations on finite field codes. No field structure or
noncomputable quotient operation is used by the encoded algorithm. -/
structure Operations (α : Type*) where
  zero : α
  one : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  inv : α → α

structure Interpretation {α F : Type*} [Field F]
    (O : Operations α) (decode : α → F) : Prop where
  injective : Function.Injective decode
  zero : decode O.zero = 0
  one : decode O.one = 1
  add : ∀ a b, decode (O.add a b) = decode a + decode b
  sub : ∀ a b, decode (O.sub a b) = decode a - decode b
  mul : ∀ a b, decode (O.mul a b) = decode a * decode b
  inv : ∀ a, decode (O.inv a) = (decode a)⁻¹

def mapTable {α β : Type*} (f : α → β) {m n : ℕ} (A : Table α m n) : Table β m n :=
  ofMatrix fun i j => f (toMatrix A i j)






variable {α : Type*} [DecidableEq α]

def scan (O : Operations α) {m n : ℕ} (A : Table α m n) :
    List (Fin m × Fin n) → Option (Fin m × Fin n) × ℕ
  | [] => (none, 0)
  | p :: ps =>
      if toMatrix A p.1 p.2 != O.zero then (some p, 1)
      else let r := scan O A ps; (r.1, r.2+1)

def schur (O : Operations α) {m n : ℕ} (A : Table α (m+1) (n+1))
    (p : Fin (m+1) × Fin (n+1)) : Table α m n :=
  let B := toMatrix A
  let aInv := O.inv (B p.1 p.2)
  ofMatrix fun i j =>
    O.sub (B (p.1.succAbove i) (p.2.succAbove j))
      (O.mul (O.mul (B (p.1.succAbove i) p.2) aInv)
        (B p.1 (p.2.succAbove j)))

/-- Actual finite-code elimination. The recursive argument loses one row and
column after each successful pivot, and the resulting arrays are eager. -/
def run (O : Operations α) : {m n : ℕ} → Table α m n → ℕ × Work
  | 0, _, _ => (0, {})
  | _+1, 0, _ => (0, {})
  | m+1, n+1, A =>
      let s := scan O A (cells (m+1) (n+1))
      match s.1 with
      | none => (0, zeroWork s.2 ((m+1)*(n+1)))
      | some p =>
          let r := run O (schur O A p)
          (r.1+1, (pivotWork m n s.2).add r.2)

variable {F : Type*} [Field F] [DecidableEq F]
variable {O : Operations α} {decode : α → F}





















































end ExpandingCodes.Computation.EncodedGaussian

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Computation.EncodedGaussian BinaryPolynomial

def zeroIndex (ell : ℕ) : Fin (2 ^ ell) := (indexEquiv ell).symm (zero ell)

def oneIndex (ell : ℕ) : Fin (2 ^ ell) := (indexEquiv ell).symm (one ell)

def indexOperations (ell : ℕ) (h : 0 < ell) : Operations (Fin (2 ^ ell)) where
  zero := zeroIndex ell
  one := oneIndex ell
  add := addIndex ell
  sub := addIndex ell
  mul i j := multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell i) (indexEquiv ell j)
  inv := inverseIndex ell h




























end ExpandingCodes.PolynomialStretch.BinaryField

end FlattenModule56

/-! Inlined whole module: ExpandingCodes.Algebra.FullEvaluation -/
section FlattenModule57



set_option autoImplicit false

open scoped BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Every bounded exponent tuple is represented explicitly. Rows outside the
canonical total-degree bound are zero. This avoids dependent subtype search in
the tester's row enumeration. -/
def fullEvaluationMatrix {d n : ℕ} (g : Geometry d n) :
    Matrix (Fin d → Fin (Fintype.card g.F)) (Fin (rowCount d n)) g.F :=
  fun a z => if (∑ i, (a i).val) ≤ auxiliaryDegree (Fintype.card g.F) d
    then ∏ i, (g.rowOrder z i) ^ (a i).val else 0













def fullTestMatrix {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :=
  (fullEvaluationMatrix g * Matrix.diagonal (fun z => if y z = 0 then (0 : g.F) else 1)) *
    (fullEvaluationMatrix g).transpose


















































/-- Explicit base-q exponent enumeration, using arithmetic quotient and
remainder through `finFunctionFinEquiv`; it does not choose an enumeration of
the dependent monomial subtype. -/
def fullExponentOrder {d n : ℕ} (g : Geometry d n) :
    Fin (rowCount d n) ≃ (Fin d → Fin (Fintype.card g.F)) :=
  (finCongr (by
    have h : fieldSize d n = Fintype.card g.F := by
      simpa using Fintype.card_congr g.elements
    simp [rowCount, h])).trans finFunctionFinEquiv.symm

/-- The complete input table for the generic Gaussian algorithm. Its cells are
eagerly materialized, and its row enumeration is explicit base-q arithmetic. -/
def fullTestTable {d n : ℕ} (g : Geometry d n) (y : Word (rowCount d n)) :
    Computation.Gaussian.Table g.F (rowCount d n) (rowCount d n) :=
  Computation.Gaussian.ofMatrix
    ((fullTestMatrix g y).submatrix (fullExponentOrder g) (fullExponentOrder g))




























/-- Executable semantic tester: eager finite arrays, Gaussian elimination, and
one natural-number comparison. Tape-program refinement remains separate. -/
def rationalRankTest (θ : ℚ) {d n : ℕ} (g : Geometry d n) [DecidableEq g.F]
    (y : Word (rowCount d n)) : Bool :=
  let η : ℚ := 1/2 - θ/2
  decide ((Computation.Gaussian.run (fullTestTable g y)).1 * η.den ≤
    η.num.toNat * rowCount d n)

















end ExpandingCodes.PolynomialStretch

end FlattenModule57

/-! Inlined whole module: ExpandingCodes.Computation.EncodedTester -/
section FlattenModule58




set_option autoImplicit false

open scoped BigOperators

namespace ExpandingCodes.Computation.EncodedTester

open EncodedGaussian Gaussian

variable {α : Type*}

/-- The second component counts actual calls to encoded field operations. -/
def power (O : Operations α) (x : α) : ℕ → α × ℕ
  | 0 => (O.one, 0)
  | k+1 => let r := power O x k; (O.mul r.1 x, r.2+1)

def product (O : Operations α) : List (α × ℕ) → α × ℕ
  | [] => (O.one, 0)
  | a :: as => let r := product O as; (O.mul a.1 r.1, a.2+r.2+1)

def sum (O : Operations α) : List (α × ℕ) → α × ℕ
  | [] => (O.zero, 0)
  | a :: as => let r := sum O as; (O.add a.1 r.1, a.2+r.2+1)



























variable {F : Type*} [Field F] {O : Operations α} {decode : α → F}



















/-- Explicit base-q digit extraction; the fixed source program must refine
this bounded enumeration using runtime quotient/remainder loops. -/
def digits (q d : ℕ) : Fin (q^d) ≃ (Fin d → Fin q) := finFunctionFinEquiv.symm

def evaluation {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (a z : Fin (q^d)) : Fin q × ℕ :=
  if (∑ i, (digits q d a i).val) ≤ R then
    product O (List.ofFn fun i : Fin d =>
      power O (digits q d z i) (digits q d a i).val)
  else (O.zero, 0)























/-- Recompute two bounded monomials per point. Reusing an evaluation table is
unnecessary for polynomial time and would complicate physical storage. -/
def term {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) (a b z : Fin (q^d)) : Fin q × ℕ :=
  if y z then
    let x := evaluation O R a z
    let w := evaluation O R b z
    (O.mul x.1 w.1, x.2+w.2+1)
  else (O.zero, 0)

def entry {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) (a b : Fin (q^d)) : Fin q × ℕ :=
  sum O (List.ofFn fun z : Fin (q^d) => term O R y a b z)

def table {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) : Table (Fin q) (q^d) (q^d) :=
  ofMatrix fun a b => (entry O R y a b).1
















































end ExpandingCodes.Computation.EncodedTester

namespace ExpandingCodes.PolynomialStretch

open Computation EncodedGaussian EncodedTester

/-- Explicit rectangular exponent enumeration, followed only by proof casts
of individual digits. It enumerates every canonical bounded exponent tuple. -/
def encodedExponentOrder {d n : ℕ} (g : Geometry d n) :
    Fin (rowCount d n) ≃ (Fin d → Fin (Fintype.card g.F)) :=
  (digits (fieldSize d n) d).trans
    (Equiv.piCongrRight fun _ => finCongr (geometry_card g).symm)





def binaryTestTable (d n : ℕ) (y : Word (rowCount d n)) :
    Gaussian.Table (Fin (fieldSize d n)) (rowCount d n) (rowCount d n) :=
  table (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
    (auxiliaryDegree (fieldSize d n) d) (fun z => decide (y z ≠ 0))
















































































/-- Executable finite-code tester. Physical TapeProgram refinement, parsing,
and a source-step bound are separate obligations. -/
def binaryRankTest (θ : ℚ) (d n : ℕ) (y : Word (rowCount d n)) : Bool :=
  let η : ℚ := 1/2-θ/2
  decide ((EncodedGaussian.run
    (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
    (binaryTestTable d n y)).1*η.den ≤ η.num.toNat*rowCount d n)












end ExpandingCodes.PolynomialStretch

end FlattenModule58

/-! Inlined whole module: ExpandingCodes.Computation.EncodedSampler -/
section FlattenModule59




set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.EncodedSampler

open EncodedGaussian EncodedTester
open ExpandingCodes.PolynomialStretch

variable {q d k b : ℕ}

def fixed (O : Operations (Fin q)) (a : Fin q) (z : Fin d → Fin q) : Fin q × ℕ :=
  sum O (List.ofFn fun j : Fin d =>
    let p := power O a j.val
    (O.mul p.1 (z j), p.2+1))

def linear (O : Operations (Fin q)) (s z : Fin d → Fin q) : Fin q × ℕ :=
  sum O (List.ofFn fun j : Fin d => (O.mul (s j) (z j), 1))

def address (O : Operations (Fin q)) (s : Fin (2*k*q*d) → Fin q)
    (i : Fin k) (z : Fin d → Fin q) : (Fin q × Fin q × Fin q) × ℕ :=
  let a := fixed O (if h : i.val < q then ⟨i.val,h⟩ else O.zero) z
  let u := linear O (fun j => s (SamplerTables.flatFour 2 k q d (((0,i),a.1),j))) z
  let v := linear O (fun j => s (SamplerTables.flatFour 2 k q d (((1,i),a.1),j))) z
  ((a.1,u.1,v.1),a.2+u.2+v.2)

def neighbor (O : Operations (Fin q)) (s : Fin (2*k*q*d) → Fin q)
    (h : Fin (k*q*q*q) → Fin b) (i : Fin k) (z : Fin d → Fin q) : Fin b :=
  let a := (address O s i z).1
  h (SamplerTables.flatFour k q q q (((i,a.1),a.2.1),a.2.2))

/-- Executable finite-index generator. Only finite-index arithmetic and field
code operations occur; quotient-field values enter only its semantic proof. -/
def matrix (n : ℕ) (O : Operations (Fin q)) (s : Fin (2*k*q*d) → Fin q)
    (h : Fin (k*q*q*q) → Fin b) : Generator (q^d) n :=
  fun z j => if ∃ i : Fin k,
    j.val = i.val*b+(neighbor O s h i (digits q d z)).val then 1 else 0































variable {F : Type*} [Field F] {O : Operations (Fin q)} {decode : Fin q → F}













end ExpandingCodes.Computation.EncodedSampler

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation EncodedGaussian EncodedTester

























































/-- The finite-index matrix from exactly the physical random-reader values.
This is a data function, not a source-runtime claim. -/
def binarySamplerFromInput (d n k beta : ℕ) (inp : NKtLB.Inputs) :
    Generator (rowCount d n) n :=
  EncodedSampler.matrix n
    (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
    (RandomTables.sampledValues inp (SamplerTables.formEntries d n k) (fieldExponent d n) 0)
    (RandomTables.sampledValues inp (SamplerTables.hashEntries d n k) beta
      (SamplerTables.formEntries d n k * fieldExponent d n))
































end ExpandingCodes.PolynomialStretch

end FlattenModule59


section FlattenModule60



set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerLayerBounds
open ExpandingCodes.PolynomialStretch
variable {q d k b : ℕ}

























































end ExpandingCodes.Computation.SamplerLayerBounds

end FlattenModule60

/-! Inlined whole module: ExpandingCodes.Computation.SamplerProgram -/
section FlattenModule61






set_option autoImplicit false
namespace ExpandingCodes.Computation.SamplerProgram
open NKtLB SamplerEvaluation
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}

def workspace (r : Fin 31 → Fin R) (i : Fin 30) : Fin R := r ⟨i.val,by omega⟩







structure Environment (r : Fin 31 → Fin R) (ell : ℕ) (m : Fin (2^ell))
    (s : TapeStore R B) : Prop where
  modulus : s.reg (r 3)=2^ell+m.val
  length : s.reg (r 19)=3*ell+1
  cardinal : s.reg (r 23)=2^ell
  square : s.reg (r 24)=2^(2*ell)




































/-- A real multiply/add step of a dot product. Coefficient and point input
registers are caller data; the 31-register workspace contains only scalar
field values and bounded scratch counters. -/
def term (r : Fin 31 → Fin R) (x y : Fin R) : TapeProgram R B 849 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (TapeMacros.copy x (r 27) (r 2)) (TapeMacros.copy y (r 28) (r 2)))
      (multiplyFrom (workspace r))) (TapeMacros.copy (r 29) (r 27) (r 2)))
        (TapeMacros.copy (r 30) (r 28) (r 2))) (addFrom (workspace r)))
          (TapeMacros.copy (r 29) (r 30) (r 2))




































































































def dotLabels : List (Fin R × Fin R) → ℕ
  | [] => 1
  | _::ps => dotLabels ps+849

/-- A finite, statically unrolled dot product. Tail-first execution agrees
exactly with the right-associated encoded sum, avoiding reassociation assumptions. -/
def dot (r : Fin 31 → Fin R) : (ps : List (Fin R × Fin R)) → TapeProgram R B (dotLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (dot r ps) (term r p.1 p.2)

def dotValue (ell : ℕ) (h : 0<ell) (m : Fin (2^ell)) (values : Fin R → Fin (2^ell)) :
    List (Fin R × Fin R) → Fin (2^ell) → Fin (2^ell)
  | [],c => c
  | p::ps,c => BinaryField.addIndex ell
      (BinaryField.multiplyIndex ell h m (indexEquiv ell (values p.1)) (indexEquiv ell (values p.2)))
      (dotValue ell h m values ps c)



























































def dotFromZero (r : Fin 31 → Fin R) (ps : List (Fin R × Fin R)) :
    TapeProgram R B (2+dotLabels ps) := TapeProgram.seq (TapeMacros.clear (r 30)) (dot r ps)









































/-- Actual source program for a fixed-dimensional encoded linear form. -/
def linear {d : ℕ} (r : Fin 31 → Fin R) (coeff point : Fin d → Fin R) :
    TapeProgram R B (2+dotLabels (List.ofFn (fun i => (coeff i,point i)))) :=
  dotFromZero r (List.ofFn (fun i => (coeff i,point i)))




































def powerWorkspace (r : Fin 32 → Fin R) (i : Fin 31) : Fin R := r ⟨i.val,by omega⟩
























/-- One actual power multiplication. Register31 keeps the successive power;
all runtime arithmetic still executes the shared physical field routines. -/
def powerStep (r : Fin 32 → Fin R) (x : Fin R) : TapeProgram R B 862 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 30))
    (term (powerWorkspace r) (r 31) x)) (TapeMacros.copy (r 30) (r 31) (r 2))


















































def powerLabels : ℕ → ℕ
  | 0 => 1
  | j+1 => 862+powerLabels j

def powerCore (r : Fin 32 → Fin R) (x : Fin R) : (j : ℕ) → TapeProgram R B (powerLabels j)
  | 0 => TapeProgram.skip
  | j+1 => TapeProgram.seq (powerStep r x) (powerCore r x j)















































/-- Actual fixed-exponent field power; exponent j affects finite control only. -/
def powerFromOne (r : Fin 32 → Fin R) (x : Fin R) (j : ℕ) :
    TapeProgram R B (4+powerLabels j) :=
  TapeProgram.seq (SourceFieldArithmetic.setOne (r 31)) (powerCore r x j)






































def vectorIndex {d : ℕ} (j : Fin d) (i : Fin 12) : Fin 11 ⊕ Fin d :=
  if hi : i.val<11 then .inl ⟨i.val,hi⟩ else .inr j

def vectorLayout {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (j : Fin d) : Fin 12 → Fin R :=
  r ∘ vectorIndex j

























def vectorLabels {d : ℕ} (c : ℕ) : List (Fin d) → ℕ
  | [] => 1
  | j::js => coefficientLoadLabels c d j.val+vectorLabels c js

/-- Static coefficient-vector loader. A separate caller counter stores each
coordinate, while each coefficient is found by a real physical table lookup. -/
def vectorLoad {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (b : Fin B) (c : ℕ) :
    (js : List (Fin d)) → TapeProgram R B (vectorLabels c js)
  | [] => TapeProgram.skip
  | j::js => TapeProgram.seq (coefficientLoad (vectorLayout r j) b c d j.val) (vectorLoad r b c js)

def vectorAddress {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (c : ℕ) (j : Fin d)
    (s : TapeStore R B) : ℕ := d*(s.reg (r (.inl 0))+c*s.reg (r (.inl 1)))+j.val

def vectorTimeBound (c d M : ℕ) : ℕ := (112+6*c+6*d*(c+1)+2*d)*(M+1)^2

















































































def allCoefficients {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (b : Fin B) (c : ℕ) :
    TapeProgram R B (vectorLabels c (List.finRange d)) := vectorLoad r b c (List.finRange d)




















/-- Semantic interpretation of one scalar caller counter, used only in proofs;
the physical evaluator still consists solely of the finite source routines. -/
def scalarValue (ell : ℕ) (s : TapeStore R B) (i : Fin R) : Fin (2^ell) :=
  if h : s.reg i<2^ell then ⟨s.reg i,h⟩ else ⟨0,Nat.two_pow_pos ell⟩





























def powerField {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (i : Fin 32) : Fin R :=
  r (.inl ⟨i.val,by omega⟩)























def powerCoefficientLabels (j : ℕ) : ℕ := (4+powerLabels j)+11

def powerCoefficient {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (j : Fin d) :
    TapeProgram R B (powerCoefficientLabels j.val) :=
  TapeProgram.seq (powerFromOne (powerField r) (r (.inl 32)) j.val)
    (TapeMacros.copy (powerField r 31) (r (.inr j)) (powerField r 2))

def powerCoefficientTimeBound (d M : ℕ) : ℕ := (d+2)*(13440*(M+1)^6)































































def powerVectorLabels {d : ℕ} : List (Fin d) → ℕ
  | [] => 1
  | j::js => powerCoefficientLabels j.val+powerVectorLabels js

def powerVector {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) :
    (js : List (Fin d)) → TapeProgram R B (powerVectorLabels js)
  | [] => TapeProgram.skip
  | j::js => TapeProgram.seq (powerCoefficient r j) (powerVector r js)









































def allPowers {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) :
    TapeProgram R B (powerVectorLabels (List.finRange d)) := powerVector r (List.finRange d)

















def fixedPowerIndex {d : ℕ} : Fin 33 ⊕ Fin d → Fin 33 ⊕ (Fin d ⊕ Fin d)
  | .inl i => .inl i
  | .inr j => .inr (.inl j)

def fixedPowerLayout {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : Fin 33 ⊕ Fin d → Fin R :=
  r ∘ fixedPowerIndex

def fixedFieldLayout {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : Fin 31 → Fin R :=
  powerWorkspace (powerField (fixedPowerLayout r))

def fixedCoeff {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) (j : Fin d) : Fin R := r (.inr (.inl j))
def fixedPoint {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) (j : Fin d) : Fin R := r (.inr (.inr j))











































def fixedLabels {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : ℕ :=
  powerVectorLabels (List.finRange d)+(2+dotLabels (List.ofFn (fun i => (fixedCoeff r i,fixedPoint r i))))

/-- Actual fixed-form evaluator: compute the statically many powers of the
runtime layer element, then evaluate the exact encoded sum of scalar products. -/
def fixed {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : TapeProgram R B (fixedLabels r) :=
  TapeProgram.seq (allPowers (fixedPowerLayout r)) (linear (fixedFieldLayout r) (fixedCoeff r) (fixedPoint r))

def fixedTimeBound (d M : ℕ) : ℕ := d*(powerCoefficientTimeBound d M+1)+1+(d+1)*(13320*(M+1)^6)














































def randomLinearLabels {d : ℕ} (v : Fin 11 ⊕ Fin d → Fin R) (point : Fin d → Fin R) (c : ℕ) : ℕ :=
  vectorLabels c (List.finRange d)+(2+dotLabels (List.ofFn (fun j => (v (.inr j),point j))))

/-- Actual runtime-addressed random linear form: load all d coefficients from
physical tape cells, then execute the finite scalar linear-form evaluator. -/
def randomLinear {d : ℕ} (v : Fin 11 ⊕ Fin d → Fin R) (f : Fin 31 → Fin R)
    (point : Fin d → Fin R) (b : Fin B) (c : ℕ) : TapeProgram R B (randomLinearLabels v point c) :=
  TapeProgram.seq (allCoefficients v b c) (linear f (fun j => v (.inr j)) point)

def randomLinearTimeBound (c d M : ℕ) : ℕ := d*(vectorTimeBound c d M+1)+1+(d+1)*(13320*(M+1)^6)





















































namespace Storage
/-- Concrete finite sampler storage; dimensions and arity are static program
parameters. All input-dependent quantities remain counter or buffer data. -/
def registers (d k : ℕ) : ℕ := 80+4*d+k

def low (d k : ℕ) (i : Fin 80) : Fin (registers d k) := ⟨i.val,by unfold registers; omega⟩
def point (d k : ℕ) (j : Fin d) : Fin (registers d k) := ⟨80+j.val,by unfold registers; have := j.isLt; omega⟩
def countdown (d k : ℕ) (j : Fin d) : Fin (registers d k) := ⟨80+d+j.val,by unfold registers; have := j.isLt; omega⟩
def coefficient (d k : ℕ) (j : Fin d) : Fin (registers d k) := ⟨80+2*d+j.val,by unfold registers; have := j.isLt; omega⟩
def neighbor (d k : ℕ) (i : Fin k) : Fin (registers d k) := ⟨80+4*d+i.val,by unfold registers; have := i.isLt; omega⟩

def field (d k : ℕ) (i : Fin 31) : Fin (registers d k) := low d k ⟨i.val,by have := i.isLt; omega⟩

def alpha (d k : ℕ) : Fin (registers d k) := low d k 69
def address (d k : ℕ) : Fin (registers d k) := low d k 70
def u (d k : ℕ) : Fin (registers d k) := low d k 71
def v (d k : ℕ) : Fin (registers d k) := low d k 72
def hashIndex (d k : ℕ) : Fin (registers d k) := low d k 73
def bucket (d k : ℕ) : Fin (registers d k) := low d k 74

def pointPairs (d k : ℕ) : List (Fin (registers d k) × Fin (registers d k)) :=
  (List.finRange d).map (fun j => (point d k j,countdown d k j))

theorem low_injective (d k : ℕ) : Function.Injective (low d k) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  exact Fin.ext hh











@[simp] theorem low_val (d k : ℕ) (i : Fin 80) : (low d k i).val=i.val := rfl



@[simp] theorem neighbor_val (d k : ℕ) (i : Fin k) : (neighbor d k i).val=80+4*d+i.val := rfl
end Storage

namespace Storage

def fixedCommon (d k : ℕ) (i : Fin 33) : Fin (registers d k) :=
  if hi : i.val<32 then low d k ⟨i.val,by omega⟩ else alpha d k

def fixedLayout (d k : ℕ) : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin (registers d k)
  | .inl i => fixedCommon d k i
  | .inr (.inl j) => coefficient d k j
  | .inr (.inr j) => point d k j

def formCommon (d k : ℕ) : Fin 11 → Fin (registers d k) :=
  ![address d k,low d k 23,low d k 0,low d k 1,low d k 2,low d k 4,
    low d k 5,low d k 6,low d k 7,low d k 8,low d k 9]

def formLayout (d k : ℕ) : Fin 11 ⊕ Fin d → Fin (registers d k)
  | .inl i => formCommon d k i
  | .inr j => coefficient d k j

def hashLayout (d k : ℕ) : Fin 8 → Fin (registers d k) :=
  ![low d k 23,address d k,u d k,v d k,hashIndex d k,low d k 53,low d k 54,low d k 55]

def hashReadLayout (d k : ℕ) : Fin 8 → Fin (registers d k) :=
  ![hashIndex d k,low d k 39,low d k 56,low d k 57,low d k 58,low d k 59,bucket d k,low d k 53]
end Storage

def saveField (d k : ℕ) (dst : Fin 80) : TapeProgram (Storage.registers d k) 2 11 :=
  TapeMacros.copy (Storage.low d k 30) (Storage.low d k dst) (Storage.low d k 53)

def layerLabels (d k : ℕ) (i : Fin k) : ℕ :=
  (((((((2+ParameterPrograms.raiseLabels i.val)+fixedLabels (Storage.fixedLayout d k))+11)+
    randomLinearLabels (Storage.formLayout d k) (Storage.point d k) i.val)+11)+
      randomLinearLabels (Storage.formLayout d k) (Storage.point d k) (i.val+k))+11)+hashedColumnLabels i.val

/-- Concrete finite sampler layer. All labels and register locations depend
only on fixed d,k,i. Runtime n,q,ell,b and table values are data throughout. -/
def layer (d k : ℕ) (i : Fin k) : TapeProgram (Storage.registers d k) 2 (layerLabels d k i) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (ParameterPrograms.loadConstant (Storage.alpha d k) i.val)
      (fixed (Storage.fixedLayout d k))) (saveField d k 70))
        (randomLinear (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) i.val))
          (saveField d k 71))
            (randomLinear (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) (i.val+k)))
              (saveField d k 72))
                (hashedColumn (Storage.hashLayout d k) (Storage.hashReadLayout d k)
                  (Storage.neighbor d k i) (Storage.low d k 53) (1 : Fin 2) i.val)

def layerTimeBound (d k : ℕ) (i : Fin k) (M : ℕ) : ℕ :=
  fixedTimeBound d M+randomLinearTimeBound i.val d M+randomLinearTimeBound (i.val+k) d M+
    hashedColumnTimeBound i.val M+22*M+2*i.val+30



























/-- One clock for every statically unrolled layer. -/
def layerTimeUniform (d k M : ℕ) : ℕ := Finset.univ.sum (fun i : Fin k => layerTimeBound d k i M)















namespace Storage



















































































































































































end Storage




namespace Storage


































































end Storage





/-- The two sampler tables as actual explicit thermometer-buffer cells. -/
structure PhysicalTables (d k ell b : ℕ)
    (forms : Fin (2*k*(2^ell)*d) → Fin (2^ell))
    (hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b) (s : TapeStore R 2) : Prop where
  formMarked : TapeArrays.BottomMarked s 0
  hashMarked : TapeArrays.BottomMarked s 1
  formTable : TapeArrays.ThermometerTable s 0 (2^ell) (fun i => (forms i).val)
  hashTable : TapeArrays.ThermometerTable s 1 b (fun i => (hashes i).val)









/-- Stable phase invariant for the concrete sampler layer. All input-dependent
quantities here are semantic counter/buffer values, not finite-code parameters. -/
structure LayerInvariant (d k ell b : ℕ) (h : 0<ell)
    (forms : Fin (2*k*(2^ell)*d) → Fin (2^ell))
    (hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b) (z : Fin d → Fin (2^ell))
    (M : ℕ) (s : TapeStore (Storage.registers d k) 2) : Prop where
  field : Environment (Storage.field d k) ell (selectedIndex ell h) s
  buckets : s.reg (Storage.low d k 39)=b
  points : ∀ j,s.reg (Storage.point d k j)=(z j).val
  counters : ∀ r,s.reg r     ≤     M
  heads : ∀ t,s.bufferHead t     ≤     M
  tables : PhysicalTables d k ell b forms hashes s

/-- Uniform scalar/table caps sufficient for all accesses in any one layer. -/
structure LayerCaps (d k ell b M : ℕ) : Prop where
  formHead : 1+(2*k*(2^ell)*d)*(2^ell)     ≤     M
  hashHead : 1+(k*(2^ell)*(2^ell)*(2^ell))*b     ≤     M
  middle : 2*k*(2^ell)     ≤     M
  columns : k*b     ≤     M

/-- Conservative finite write footprint of one layer. Point data, countdowns,
setup counters, row controls and every other neighbor lie outside it. -/
def LayerWritable (d k : ℕ) (i : Fin k) (x : Fin (Storage.registers d k)) : Prop :=
  x.val<32 ∨ (53  ≤  x.val ∧ x.val<60) ∨ (69  ≤  x.val ∧ x.val<75) ∨
    (80+2*d  ≤  x.val ∧ x.val<80+3*d) ∨ x=Storage.neighbor d k i

def LayerFrame (d k : ℕ) (i : Fin k) (s e : TapeStore (Storage.registers d k) 2) : Prop :=
  ∀ x,¬LayerWritable d k i x → e.reg x=s.reg x














































































































































































































def formSlice {d k ell : ℕ} (forms : Fin (2*k*(2^ell)*d) → Fin (2^ell))
    (r : Fin 2) (i : Fin k) (a : Fin (2^ell)) (j : Fin d) : Fin (2^ell) :=
  forms (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j))






















































































































































































































































































































end ExpandingCodes.Computation.SamplerProgram

end FlattenModule61

/-! Inlined whole module: ExpandingCodes.Computation.TesterPowers -/
section FlattenModule62


set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterPowers
open NKtLB SamplerEvaluation SamplerProgram
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}

/-- Fixed scalar workspace plus one runtime exponent countdown. -/
def scalar (r : Fin 33 → Fin R) (i : Fin 32) : Fin R := r ⟨i.val,by omega⟩















/-- The transition table is independent of the exponent, field size and input.
Every multiplication runs the physical binary-field source program. -/
def powerLoop (r : Fin 33 → Fin R) (x : Fin R) : TapeProgram R B 864 :=
  TapeProgram.countedLoop (powerStep (scalar r) x) (r 32)




















































/-- Preserve the runtime exponent while loading a fresh countdown, initialize
one, then execute the actual counted field-power loop. -/
def power (r : Fin 33 → Fin R) (x exponent : Fin R) : TapeProgram R B 879 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy exponent (r 32) (r 2))
    (SourceFieldArithmetic.setOne (r 31))) (powerLoop r x)



















































/-- Append one monomial factor. Its exponent is a runtime caller counter;
the product accumulator is outside the shared scalar workspace. -/
def factor (r : Fin 33 → Fin R) (out exponent x : Fin R) : TapeProgram R B 1752 :=
  TapeProgram.seq (TapeProgram.seq (power r x exponent) (powerStep (scalar r) out))
    (TapeMacros.copy (r 31) out (r 2))

















































def productLabels : List (Fin R × Fin R) → ℕ
  | [] => 1
  | _::ps => productLabels ps+1752

/-- A statically unrolled dimension, with independently bounded runtime powers. -/
def productCore (r : Fin 33 → Fin R) (out : Fin R) :
    (ps : List (Fin R × Fin R)) → TapeProgram R B (productLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (productCore r out ps) (factor r out p.1 p.2)

def productValue (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (exponents : Fin R → ℕ) : List (Fin R × Fin R) → Fin (2^ell)
  | [] => BinaryField.oneIndex ell
  | p::ps => (BinaryField.indexOperations ell h).mul
      (EncodedTester.power (BinaryField.indexOperations ell h) (values p.2) (exponents p.1)).1
      (productValue ell h values exponents ps)












































/-- Initialize the accumulator to the canonical field one before the finite
product code. Exponents remain runtime values throughout. -/
def product (r : Fin 33 → Fin R) (out : Fin R) (ps : List (Fin R × Fin R)) :
    TapeProgram R B (4+productLabels ps) :=
  TapeProgram.seq (SourceFieldArithmetic.setOne out) (productCore r out ps)










































end ExpandingCodes.Computation.TesterPowers

end FlattenModule62

/-! Inlined whole module: ExpandingCodes.Computation.TesterEvaluation -/
section FlattenModule63



set_option autoImplicit false
open scoped BigOperators
namespace ExpandingCodes.Computation.TesterEvaluation
open NKtLB SamplerEvaluation SamplerProgram TesterPowers
open FieldPrograms UnaryArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}

def sumLabels : List (Fin R) → ℕ
  | [] => 1
  | _::ps => sumLabels ps+9

def sumCore (dst tmp : Fin R) : (ps : List (Fin R)) → TapeProgram R B (sumLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (sumCore dst tmp ps) (TapeMacros.addPreserving p dst tmp)

def sumValue (values : Fin R → ℕ) (ps : List (Fin R)) : ℕ := (ps.map values).sum














































/-- The finite sum routine preserves every digit counter. -/
def sumDigits (dst tmp : Fin R) (ps : List (Fin R)) : TapeProgram R B (4+sumLabels ps) :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear dst) (TapeMacros.clear tmp)) (sumCore dst tmp ps)




































/-- Caller locations: result0, degree1, exponent-sum2, comparison flag3. -/
def comparison (r : Fin 33 → Fin R) (c : Fin 4 → Fin R) : Fin 6 → Fin R :=
  ![c 1,c 2,c 3,r 0,r 1,r 2]







/-- Total-degree guard around the physical monomial evaluator. It has a finite
code table determined by the static digit-register list, not its contents. -/
def evaluate (r : Fin 33 → Fin R) (c : Fin 4 → Fin R) (ps : List (Fin R × Fin R)) :
    TapeProgram R B (((4+sumLabels (ps.map Prod.fst))+33)+((4+productLabels ps)+2+2)) :=
  TapeProgram.seq (TapeProgram.seq (sumDigits (c 2) (r 2) (ps.map Prod.fst))
    (ParameterPrograms.lessThan (comparison r c)))
      (TapeProgram.branchZero (c 3) (TesterPowers.product r (c 0) ps) (TapeMacros.clear (c 0)))









/-- The exact encoded list semantics; canonical odometer digits instantiate the
list in the full eager Gram construction. -/
def value (ell : ℕ) (h : 0<ell) (degree : ℕ)
    (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ) (ps : List (Fin R × Fin R)) : Fin (2^ell) :=
  if sumValue exponents (ps.map Prod.fst)  ≤  degree then productValue ell h values exponents ps
  else BinaryField.zeroIndex ell


def timeBound (d M : ℕ) : ℕ :=
  (d+1)*(8*M+10)+64*(M+1)+max ((d+1)*(27020*(M+1)^7)) (M+1)+4





















































































































































































































/-- Five scalar counters: q0 is preserved; result4 receives the degree cutoff.
The dimension affects only a finite static number of unary additions. -/
def degree (r : Fin 5 → Fin R) (d : ℕ) : TapeProgram R B (((((11+2)+2)+SamplerEvaluation.scaleLabels (d-3))+2)+9) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 0) (r 1) (r 3)) (SamplerOdometer.decrement (r 1)))
    (TapeMacros.clear (r 2))) (SamplerEvaluation.scaleAdd (r 1) (r 2) (r 3) (d-3)))
    (SamplerOdometer.decrement (r 2))) (FieldPrograms.halve (r 2) (r 4) (r 3))

def degreePrepare (r : Fin 5 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg (r 1) (s.reg (r 0)-1)).setReg (r 3) 0).setReg (r 2) 0

def degreeScaled (r : Fin 5 → Fin R) (d : ℕ) (s : TapeStore R B) : TapeStore R B :=
  SamplerEvaluation.scaleStore (r 1) (r 2) (r 3) (d-3) (degreePrepare r s)

def degreeStore (r : Fin 5 → Fin R) (d : ℕ) (s : TapeStore R B) : TapeStore R B :=
  FieldPrograms.halfStore ((degreeScaled r d s).setReg (r 2) ((d-3)*(s.reg (r 0)-1)-1)) (r 2) (r 4) (r 3)




























































































end ExpandingCodes.Computation.TesterEvaluation

end FlattenModule63

/-! Inlined whole module: ExpandingCodes.Computation.TesterInput -/
section FlattenModule64



set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterInput
open NKtLB SamplerEvaluation
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}

/-- The current RO0 input bit, normalized to a unary zero or one. -/
def bit (inp : Inputs) (p : ℕ) : ℕ := if Machine.readRO inp.input p=.one then 1 else 0



def readBit (a : Fin R) : TapeProgram R B 4 where
  entry := 0
  code j := if j=0 then .read 0 (fun s => if s=.one then 1 else 2)
    else if j=1 then .inc a 3 else if j=2 then .jump 3 else .halt

def readBitStore (a : Fin R) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  { s.setReg a (s.reg a+bit inp (s.roHead 0)) with
    roHead := Function.update s.roHead 0 (s.roHead 0+1) }


















/-- Four scalar registers: preserved q0, consumed width1, bit2, copy scratch3.
One input bit becomes one physical q-cell thermometer block. -/
def block (r : Fin 4 → Fin R) (b : Fin B) : TapeProgram R B 24 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 2)) (readBit (r 2)))
    (TapeMacros.copy (r 0) (r 1) (r 3))) (TapeArrays.writeBlock (r 2) (r 1) b)

def blockPrepare (r : Fin 4 → Fin R) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  (((readBitStore (r 2) inp (s.setReg (r 2) 0)).setReg (r 1) (s.reg (r 0))).setReg (r 3) 0)

def blockStore (r : Fin 4 → Fin R) (b : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  TapeArrays.writeBlockStore (r 2) (r 1) b (bit inp (s.roHead 0)) (s.reg (r 0)) (blockPrepare r inp s)










def advanced (s : TapeStore R B) : TapeStore R B :=
  {s with roHead := Function.update s.roHead 0 (s.roHead 0+1)}






















































/-- Runtime m-fold input storage. Neither m nor q enters this code table. -/
def loadLayout (r : Fin 5 → Fin R) (i : Fin 4) : Fin R := r i.castSucc







def load (r : Fin 5 → Fin R) (b : Fin B) : TapeProgram R B 26 :=
  TapeProgram.countedLoop (block (loadLayout r) b) (r 4)

def loadStore (r : Fin 5 → Fin R) (b : Fin B) (inp : Inputs) (n : ℕ) (s : TapeStore R B) : TapeStore R B :=
  SourceFieldArithmetic.loopResult (r 4) (blockStore (loadLayout r) b inp) n s







/-- Prefix invariant for the eager q-cell input table. All already written cells
are retained while the next bit is read and appended. -/
structure Loading (r : Fin 5 → Fin R) (b : Fin B) (q M start N : ℕ)
    (y : Fin N → Bool) (rem : ℕ) (s : TapeStore R B) : Prop where
  remaining : rem ≤ N
  bounded : ∀ j,s.reg j ≤ M
  width : s.reg (r 0)=q
  positive : 1 ≤ q
  inputHead : s.roHead 0=start+(N-rem)
  head : s.bufferHead b=1+(N-rem)*q
  marked : TapeArrays.BottomMarked s b
  table : ∀ j : Fin N,j.val<N-rem → TapeArrays.ThermometerAt s b (TapeArrays.entryOffset j.val q) q (if y j then 1 else 0)








































































































































































end ExpandingCodes.Computation.TesterInput

end FlattenModule64

/-! Inlined whole module: ExpandingCodes.Computation.ParameterPower -/
section FlattenModule65


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- One actual multiplication and copy. Registers: base 0, accumulator 1,
product 2, unary arithmetic scratch 3 and 4, outer loop count 5. -/
def powerStep (r : Fin 6 → Fin R) : TapeProgram R B 35 :=
  TapeProgram.seq (multiply (r 0) (r 1) (r 2) (r 3) (r 4))
    (TapeMacros.copy (r 2) (r 1) (r 3))

def powerStepStore (r : Fin 6 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let dm := multiplyStore d (r 0) (r 1) (r 2) (r 3) (r 4)
  (dm.setReg (r 1) (dm.reg (r 2))).setReg (r 3) 0

























































/-- The exponent is a unary runtime counter loaded from a fixed program
constant. This loop has 37 labels regardless of input size or exponent value. -/
def powerLoop (r : Fin 6 → Fin R) : TapeProgram R B 37 :=
  TapeProgram.countedLoop (powerStep r) (r 5)

def powerLoopStore (r : Fin 6 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d.setReg (r 5) 0
  | n+1, d => powerLoopStore r n (powerStepStore r (d.setReg (r 5) n))




















































































/-- Load the fixed exponent into the outer loop counter before executing a
uniform multiplication loop. Only this fixed exponent affects the code size. -/
def fixedPowerLabels (e : ℕ) : ℕ := (2+raiseLabels 1)+(2+raiseLabels e)+37

def fixedPower (r : Fin 6 → Fin R) (e : ℕ) : TapeProgram R B (fixedPowerLabels e) :=
  TapeProgram.seq (TapeProgram.seq (loadConstant (r 1) 1) (loadConstant (r 5) e))
    (powerLoop r)

def powerPrepare (r : Fin 6 → Fin R) (e : ℕ) (d : TapeStore R B) : TapeStore R B :=
  (d.setReg (r 1) 1).setReg (r 5) e

def fixedPowerStore (r : Fin 6 → Fin R) (e : ℕ) (d : TapeStore R B) : TapeStore R B :=
  powerLoopStore r e (powerPrepare r e d)

















































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule65

/-! Inlined whole module: ExpandingCodes.Computation.SizeParameters -/
section FlattenModule66


set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace SizeParameters

/-- Scalar specification of the actual compare/double loop. This is not a
machine instruction: the source implementation must use unary comparison and
addition to realize one step. -/
def ceilStep (p : ℕ) (x : ℕ × ℕ) : ℕ × ℕ :=
  if x.1<p then (2*x.1,x.2+1) else x

def ceilIter (p : ℕ) : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | 0, x => x
  | t+1, x => ceilIter p t (ceilStep p x)



























































































end SizeParameters
end ExpandingCodes.Computation

end FlattenModule66

/-! Inlined whole module: ExpandingCodes.Computation.ParameterRounding -/
section FlattenModule67



set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- Runtime q is doubled by a preserving copy and unary addition; ell receives
one actual increment. The other registers remain ordinary unary scratch. -/
def doubleBody (q ell copy tmp : Fin R) : TapeProgram R B 22 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy q copy tmp)
    (TapeMacros.addPreserving copy q tmp)) (TapeMacros.increment ell)

def doubleBodyStore (q ell copy tmp : Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg copy (d.reg q)).setReg tmp 0
  let d₂ := (d₁.setReg q (d₁.reg q+d₁.reg copy)).setReg tmp 0
  d₂.setReg ell (d₂.reg ell+1)























def ceilCompareLayout (r : Fin 8 → Fin R) (j : Fin 6) : Fin R :=
  r ⟨j.val, by omega⟩







/-- The comparison result is either zero or one, so a counted loop gives a
real conditional instruction sequence without testing an entire unary value. -/
def ceilConditional (r : Fin 8 → Fin R) : TapeProgram R B 24 :=
  TapeProgram.countedLoop (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2)

def ceilConditionalStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg (r 2)=0 then d else
    doubleBodyStore (r 0) (r 6) (r 3) (r 5) (d.setReg (r 2) 0)








































/-- Registers 0,1,6 hold runtime q,p,ell; 2--5 are scratch and 7 is the
fresh outer count. Neither p nor q contributes any labels to this code table. -/
def ceilingStep (r : Fin 8 → Fin R) : TapeProgram R B 57 :=
  TapeProgram.seq (lessThan (ceilCompareLayout r)) (ceilConditional r)

def ceilingStepStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ceilConditionalStore r (lessThanStore (ceilCompareLayout r) d)

























def ceilingStepFlatStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let z := (((d.setReg (r 2) 0).setReg (r 3) 0).setReg (r 4) 0).setReg (r 5) 0
  if d.reg (r 0)<d.reg (r 1) then
    (((z.setReg (r 0) (2*d.reg (r 0))).setReg (r 3) (d.reg (r 0))).setReg (r 6) (d.reg (r 6)+1))
  else z








































































































/-- The fixed p-step outer loop. Its counter is separate from all comparison
and unary arithmetic scratch, and the code has exactly 59 labels. -/
def ceilingLoop (r : Fin 8 → Fin R) : TapeProgram R B 59 :=
  TapeProgram.countedLoop (ceilingStep r) (r 7)

def ceilingLoopStore (r : Fin 8 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d.setReg (r 7) 0
  | t+1, d => ceilingLoopStore r t (ceilingStepStore r (d.setReg (r 7) t))
















































































/-- Compute the least power of two at least p. Static initialization is joined
to a p-counted runtime loop; there are 77 labels for every runtime p. -/
def ceilingPowerTwo (r : Fin 8 → Fin R) : TapeProgram R B 77 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (loadConstant (r 0) 1)
    (TapeMacros.clear (r 6))) (TapeMacros.copy (r 1) (r 7) (r 5))) (ceilingLoop r)

def ceilingPrepare (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 0) 1).setReg (r 6) 0
  (d₁.setReg (r 7) (d₁.reg (r 1))).setReg (r 5) 0

def ceilingPowerStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ceilingLoopStore r (d.reg (r 1)) (ceilingPrepare r d)








































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule67

/-! Inlined whole module: ExpandingCodes.Computation.ParameterDivision -/
section FlattenModule68


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- The finite control remembers the remainder modulo the fixed positive k.
No instruction divides a runtime integer. Each consumed source unit executes
one decrement; each group of k units executes one quotient increment. -/
def divideLoop (src quotient : Fin R) (k : ℕ) : TapeProgram R B (k+2) where
  entry := ⟨0,by omega⟩
  code j := if hj : j.val<k then .dec src ⟨k+1,by omega⟩
    (if hnext : j.val+1<k then ⟨j.val+1,by omega⟩ else ⟨k,by omega⟩)
    else if j.val=k then .inc quotient ⟨0,by omega⟩ else .halt

def divideLoopStore (src quotient : Fin R) (k j n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  (d.setReg src 0).setReg quotient (d.reg quotient+(n+j)/k)

































































/-- Preserve the dividend in register 0, place its quotient by fixed k in 1,
and use two ordinary unary scratch registers 2,3. -/
def divideConstant (r : Fin 4 → Fin R) (k : ℕ) : TapeProgram R B (13+(k+2)) :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 0) (r 2) (r 3))
    (TapeMacros.clear (r 1))) (divideLoop (r 2) (r 1) k)

def dividePrepare (r : Fin 4 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg (r 2) (d.reg (r 0))).setReg (r 3) 0).setReg (r 1) 0

def divideConstantStore (r : Fin 4 → Fin R) (k : ℕ) (d : TapeStore R B) : TapeStore R B :=
  divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0)) (dividePrepare r d)



















































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule68

/-! Inlined whole module: ExpandingCodes.Computation.ParameterFloor -/
section FlattenModule69


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- A single actual decrement/test, joining both branches at halt. -/
def decrement (r : Fin R) : TapeProgram R B 2 where
  entry := 0
  code j := if j=0 then .dec r 1 1 else .halt













def floorCeilIndex : Fin 8 → Fin 9 := ![0,8,2,3,4,5,6,7]



def floorCeilLayout (r : Fin 9 → Fin R) : Fin 8 → Fin R := r ∘ floorCeilIndex




/-- Reuse ceiling(u+1), halve its power, and decrement its exponent. All three
operations are actual unary source routines. Registers 0,6 are outputs b,beta;
1 is the preserved positive input u; 8 holds a unary copy u+1. -/
def floorPowerTwo (r : Fin 9 → Fin R) : TapeProgram R B 104 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 1) (r 8) (r 5)) (TapeMacros.increment (r 8)))
    (ceilingPowerTwo (floorCeilLayout r))) (halfStep (r 0) (r 3) (r 4)))
    (decrement (r 6))

def floorPrepare (r : Fin 9 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg (r 8) (d.reg (r 1))).setReg (r 5) 0).setReg (r 8) (d.reg (r 1)+1)

def floorPowerStore (r : Fin 9 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let dc := ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)
  let dh := halfStepStore dc (r 0) (r 3) (r 4)
  dh.setReg (r 6) (dh.reg (r 6)-1)

















































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule69

/-! Inlined whole module: ExpandingCodes.Computation.ParameterFrames -/
section FlattenModule70





set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- Exact physical frame needed when appending setup to an input parser or
following it with random-table fills. In particular random-tape heads are fixed. -/
def SamePayload (d e : TapeStore R B) : Prop :=
  e.roHead=d.roHead ∧ e.output=d.output ∧ e.bufferTape=d.bufferTape ∧ e.bufferHead=d.bufferHead































































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule70

/-! Inlined whole module: ExpandingCodes.Computation.ParameterPolynomial -/
section FlattenModule71


set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace ParameterPrograms

/-- A scalar polynomial majorant. This is only a closure lemma for the explicit
source-step bounds proved by the actual finite programs. -/
def PolynomialMajorant (f : ℕ → ℕ) : Prop := ∃ C a, ∀ n, f n≤C*(n+1)^a

namespace PolynomialMajorant





















































end PolynomialMajorant

def powerCounterBound (e M : ℕ) : ℕ := (e+1)*(M+1)^(e+1)
def powerTimeBound (e M : ℕ) : ℕ := 512*(e+1)^3*(M+1)^(2*(e+1))
def ceilingCounterBound (M : ℕ) : ℕ := 2*M+2
def ceilingTimeBound (M : ℕ) : ℕ := 512*(M+1)^2
def divisionTimeBound (M : ℕ) : ℕ := 16*(M+1)
def floorCounterBound (M : ℕ) : ℕ := 2*M+4
def floorTimeBound (M : ℕ) : ℕ := 4096*(M+1)^2
















def setupBound₁ (d M : ℕ) : ℕ := powerCounterBound (2*d) M
def setupBound₂ (d M : ℕ) : ℕ := ceilingCounterBound (setupBound₁ d M)
def setupBound₃ (d M : ℕ) : ℕ := powerCounterBound d (setupBound₂ d M)
def setupCounterBound (d M : ℕ) : ℕ := floorCounterBound (setupBound₃ d M)
def setupTimeBound (d M : ℕ) : ℕ :=
  powerTimeBound (2*d) M+1+ceilingTimeBound (setupBound₁ d M)+1+
    powerTimeBound d (setupBound₂ d M)+1+divisionTimeBound (setupBound₃ d M)+1+
    floorTimeBound (setupBound₃ d M)















end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule71

/-! Inlined whole module: ExpandingCodes.Computation.SizeReader -/
section FlattenModule72


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace SizeReader
variable {R B : ℕ}

/-- A three-label source scanner counts consecutive input ones and consumes
one delimiter. Every iteration inspects only the current RO0 symbol. -/
def scan (r : Fin R) : TapeProgram R B 3 where
  entry := 0
  code j := if j = 0 then .read 0 (fun s => if s = .one then 1 else 2)
    else if j = 1 then .inc r 0 else .halt

def scanStore (r : Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  { d.setReg r (d.reg r+n) with
    roHead := Function.update d.roHead 0 (d.roHead 0+n+1) }

 



































/-- Clear one runtime unary size register and then scan the input prefix. -/
def sizeInput (r : Fin R) : TapeProgram R B 5 :=
  TapeProgram.seq (TapeMacros.clear r) (scan r)

def sizeStore (r : Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  { d.setReg r n with roHead := Function.update d.roHead 0 (d.roHead 0+n+1) }

 



























end SizeReader
end ExpandingCodes.Computation

end FlattenModule72

/-! Inlined whole module: ExpandingCodes.Computation.ParameterSetup -/
section FlattenModule73




set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- Eight stable outputs followed by six ordinary unary scratch registers.
The ambient map permits the sampler's fixed point/neighbor registers to live
outside this frame. -/
def setupPowerPIndex : Fin 6 → Fin 14 := ![0,1,8,9,10,11]
def setupCeilingIndex : Fin 8 → Fin 14 := ![3,1,8,9,10,11,2,12]
def setupPowerMIndex : Fin 6 → Fin 14 := ![3,4,8,9,10,11]
def setupDivisionIndex : Fin 4 → Fin 14 := ![0,5,8,9]
def setupFloorIndex : Fin 9 → Fin 14 := ![7,5,8,9,10,11,6,12,13]

def setupPowerPLayout (r : Fin 14 → Fin R) : Fin 6 → Fin R := r ∘ setupPowerPIndex
def setupCeilingLayout (r : Fin 14 → Fin R) : Fin 8 → Fin R := r ∘ setupCeilingIndex
def setupPowerMLayout (r : Fin 14 → Fin R) : Fin 6 → Fin R := r ∘ setupPowerMIndex
def setupDivisionLayout (r : Fin 14 → Fin R) : Fin 4 → Fin R := r ∘ setupDivisionIndex
def setupFloorLayout (r : Fin 14 → Fin R) : Fin 9 → Fin R := r ∘ setupFloorIndex












def setupLabels (d k : ℕ) : ℕ := (((fixedPowerLabels (2*d)+77)+fixedPowerLabels d)+(13+(k+2)))+104

/-- Actual finite setup code: n^(2d), ceiling power of two, q^d, quotient by
fixed positive k, and floor power of two. Its labels depend only on fixed d,k. -/
def setup (r : Fin 14 → Fin R) (d k : ℕ) : TapeProgram R B (setupLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (fixedPower (setupPowerPLayout r) (2*d)) (ceilingPowerTwo (setupCeilingLayout r)))
    (fixedPower (setupPowerMLayout r) d)) (divideConstant (setupDivisionLayout r) k))
    (floorPowerTwo (setupFloorLayout r))

def setupStage₁ (r : Fin 14 → Fin R) (d : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  fixedPowerStore (setupPowerPLayout r) (2*d) σ
def setupStage₂ (r : Fin 14 → Fin R) (d : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  ceilingPowerStore (setupCeilingLayout r) (setupStage₁ r d σ)
def setupStage₃ (r : Fin 14 → Fin R) (d : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  fixedPowerStore (setupPowerMLayout r) d (setupStage₂ r d σ)
def setupStage₄ (r : Fin 14 → Fin R) (d k : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  divideConstantStore (setupDivisionLayout r) k (setupStage₃ r d σ)
def setupStore (r : Fin 14 → Fin R) (d k : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  floorPowerStore (setupFloorLayout r) (setupStage₄ r d k σ)





























































































































































































/-- Complete unary-input frontend. The scanner consumes true^n,false; every
subsequent setup instruction preserves that input head and the random tape. -/
def setupInput (r : Fin 14 → Fin R) (d k : ℕ) : TapeProgram R B (5+setupLabels d k) :=
  TapeProgram.seq (SizeReader.sizeInput (r 0)) (setup r d k)







































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule73

/-! Inlined whole module: ExpandingCodes.Computation.RawIrreducibility -/
section FlattenModule74


set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.RawIrreducibility
open Polynomial
open ExpandingCodes.PolynomialStretch BinaryPolynomial BinaryField
open FieldConvolution FieldCertificates FieldPrograms

noncomputable def poly (ell : ℕ) (a : Fin (2^ell)) : (ZMod 2)[X] :=
  polynomial (indexEquiv ell a)





































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






















































































end ExpandingCodes.Computation.RawIrreducibility

end FlattenModule74

/-! Inlined whole module: ExpandingCodes.Computation.SourceModulus -/
section FlattenModule75



set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceModulus
open NKtLB FieldPrograms FieldConvolution FieldCertificates SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}

/-- Static modulus-search layout, independent of runtime ell,q. Certificate
registers0..19; q23; q-2 in24; valid25; factorcount26; answer27;
copy scratch28; found29; inner factorcount30; descending moduluscount31. -/
def certificateLayout (r : Fin 32 → Fin R) : Fin 20 → Fin R :=
  fun i => r ⟨i.val,by have := i.isLt;omega⟩
def commitLayout (r : Fin 32 → Fin R) : Fin 5 → Fin R := fun i => r (![31,27,28,29,25] i)



















def decrement (x : Fin R) : TapeProgram R B 2 where
  entry := 0
  code i := if i = 0 then .dec x 1 1 else .halt















def subtractTwo (x : Fin R) : TapeProgram R B 4 := TapeProgram.seq (decrement x) (decrement x)









def setTwo (x : Fin R) : TapeProgram R B 6 := TapeProgram.seq (setOne x) (TapeMacros.increment x)




























/-- Check a raw factor pair and clear validity if it succeeds. -/
def factorBody (r : Fin 32 → Fin R) : TapeProgram R B 324 :=
  TapeProgram.seq (TapeProgram.seq (certificate (certificateLayout r)) (requireZero (r 6) (r 25)))
    (TapeMacros.increment (r 1))
def factorBodyStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := requireStore (r 6) (r 25) (certificateResult (certificateLayout r) d)
  c.setReg (r 1) (c.reg (r 1)+1)












































def innerLoop (r : Fin 32 → Fin R) : TapeProgram R B 326 := TapeProgram.countedLoop (factorBody r) (r 30)
def innerResult (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 30) (factorBodyStore r) n d


































def innerPrepare (r : Fin 32 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (setTwo (r 1)) (TapeMacros.copy (r 24) (r 30) (r 28))
def innerPrepareStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := d.setReg (r 1) 2
  (c.setReg (r 30) (c.reg (r 24))).setReg (r 28) 0































def outerBody (r : Fin 32 → Fin R) : TapeProgram R B 345 :=
  TapeProgram.seq (TapeProgram.seq (innerPrepare r) (innerLoop r)) (TapeMacros.increment (r 0))
def outerBodyStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := innerResult r (d.reg (r 24)) (innerPrepareStore r d)
  c.setReg (r 0) (c.reg (r 0)+1)





























































def outerLoop (r : Fin 32 → Fin R) : TapeProgram R B 347 := TapeProgram.countedLoop (outerBody r) (r 26)
def outerResult (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 26) (outerBodyStore r) n d







































def candidatePrepare (r : Fin 32 → Fin R) : TapeProgram R B 45 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (TapeMacros.copy (r 23) (r 2) (r 28)) (TapeMacros.addPreserving (r 31) (r 2) (r 28)))
    (TapeMacros.clear (r 3))) (TapeMacros.clear (r 4))) (setTwo (r 0))) (setOne (r 25)))
    (TapeMacros.copy (r 24) (r 26) (r 28))
def candidatePrepareStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₁ := (d.setReg (r 2) (d.reg (r 23))).setReg (r 28) 0
  let c₂ := (c₁.setReg (r 2) (c₁.reg (r 2)+c₁.reg (r 31))).setReg (r 28) 0
  let c₃ := (((c₂.setReg (r 3) 0).setReg (r 4) 0).setReg (r 0) 2).setReg (r 25) 1
  (c₃.setReg (r 26) (c₃.reg (r 24))).setReg (r 28) 0






















































def candidateBody (r : Fin 32 → Fin R) : TapeProgram R B 409 :=
  TapeProgram.seq (TapeProgram.seq (candidatePrepare r) (outerLoop r)) (commit (commitLayout r))
def candidateBodyStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  commitStore (commitLayout r) (outerResult r (d.reg (r 24)) (candidatePrepareStore r d))
















































def candidateLoop (r : Fin 32 → Fin R) : TapeProgram R B 411 := TapeProgram.countedLoop (candidateBody r) (r 31)
def candidateResult (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 31) (candidateBodyStore r) n d
































def prepare (r : Fin 32 → Fin R) : TapeProgram R B 30 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 23) (r 24) (r 28)) (subtractTwo (r 24)))
    (TapeMacros.copy (r 23) (r 31) (r 28))) (TapeMacros.clear (r 27))) (TapeMacros.clear (r 29))
def prepareStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₁ := (d.setReg (r 24) (d.reg (r 23))).setReg (r 28) 0
  let c₂ := c₁.setReg (r 24) (c₁.reg (r 24)-2)
  let c₃ := (c₂.setReg (r 31) (c₂.reg (r 23))).setReg (r 28) 0
  (c₃.setReg (r 27) 0).setReg (r 29) 0


































/-- Fixed441-label canonical modulus constructor. Candidate moduli are visited
in descending order; every accepted index overwrites the previous answer. -/
def construct (r : Fin 32 → Fin R) : TapeProgram R B 441 := TapeProgram.seq (prepare r) (candidateLoop r)
def constructResult (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  candidateResult r (d.reg (r 23)) (prepareStore r d)
































def FactorTest (N target a b : ℕ) : Prop := ∀ j < N,FieldCertificates.CoefficientMatches a b target 0 0 j
instance (N target a b : ℕ) : Decidable (FactorTest N target a b) := by unfold FactorTest;infer_instance

def FactorSetup (r : Fin 32 → Fin R) (N target : ℕ) (d : TapeStore R B) : Prop :=
  d.reg (r 2) = target ∧ d.reg (r 3) = 0 ∧ d.reg (r 4) = 0 ∧ d.reg (r 19) = N







































































































































def OffsetFactorFree (ell : ℕ) (p : Fin (2^ell)) : Prop :=
  ∀ a < 2^ell-2,∀ b < 2^ell-2,¬ FactorTest (3*ell+1) (2^ell+p.val) (2+a) (2+b)


















def ModulusSetup (r : Fin 32 → Fin R) (ell : ℕ) (d : TapeStore R B) : Prop :=
  d.reg (r 23) = 2^ell ∧ d.reg (r 24) = 2^ell-2 ∧ d.reg (r 19) = 3*ell+1



























def modulusTest (ell p : ℕ) : Bool :=
  if hp : p < 2^ell then decide (RawIrreducibility.FactorFree ell ⟨p,hp⟩) else false

def modulusAnswer (r : Fin 32 → Fin R) (d : TapeStore R B) : Option ℕ :=
  if d.reg (r 29) = 0 then none else some (d.reg (r 27))



































/-- Mathematical projection of the descending candidate-source scan. -/
def descend (test : ℕ → Bool) : ℕ → Option ℕ → Option ℕ
  | 0,state => state
  | n+1,state => descend test n (if test n then some n else state)






































































































































































end ExpandingCodes.Computation.SourceModulus

end FlattenModule75

/-! Inlined whole module: ExpandingCodes.Computation.SourceFieldSetup -/
section FlattenModule76


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldSetup
open NKtLB FieldPrograms FieldConvolution SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}

/-- Runtime ell is preserved in register20, and q in register23. -/
def coefficientBound (r : Fin 32 → Fin R) : TapeProgram R B 31 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 19))
    (TapeMacros.addPreserving (r 20) (r 19) (r 28))) (TapeMacros.addPreserving (r 20) (r 19) (r 28)))
    (TapeMacros.addPreserving (r 20) (r 19) (r 28))) (TapeMacros.increment (r 19))
def boundStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₀ := d.setReg (r 19) 0
  let c₁ := (c₀.setReg (r 19) (c₀.reg (r 19)+c₀.reg (r 20))).setReg (r 28) 0
  let c₂ := (c₁.setReg (r 19) (c₁.reg (r 19)+c₁.reg (r 20))).setReg (r 28) 0
  let c₃ := (c₂.setReg (r 19) (c₂.reg (r 19)+c₂.reg (r 20))).setReg (r 28) 0
  c₃.setReg (r 19) (c₃.reg (r 19)+1)



















































/-- Convert the selected index into the actual ordinary monic bit-word q+p. -/
def monicWord (r : Fin 32 → Fin R) : TapeProgram R B 20 :=
  TapeProgram.seq (TapeMacros.copy (r 23) (r 3) (r 28)) (TapeMacros.addPreserving (r 27) (r 3) (r 28))
def monicStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := (d.setReg (r 3) (d.reg (r 23))).setReg (r 28) 0
  (c.setReg (r 3) (c.reg (r 3)+c.reg (r 27))).setReg (r 28) 0



























/-- Fully actual uniform setup for the shared source arithmetic environment. -/
def setup (r : Fin 32 → Fin R) : TapeProgram R B 516 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (coefficientBound r) (SourceModulus.construct r))
    (monicWord r)) (UnaryArithmetic.multiply (r 23) (r 23) (r 24) (r 28) (r 30))
def setupStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  UnaryArithmetic.multiplyStore (monicStore r (SourceModulus.constructResult r (boundStore r d)))
    (r 23) (r 23) (r 24) (r 28) (r 30)






def Environment (r : Fin 32 → Fin R) (ell : ℕ) (h : 0 < ell) (d : TapeStore R B) : Prop :=
  d.reg (r 20) = ell ∧ d.reg (r 23) = 2^ell ∧ d.reg (r 19) = 3*ell+1 ∧
    d.reg (r 3) = 2^ell+(selectedIndex ell h).val ∧ d.reg (r 24) = 2^(2*ell) ∧ d.reg (r 27) = (selectedIndex ell h).val











































































































end ExpandingCodes.Computation.SourceFieldSetup

end FlattenModule76

/-! Inlined whole module: ExpandingCodes.Computation.TesterGram -/
section FlattenModule77






set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB

/-- Scalar source workspace occupies low registers. The three d-tuples and their
separate countdowns occupy exactly 6*d additional registers. -/
abbrev Registers (d : ℕ) := Fin (80+6*d)

def low (d : ℕ) (i : Fin 80) : Registers d := ⟨i.val,by omega⟩

def digit (d : ℕ) (group : Fin 6) (i : Fin d) : Registers d :=
  ⟨80+group.val*d+i.val,by
    have hg : group.val*d ≤ 5*d := Nat.mul_le_mul_right d (by omega)
    have hi := i.isLt
    omega⟩

def scalar (d : ℕ) (i : Fin 33) : Registers d := low d ⟨i.val,by omega⟩

def termWorkspace (d : ℕ) (i : Fin 31) : Registers d := low d ⟨i.val,by omega⟩

/-- Result64, canonical degree65, sum66 and flag67. -/
def evaluationCaller (d : ℕ) : Fin 4 → Registers d := ![low d 64,low d 65,low d 66,low d 67]

def aDigits (d : ℕ) := List.ofFn (fun i : Fin d => (digit d 0 i,digit d 1 i))
def bDigits (d : ℕ) := List.ofFn (fun i : Fin d => (digit d 2 i,digit d 3 i))
def zDigits (d : ℕ) := List.ofFn (fun i : Fin d => (digit d 4 i,digit d 5 i))

def aEvaluation (d : ℕ) := TesterEvaluation.evaluate (B := 3) (scalar d) (evaluationCaller d)
  (List.ofFn fun i : Fin d => (digit d 0 i,digit d 4 i))

def bEvaluation (d : ℕ) := TesterEvaluation.evaluate (B := 3) (scalar d) (evaluationCaller d)
  (List.ofFn fun i : Fin d => (digit d 2 i,digit d 4 i))

/-- Physical input table lookup: zIndex73 and q23 are preserved, bit78 is output;
all remaining used registers are disposable scalar scratch outside the modulus. -/
def inputLookup (d : ℕ) : Fin 8 → Registers d :=
  ![low d 73,low d 23,low d 0,low d 1,low d 2,low d 4,low d 78,low d 5]

/-- Two actual bounded monomials followed by their product and field addition
into the separately preserved Gram accumulator69. -/
def maskedTerm (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (aEvaluation d) (TapeMacros.copy (B := 3) (low d 64) (low d 68) (low d 2)))
    (bEvaluation d)) (TapeMacros.copy (low d 69) (low d 30) (low d 2)))
    (SamplerProgram.term (termWorkspace d) (low d 68) (low d 64)))
    (TapeMacros.copy (low d 30) (low d 69) (low d 2))

/-- One point: look up its stored input bit, conditionally accumulate the actual
masked term, then advance the physical point odometer and flat point index. -/
def pointBody (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (SamplerEvaluation.lookup (B := 3) (inputLookup d) (2 : Fin 3))
    (TapeProgram.branchZero (low d 78) TapeProgram.skip (maskedTerm d)))
    (SamplerOdometer.program (low d 23) (low d 2) (zDigits d)))
    (TapeMacros.increment (low d 73))

/-- One Gram entry is recomputed by an eager m-point loop. Values are written
sequentially to buffer0 using their real q-cell physical width. -/
def pairBody (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
      (TapeMacros.clear (B := 3) (low d 69))
      (SamplerOdometer.initDigits (low d 23) (low d 2) (zDigits d)))
      (TapeMacros.clear (low d 73)))
      (TapeMacros.copy (low d 70) (low d 76) (low d 2)))
      (TapeProgram.countedLoop (pointBody d) (low d 76)))
      (TapeMacros.copy (low d 23) (low d 79) (low d 2)))
      (TapeArrays.writeBlock (low d 69) (low d 79) (0 : Fin 3)))
      (TapeMacros.increment (low d 77)))
      (SamplerOdometer.program (low d 23) (low d 2) (bDigits d)))
      (TapeMacros.increment (low d 72))

/-- One exponent-row: reinitialize b and run the actual m-column loop. -/
def rowBody (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (B := 3) (low d 23) (low d 2) (bDigits d))
    (TapeMacros.clear (low d 72)))
    (TapeMacros.copy (low d 70) (low d 75) (low d 2)))
    (TapeProgram.countedLoop (pairBody d) (low d 75)))
    (SamplerOdometer.program (low d 23) (low d 2) (aDigits d)))
    (TapeMacros.increment (low d 71))

/-- The complete finite eager m-by-m Gram loop. Runtime m is in register70,
q in register23, cutoff in65; y is already stored in buffer2 and buffer0's
head is at1 after its marker. This definition contains only finite compositions
of permitted scalar/control/one-cell source instructions. -/
def program (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (B := 3) (low d 23) (low d 2) (aDigits d))
    (TapeMacros.clear (low d 71)))
    (TapeMacros.clear (low d 77)))
    (TapeMacros.copy (low d 70) (low d 74) (low d 2)))
    (TapeProgram.countedLoop (rowBody d) (low d 74))

/-- Physical input loader allocation preserves the field environment. -/
def inputLayout (d : ℕ) : Fin 5 → Registers d :=
  ![low d 23,low d 79,low d 78,low d 5,low d 76]

/-- Eager input storage and all three bottom-marker writes are actual source.
The size parser has already consumed n+1 RO0 symbols; m70 and field setup are
ready. The canonical degree source is composed separately before `program`. -/
def input (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeArrays.initializeBuffer (R := 80+6*d) (0 : Fin 3))
    (TapeArrays.initializeBuffer (1 : Fin 3))) (TapeArrays.initializeBuffer (2 : Fin 3)))
    (TapeMacros.copy (low d 70) (low d 76) (low d 2)))
    (TesterInput.load (inputLayout d) (2 : Fin 3))





















































































































































































































/-- Actual initial size parser and parameter arithmetic use only the static
construction dimension; k=1 is sufficient because tester buckets are unused. -/
def parameterLayout (d : ℕ) (i : Fin 14) : Registers d := low d ⟨i.val,by omega⟩

def fieldSetupLayout (d : ℕ) (i : Fin 32) : Registers d := low d ⟨i.val,by omega⟩

def setup (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (ParameterPrograms.setupInput (B := 3) (parameterLayout d) d 1)
    (TapeMacros.copy (low d 4) (low d 70) (low d 79)))
    (TapeMacros.copy (low d 2) (low d 20) (low d 79)))
    (TapeMacros.copy (low d 3) (low d 23) (low d 79)))
    (SourceFieldSetup.setup (fieldSetupLayout d))

def degreeLayout (d : ℕ) : Fin 5 → Registers d :=
  ![low d 23,low d 0,low d 1,low d 2,low d 65]

/-- Full actual finite tester matrix prefix, fixed before runtime n,q,ell,m,y.
It parses sizeInput, computes all size/field data and the canonical modulus,
stores the received word, computes the cutoff, and executes the eager Gram code.
The transitive execution refinement of the m³ loops remains a separate obligation. -/
def construct (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (setup d) (input d))
    (TesterEvaluation.degree (degreeLayout d) d)) (program d)


end ExpandingCodes.Computation.TesterGram

end FlattenModule77

/-! Inlined whole module: ExpandingCodes.Computation.TapeRename -/
section FlattenModule78


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeInstr
variable {R B S C L : ℕ}

/-- Injecting storage names changes no control flow and executes no extra
instruction. Both register and buffer counts remain fixed program parameters. -/
def renameStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) :
    TapeInstr R B L → TapeInstr S C L
  | .halt => .halt
  | .jump j => .jump j
  | .inc r j => .inc (ρ r) j
  | .dec r z p => .dec (ρ r) z p
  | .emit b j => .emit b j
  | .read r f => .read r f
  | .buffer b f => .buffer (σ b) f



end TapeInstr

namespace TapeCfg
variable {R B S C L : ℕ}

def projectStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (c : TapeCfg S C L) : TapeCfg R B L :=
  ⟨c.pc,c.reg ∘ ρ,c.roHead,c.output,c.bufferTape ∘ σ,c.bufferHead ∘ σ⟩
end TapeCfg

namespace TapeStore
variable {R B S C L : ℕ}

def projectStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (d : TapeStore S C) : TapeStore R B :=
  ⟨d.reg ∘ ρ,d.roHead,d.output,d.bufferTape ∘ σ,d.bufferHead ∘ σ⟩




end TapeStore

namespace TapeProgram
variable {R B S C L : ℕ}

def renameStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (P : TapeProgram R B L) :
    TapeProgram S C L := ⟨P.entry,fun j => (P.code j).renameStorage ρ σ⟩















































































































end TapeProgram
end ExpandingCodes.Computation

end FlattenModule78

/-! Inlined whole module: ExpandingCodes.Computation.GaussianProgram -/
section FlattenModule79




set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianProgram

open NKtLB TapeArrays

/-- Register layout for physical Gaussian array access: persistent width 0,
scratch width 1, flat index 2, offset 3, scratch 4/5, entry value 6,
remaining cells 7, and found flag 8. The remaining fixed registers are
available for dimensions, pivot coordinates, rank and field routines. -/
abbrev Store := TapeStore 64 2

def readCurrent (b : Fin 2) : TapeProgram 64 2 48 :=
  TapeProgram.seq (TapeMacros.copy 0 1 4)
    (TapeProgram.seq (TapeMacros.clear 6) (readEntry 2 1 3 4 5 6 b))

def readPost (d : Store) (v : ℕ) : Store :=
  ((((d.setReg 1 0).setReg 3 0).setReg 4 0).setReg 5 0).setReg 6 v














def AccessBounded (d : Store) (M : ℕ) : Prop :=
  d.reg 0 ≤ M ∧ d.reg 1 ≤ M ∧ d.reg 2 ≤ M ∧ d.reg 3 ≤ M ∧
    d.reg 4 ≤ M ∧ d.reg 5 ≤ M ∧ d.reg 6 ≤ M









































































section SearchLoop

variable {R B L : ℕ}

def searchLabel (L : ℕ) (k : Fin 6) : Fin (L+6) := TapeProgram.rightLabel L k

/-- Actual finite early-exit loop. Body halt jumps to an explicit unary test;
zero advances the flat index, while positive restores the value and marks a
successful pivot. All destinations are finite labels, with no array oracle. -/
def searchLoop (P : TapeProgram R B L) (remaining value index found : Fin R) :
    TapeProgram R B (L+6) where
  entry := searchLabel L 0
  code j := match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (searchLabel L 1)
      | a => a.relabel (TapeProgram.leftLabel 6)
    | .inr k =>
      if k = 0 then .dec remaining (searchLabel L 5) (TapeProgram.leftLabel 6 P.entry)
      else if k = 1 then .dec value (searchLabel L 2) (searchLabel L 3)
      else if k = 2 then .inc index (searchLabel L 0)
      else if k = 3 then .inc value (searchLabel L 4)
      else if k = 4 then .inc found (searchLabel L 5) else .halt














































































































end SearchLoop

def pivotScan (b : Fin 2) : TapeProgram 64 2 54 := searchLoop (readCurrent b) 7 6 2 8

/-- First nonzero entry of a bounded consecutive row-major interval. A failed
search returns the first index after that interval and value zero. -/
def scanResult (a : ℕ → ℕ) : ℕ → ℕ → ℕ × ℕ
  | i, 0 => (i, 0)
  | i, n+1 => if a i = 0 then scanResult a (i+1) n else (i, a i)

theorem scanResult_spec (a : ℕ → ℕ) (i n : ℕ) :
    ((scanResult a i n).2 = 0 ∧ (scanResult a i n).1 = i+n ∧
      ∀ j, i ≤ j → j < i+n → a j = 0) ∨
    (i ≤ (scanResult a i n).1 ∧ (scanResult a i n).1 < i+n ∧
      (scanResult a i n).2 = a (scanResult a i n).1 ∧ (scanResult a i n).2 ≠ 0 ∧
      ∀ j, i ≤ j → j < (scanResult a i n).1 → a j = 0) := by
  induction n generalizing i with
  | zero => exact Or.inl ⟨rfl, by simp [scanResult], by intro j hj hj'; omega⟩
  | succ n ih =>
    by_cases ha : a i = 0
    · simp only [scanResult, if_pos ha]
      rcases ih (i+1) with h | h
      · left
        refine ⟨h.1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2.1, ?_⟩
        intro j hji hjn
        by_cases hji' : j = i
        · simpa [hji'] using ha
        · exact h.2.2 j (by omega) (by omega)
      · right
        refine ⟨by omega, by have := h.2.1; omega, h.2.2.1, h.2.2.2.1, ?_⟩
        intro j hji hjn
        by_cases hji' : j = i
        · simpa [hji'] using ha
        · exact h.2.2.2.2 j (by omega) hjn
    · right
      simp only [scanResult, if_neg ha]
      exact ⟨le_rfl, by omega, trivial, ha, by intro j hj hj'; omega⟩

def flatEntry {q m n : ℕ} (A : Gaussian.Table (Fin q) m n) (k : ℕ) : ℕ :=
  if hk : k < m*n then
    (Gaussian.toMatrix A (finProdFinEquiv.symm ⟨k,hk⟩).1 (finProdFinEquiv.symm ⟨k,hk⟩).2).val
  else 0

/-- Representation of one full rectangular matrix by actual q-cell blocks. -/
def MatrixStored {q m n : ℕ} (d : Store) (b : Fin 2) (A : Gaussian.Table (Fin q) m n) : Prop :=
  ThermometerTable d b q (fun k : Fin (m*n) => flatEntry A k.val)

structure ScanOutcome (a : ℕ → ℕ) (q i n K : ℕ) (b : Fin 2)
    (d e : Store) : Prop where
  width : e.reg 0 = q
  index : e.reg 2 = (scanResult a i n).1
  value : e.reg 6 = (scanResult a i n).2
  found : e.reg 8 = if (scanResult a i n).2 = 0 then 0 else 1
  bounded : AccessBounded e ((K+1)^2)
  head : e.bufferHead b ≤ (K+1)^2
  payload : TapeStore.SamePayload e d
  outside : ∀ r : Fin 64, 9 ≤ r.val → e.reg r = d.reg r
  otherHead : ∀ c : Fin 2, c ≠ b → e.bufferHead c = d.bufferHead c
  scratch : ∀ r : Fin 64, r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5 → e.reg r ≤ d.reg r
  remaining : e.reg 7 ≤ d.reg 7







































































































































































































































































def fetch (b : Fin 2) (address dest : Fin 64) : TapeProgram 64 2 70 :=
  TapeProgram.seq (TapeMacros.copy address 2 4)
    (TapeProgram.seq (readCurrent b) (TapeMacros.copy 6 dest 4))

def fetchPost (d : Store) (address dest : Fin 64) (v : ℕ) : Store :=
  (readPost (d.setReg 2 (d.reg address)) v).setReg dest v





























































































def writeCurrent (b : Fin 2) (address : Fin 64) : TapeProgram 64 2 60 :=
  TapeProgram.seq (TapeMacros.copy address 2 4)
    (TapeProgram.seq (TapeMacros.copy 0 1 4) (writeEntry 2 1 3 4 5 6 b))





















































































/-- Concrete setup expected by the independently implemented finite field
source routines. These are scalar unary values, never a packed matrix. -/
def FieldSetup (ell : ℕ) (h : 0 < ell) (d : Store) : Prop :=
  d.reg 0 = 2^ell ∧ d.reg 36 = 2^(2*ell) ∧ d.reg 37 = 3*ell+1 ∧
    d.reg 38 = 2^ell+(PolynomialStretch.BinaryPolynomial.selectedIndex ell h).val

def Protected (r : Fin 64) : Prop :=
  r = 0 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 16 ∨
    r = 36 ∨ r = 37 ∨ r = 38 ∨ 40 ≤ r.val

structure ScalarOutcome (d e : Store) (out : Fin 64) (v M : ℕ) : Prop where
  value : e.reg out = v
  frame : ∀ r, Protected r → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : TapeStore.SamePayload e d
  heads : e.bufferHead = d.bufferHead









abbrev ScalarFunction := (ell : ℕ) → (h : 0 < ell) →
  Fin (2^ell) → Fin (2^ell) → Fin (2^ell)

/-- An explicit contract for an actual finite source subroutine. P and its
label count are fixed outside the ell quantifier; this is a conditional source
interface, not an assertion that the required field implementations exist. -/
structure ScalarContract {L : ℕ} (P : TapeProgram 64 2 L) (f : ScalarFunction)
    (left right out : Fin 64) (C k : ℕ) : Prop where
  stops : ∀ (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ),
    FieldSetup ell h d → (∀ r, d.reg r ≤ M) →
    ∀ (a b : Fin (2^ell)), d.reg left = a.val → d.reg right = b.val →
    ∃ t e, t ≤ C*(M+1)^k ∧ P.Stops inp (d.toCfg P.entry) t e ∧
      ScalarOutcome d e.store out (f ell h a b).val M

def multiplyFunction : ScalarFunction := fun ell h =>
  (PolynomialStretch.BinaryField.indexOperations ell h).mul

def subtractFunction : ScalarFunction := fun ell h =>
  (PolynomialStretch.BinaryField.indexOperations ell h).sub

def schurArithmetic {L₁ L₂ L₃ : ℕ} (mul₁ : TapeProgram 64 2 L₁)
    (mul₂ : TapeProgram 64 2 L₂) (sub : TapeProgram 64 2 L₃) : TapeProgram 64 2 (L₁+(L₂+L₃)) :=
  TapeProgram.seq mul₁ (TapeProgram.seq mul₂ sub)









































































/-- Two concrete embeddings of the checked 374-label multiplication program.
All mapped scratch registers are below 40, outside the Gaussian loop state. -/
def mulLayout (left right out : Fin 64) (i : Fin 27) : Fin 64 :=
  #v[left,right,1,38,2,3,4,5,6,7,8,9,10,11,19,20,21,22,23,37,out,24,25,0,36,26,27][i.val]

















def schurMultiply₁ : TapeProgram 64 2 374 := SourceFieldArithmetic.multiply (mulLayout 15 13 17)
def schurMultiply₂ : TapeProgram 64 2 374 := SourceFieldArithmetic.multiply (mulLayout 17 16 18)




































def fetchSchur (b : Fin 2) : TapeProgram 64 2 210 :=
  TapeProgram.seq (fetch b 9 14) (TapeProgram.seq (fetch b 10 15) (fetch b 11 16))

structure FetchSchurOutcome (ell : ℕ) (h : 0 < ell) (b : Fin 2) (d e : Store)
    (x y z : Fin (2^ell)) (M : ℕ) : Prop where
  setup : FieldSetup ell h e
  x : e.reg 14 = x.val
  y : e.reg 15 = y.val
  z : e.reg 16 = z.val
  inverse : e.reg 13 = d.reg 13
  target : e.reg 12 = d.reg 12
  bounded : ∀ r, e.reg r ≤ M
  head : e.bufferHead b ≤ (M+1)^2
  otherHead : ∀ c, c ≠ b → e.bufferHead c = d.bufferHead c
  payload : TapeStore.SamePayload e d
  caller : ∀ r, 40 ≤ r.val → e.reg r = d.reg r





































































































def schurEntry {L : ℕ} (sub : TapeProgram 64 2 L) (input output : Fin 2) :
    TapeProgram 64 2 (210+((374+(374+L))+60)) :=
  TapeProgram.seq (fetchSchur input)
    (TapeProgram.seq (schurArithmetic schurMultiply₁ schurMultiply₂ sub) (writeCurrent output 12))








structure SchurCellState (ell : ℕ) (h : 0 < ell) (input output : Fin 2) (e : Store) (M : ℕ) : Prop where
  setup : FieldSetup ell h e
  bounded : ∀ r, e.reg r ≤ M
  inputHead : e.bufferHead input ≤ (M+1)^2
  outputHead : e.bufferHead output ≤ (M+1)^2
  inputMarked : BottomMarked e input
  outputMarked : BottomMarked e output






















































































































def subLayout (i : Fin 27) : Fin 64 :=
  #v[14,1,2,18,3,4,5,7,8,9,10,11,15,17,19,20,21,22,23,37,6,24,25,0,36,26,38][i.val]









def schurSubtract : TapeProgram 64 2 365 := SourceFieldArithmetic.addition subLayout





/-- Fully concrete 1383-label physical Schur-cell program. The inverse and
three source/output addresses remain explicit caller-provided scalar inputs. -/
def concreteSchurEntry (input output : Fin 2) : TapeProgram 64 2 1383 :=
  schurEntry schurSubtract input output

























/-- Keep the original physical rectangle and annihilate the chosen row and
column. This avoids compaction, subtype enumeration, and dynamic division in
the Schur materialization loop. -/
def paddedSchur {α : Type*} (O : EncodedGaussian.Operations α) {m n : ℕ}
    (A : Gaussian.Table α m n) (p : Fin m × Fin n) : Gaussian.Table α m n :=
  let B := Gaussian.toMatrix A
  let aInv := O.inv (B p.1 p.2)
  Gaussian.ofMatrix fun i j => O.sub (B i j) (O.mul (O.mul (B i p.2) aInv) (B p.1 j))























































end ExpandingCodes.Computation.GaussianProgram

end FlattenModule79

/-! Inlined whole module: ExpandingCodes.Computation.TesterGramCorrectness -/
section FlattenModule80




set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB
open ExpandingCodes.PolynomialStretch

def tuple (d : ℕ) (g : Fin 3) : List (SamplerOdometer.Digit (80+6*d)) :=
  List.ofFn (fun i : Fin d => (digit d ⟨2*g.val,by omega⟩ i,digit d ⟨2*g.val+1,by omega⟩ i))













































































def Numbered (d : ℕ) (g : Fin 3) (q k : ℕ) (s : TapeStore (80+6*d) 3) : Prop :=
  s.reg (low d 23)=q ∧ SamplerOdometer.Valid (low d 23) (tuple d g) s ∧
    Nat.ofDigits q (SamplerOdometer.readings (tuple d g) s)=k%q^d



































































































/-- Exactly the accumulator update performed by the positive/zero source branch. -/
def pointValue (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b z : Fin ((2^ell)^d)) (acc : Fin (2^ell)) : Fin (2^ell) :=
  if y z then (BinaryField.indexOperations ell h).add
    ((BinaryField.indexOperations ell h).mul
      (EncodedTester.evaluation (BinaryField.indexOperations ell h) D a z).1
      (EncodedTester.evaluation (BinaryField.indexOperations ell h) D b z).1) acc
  else acc

def pointTime (d M : ℕ) :=
  64*(M+1)^2+(2*TesterEvaluation.timeBound d M+13300*(M+1)^6+28*M+32)+d*(8*M+20)+6

structure Core (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (s : TapeStore (80+6*d) 3) : Prop where
  bounded : ∀ j,s.reg j ≤ M
  environment : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) s
  degree : s.reg (low d 65)=D
  size : s.reg (low d 70)=(2^ell)^d
  inputMarked : TapeArrays.BottomMarked s 2
  inputTable : TapeArrays.ThermometerTable s 2 (2^ell) (fun z => if y z then 1 else 0)
  inputHead : s.bufferHead 2 ≤ M
















































































































































































def pointPrefix (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (k : ℕ) : Fin (2^ell) :=
  (EncodedTester.sum (BinaryField.indexOperations ell h)
    ((List.ofFn fun z : Fin ((2^ell)^d) => EncodedTester.term
      (BinaryField.indexOperations ell h) D y a b z).take k)).1
















































































structure PointLoopInv (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (remaining : ℕ) (s : TapeStore (80+6*d) 3) : Prop where
  le : remaining ≤ (2^ell)^d
  core : Core d ell h D M y s
  aTuple : Numbered d 0 (2^ell) a.val s
  bTuple : Numbered d 1 (2^ell) b.val s
  zTuple : Numbered d 2 (2^ell) ((2^ell)^d-remaining) s
  index : s.reg (low d 73)=(2^ell)^d-remaining
  accumulator : s.reg (low d 69)=(pointPrefix d ell h D y a b ((2^ell)^d-remaining)).val
  high : ∀ i : Fin 80,70 ≤ i.val → i≠73 → i≠76 → i≠78 → s.reg (low d i)=origin.reg (low d i)
  payload : TapeStore.SamePayload s origin
  head : ∀ c : Fin 3,c≠2 → s.bufferHead c=origin.bufferHead c










































































































/-- The four actual entry-prefix fragments clear the sum and point index,
initialize the physical z tuple, and copy m to the point-loop countdown. -/
def pairPrepare (d : ℕ) := TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.clear (B := 3) (low d 69))
    (SamplerOdometer.initDigits (low d 23) (low d 2) (zDigits d)))
    (TapeMacros.clear (low d 73))) (TapeMacros.copy (low d 70) (low d 76) (low d 2))

















































































































def pairFinishAfter {L : ℕ} (d : ℕ) (P : TapeProgram (80+6*d) 3 L) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq P
    (TapeMacros.copy (low d 23) (low d 79) (low d 2)))
    (TapeArrays.writeBlock (low d 69) (low d 79) (0 : Fin 3)))
    (TapeMacros.increment (low d 77)))
    (SamplerOdometer.program (low d 23) (low d 2) (bDigits d)))
    (TapeMacros.increment (low d 72))







































































































































structure GramEffect (d : ℕ) (s e : TapeStore (80+6*d) 3) (q flat v : ℕ) : Prop where
  roHead : e.roHead=s.roHead
  output : e.output=s.output
  head : e.bufferHead 0=1+(flat+1)*q
  spareHead : e.bufferHead 1=s.bufferHead 1
  symbol : ∀ c k,(e.bufferTape c).getD k .blank=
    if c=0 ∧ 1+flat*q ≤ k ∧ k<1+(flat+1)*q then
      if k<1+flat*q+v then .one else .zero
    else (s.bufferTape c).getD k .blank

def pairTime (d M m : ℕ) := d*(8*M+20)+9*M+12+1+(m*(pointTime d M+2)+1)+d*(8*M+20)+10*M+17

















































def GramPrefix (d : ℕ) (q : ℕ) (value : ℕ → ℕ) (flat : ℕ) (s : TapeStore (80+6*d) 3) : Prop :=
  ∀ k,k<flat → TapeArrays.ThermometerAt s 0 (1+k*q) q (value k)




































def gramValue (d ell : ℕ) (h : 0<ell) (D : ℕ) (y : Fin ((2^ell)^d) → Bool) : ℕ → ℕ :=
  GaussianProgram.flatEntry (EncodedTester.table (BinaryField.indexOperations ell h) D y)










structure BuildState (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (origin : TapeStore (80+6*d) 3) (flat : ℕ)
    (s : TapeStore (80+6*d) 3) : Prop where
  core : Core d ell h D M y s
  index : s.reg (low d 77)=flat
  head : s.bufferHead 0=1+flat*(2^ell)
  entries : GramPrefix d (2^ell) (gramValue d ell h D y) flat s
  marked : TapeArrays.BottomMarked s 0
  spareMarked : TapeArrays.BottomMarked s 1
  spareHead : s.bufferHead 1=origin.bufferHead 1
  roHead : s.roHead=origin.roHead
  output : s.output=origin.output































/-- The real per-row prefix initializes b, clears its scalar index and installs
m in the column-loop countdown; all tape data and the a tuple are preserved. -/
def rowPrepare (d : ℕ) := TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (B := 3) (low d 23) (low d 2) (bDigits d))
    (TapeMacros.clear (low d 72))) (TapeMacros.copy (low d 70) (low d 75) (low d 2))



































































structure RowLoopInv (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (origin : TapeStore (80+6*d) 3)
    (a : Fin ((2^ell)^d)) (outer remaining : ℕ) (s : TapeStore (80+6*d) 3) : Prop where
  le : remaining ≤ (2^ell)^d
  build : BuildState d ell h D M y origin (a.val*(2^ell)^d+((2^ell)^d-remaining)) s
  aTuple : Numbered d 0 (2^ell) a.val s
  bTuple : Numbered d 1 (2^ell) ((2^ell)^d-remaining) s
  aIndex : s.reg (low d 71)=a.val
  bIndex : s.reg (low d 72)=(2^ell)^d-remaining
  outer : s.reg (low d 74)=outer


































































def rowFinishAfter {L : ℕ} (d : ℕ) (P : TapeProgram (80+6*d) 3 L) :=
  TapeProgram.seq (TapeProgram.seq P
    (SamplerOdometer.program (low d 23) (low d 2) (aDigits d))) (TapeMacros.increment (low d 71))


























































def rowTime (d M m : ℕ) := d*(8*M+20)+8*M+10+1+(m*(pairTime d M m+2)+1)+d*(8*M+20)+3


























def programPrepare (d : ℕ) := TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (B := 3) (low d 23) (low d 2) (aDigits d))
    (TapeMacros.clear (low d 71))) (TapeMacros.clear (low d 77)))
    (TapeMacros.copy (low d 70) (low d 74) (low d 2))






































































structure ProgramLoopInv (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (origin : TapeStore (80+6*d) 3)
    (remaining : ℕ) (s : TapeStore (80+6*d) 3) : Prop where
  le : remaining ≤ (2^ell)^d
  build : BuildState d ell h D M y origin (((2^ell)^d-remaining)*(2^ell)^d) s
  aTuple : Numbered d 0 (2^ell) ((2^ell)^d-remaining) s
  aIndex : s.reg (low d 71)=(2^ell)^d-remaining













































def programTime (d M m : ℕ) := d*(8*M+20)+9*M+12+1+(m*(rowTime d M m+2)+1)

































































end ExpandingCodes.Computation.TesterGram

end FlattenModule80


section FlattenModule81



set_option autoImplicit false

namespace ExpandingCodes.Computation


























end ExpandingCodes.Computation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
















end ExpandingCodes.PolynomialStretch

end FlattenModule81

/-! Inlined whole module: ExpandingCodes.Computation.TesterEnvelope -/
section FlattenModule82


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation








/-- A fixed polynomial in the tester's input-plus-output dimension. It covers
physical table lengths, scalar values and the complete parameter setup. -/
def testerEnvelope (d x : ℕ) : ℕ :=
  2+ParameterPrograms.setupCounterBound d (x+1)+(d+1)*(x+1)^3+3*(x+1)+1

structure TesterEnvelopeCovers (d n M : ℕ) : Prop where
  two : 2 ≤ M
  setup : ParameterPrograms.setupCounterBound d (n+1) ≤ M
  rows : rowCount d n+1 ≤ M
  input : n+1 ≤ M
  square : (fieldSize d n)^2 ≤ M
  coefficients : 3*fieldExponent d n+1 ≤ M
  twiceField : 2*fieldSize d n ≤ M
  gram : 1+rowCount d n*rowCount d n*fieldSize d n ≤ M
  word : 1+rowCount d n*fieldSize d n ≤ M
  digitSum : d*(fieldSize d n-1) ≤ M
  cutoff : (d-3)*(fieldSize d n-1) ≤ M








































end ExpandingCodes.PolynomialStretch

end FlattenModule82

/-! Inlined whole module: ExpandingCodes.Computation.TesterPrefix -/
section FlattenModule83



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterPrefix
open NKtLB TesterGram FieldPrograms
open ExpandingCodes.PolynomialStretch

def initialStore (d : ℕ) : TapeStore (80+6*d) 3 :=
  ⟨fun _ => 0,fun _ => 0,[],fun _ => [],fun _ => 0⟩








def sizeResult (d n : ℕ) : TapeStore (80+6*d) 3 :=
  ParameterPrograms.setupStore (parameterLayout d) d 1
    (SizeReader.sizeStore (low d 0) n (initialStore d))

def copyParameters (d : ℕ) (s : TapeStore (80+6*d) 3) : TapeStore (80+6*d) 3 :=
  let s₁ := (s.setReg (low d 70) (s.reg (low d 4))).setReg (low d 79) 0
  let s₂ := (s₁.setReg (low d 20) (s.reg (low d 2))).setReg (low d 79) 0
  (s₂.setReg (low d 23) (s.reg (low d 3))).setReg (low d 79) 0

def setupResult (d n : ℕ) : TapeStore (80+6*d) 3 :=
  SourceFieldSetup.setupStore (fieldSetupLayout d) (copyParameters d (sizeResult d n))

def setupTime (d n M : ℕ) : ℕ :=
  2*n+4+ParameterPrograms.setupTimeBound d (n+1)+21*M+25+40000*(M+1)^7

structure SetupReady (d n M : ℕ) (s : TapeStore (80+6*d) 3) : Prop where
  bounded : ∀ r,s.reg r ≤ M
  environment : SamplerProgram.Environment (termWorkspace d) (fieldExponent d n)
    (BinaryPolynomial.selectedIndex (fieldExponent d n) (fieldExponent_pos d n)) s
  size : s.reg (low d 70)=rowCount d n
  inputHead : s.roHead 0=n+1
  output : s.output=[]
  buffers : s.bufferTape=fun _ => []
  heads : s.bufferHead=fun _ => 0































































































def markers (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq
    (TapeArrays.initializeBuffer (R := 80+6*d) (0 : Fin 3))
    (TapeArrays.initializeBuffer (1 : Fin 3))) (TapeArrays.initializeBuffer (2 : Fin 3))

def markedStore (d : ℕ) (s : TapeStore (80+6*d) 3) : TapeStore (80+6*d) 3 :=
  TapeArrays.painted (TapeArrays.painted (TapeArrays.painted s 0 .bot) 1 .bot) 2 .bot





























structure InputReady (d n M : ℕ) (y : Word (rowCount d n))
    (s : TapeStore (80+6*d) 3) : Prop where
  bounded : ∀ r,s.reg r ≤ M
  environment : SamplerProgram.Environment (termWorkspace d) (fieldExponent d n)
    (BinaryPolynomial.selectedIndex (fieldExponent d n) (fieldExponent_pos d n)) s
  size : s.reg (low d 70)=rowCount d n
  output : s.output=[]
  table : TapeArrays.ThermometerTable s 2 (fieldSize d n) (fun z => if y z≠0 then 1 else 0)
  inputHead : s.bufferHead 2 ≤ M
  gramHead : s.bufferHead 0=1
  spareHead : s.bufferHead 1=1
  marked : ∀ b,TapeArrays.BottomMarked s b

def inputTime (d n M : ℕ) : ℕ :=
  7*M+14+rowCount d n*(20*(M+1)+2)+1















































































end ExpandingCodes.Computation.TesterPrefix

end FlattenModule83

/-! Inlined whole module: ExpandingCodes.Computation.TesterFrontend -/
section FlattenModule84


set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterFrontend
open NKtLB TesterGram TesterPrefix
open ExpandingCodes.PolynomialStretch

def program (d : ℕ) := TapeProgram.seq
  (TapeProgram.seq (TesterGram.setup d) (TesterGram.input d))
  (TesterEvaluation.degree (degreeLayout d) d)




































































def time (d n M : ℕ) : ℕ := setupTime d n M+inputTime d n M+2+(d+1)*(30*(M+1))
























def clock (d x M : ℕ) : ℕ :=
  (2*x+4+ParameterPrograms.setupTimeBound d (x+1))+
    (28*M+42+40000*(M+1)^7)+
    (x*(20*(M+1)+2)+(d+1)*(30*(M+1)))






















end ExpandingCodes.Computation.TesterFrontend

end FlattenModule84

/-! Inlined whole module: ExpandingCodes.Computation.GaussianGrid -/
section FlattenModule85


set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianGrid

open NKtLB GaussianProgram

def sumInto (left right dest : Fin 64) : TapeProgram 64 2 20 :=
  TapeProgram.seq (TapeMacros.copy left dest 4) (TapeMacros.addPreserving right dest 4)

def sumPost (d : Store) (left right dest : Fin 64) : Store :=
  (d.setReg dest (d.reg left+d.reg right)).setReg 4 0

































def prepareAddresses : TapeProgram 64 2 71 :=
  TapeProgram.seq (sumInto 41 42 9)
    (TapeProgram.seq (sumInto 41 43 10)
      (TapeProgram.seq (sumInto 44 42 11) (TapeMacros.copy 45 12 4)))

def addressStore (d : Store) : Store :=
  let d₁ := sumPost d 41 42 9
  let d₂ := sumPost d₁ 41 43 10
  let d₃ := sumPost d₂ 44 42 11
  (d₃.setReg 12 (d₃.reg 45)).setReg 4 0






















































































structure Coordinates {m n : ℕ} (p : Fin m × Fin n) (i : Fin m) (j : Fin n) (d : Store) : Prop where
  rowBase : d.reg 41 = i.val*n
  column : d.reg 42 = j.val
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  target : d.reg 45 = i.val*n+j.val

def materializeCell (input output : Fin 2) : TapeProgram 64 2 1454 :=
  TapeProgram.seq prepareAddresses (concreteSchurEntry input output)


















































































































def tickStore (d : Store) : Store :=
  (d.setReg 42 (d.reg 42+1)).setReg 45 (d.reg 45+1)

def cellBudget (M : ℕ) : ℕ :=
  100*(M+1)+460*((M+1)^2+1)^2+20000*(M+1)^6+3000*(M+1)^5+7

def tickBudget (M : ℕ) : ℕ := cellBudget M+7*M+12

def cellTick (input output : Fin 2) : TapeProgram 64 2 1469 :=
  TapeProgram.seq (TapeMacros.copy 50 13 4)
    (TapeProgram.seq (materializeCell input output)
      (TapeProgram.seq (TapeMacros.increment 42) (TapeMacros.increment 45)))
























































































def prefixValues {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : ℕ) (k : Fin (m*n)) : ℕ :=
  if k.val < cut then flatEntry A k.val else old k

def PrefixStored {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : ℕ) (d : Store) (b : Fin 2) : Prop :=
  TapeArrays.ThermometerTable d b q (prefixValues A old cut)
















































structure ColumnInv {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n) (i : Fin m)
    (old : Fin (m*n) → ℕ) (M : ℕ) (base : Store) (remaining : ℕ) (d : Store) : Prop where
  state : SchurCellState ell h input output d M
  columns : d.reg 40 = n
  rows : d.reg 49 = m
  rowBase : d.reg 41 = i.val*n
  columnCount : d.reg 42+remaining = n
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  cut : d.reg 45 = i.val*n+d.reg 42
  inverse : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored d input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old (d.reg 45) d output
  frame : ∀ r,40 ≤ r.val → r ≠ 42 → r ≠ 45 → r ≠ 47 → d.reg r = base.reg r
  io : d.roHead = base.roHead ∧ d.output = base.output

def columnLoop (input output : Fin 2) : TapeProgram 64 2 1471 :=
  TapeProgram.countedLoop (cellTick input output) 47














































































































def rowPrepare : TapeProgram 64 2 13 :=
  TapeProgram.seq (TapeMacros.clear 42) (TapeMacros.copy 40 47 4)

def rowPrepareStore (d : Store) : Store :=
  ((d.setReg 42 0).setReg 47 (d.reg 40)).setReg 4 0


















def rowBudget (n M : ℕ) : ℕ := n*(tickBudget M+2)+20*(M+1)

def rowBody (input output : Fin 2) : TapeProgram 64 2 1493 :=
  TapeProgram.seq rowPrepare
    (TapeProgram.seq (columnLoop input output) (TapeMacros.addPreserving 40 41 4))

structure RowStart {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n) (i : Fin m)
    (old : Fin (m*n) → ℕ) (M : ℕ) (d : Store) : Prop where
  state : SchurCellState ell h input output d M
  columns : d.reg 40 = n
  rows : d.reg 49 = m
  rowBase : d.reg 41 = i.val*n
  cut : d.reg 45 = i.val*n
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  inverse : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored d input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old (i.val*n) d output

structure RowOutcome {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n) (i : Fin m)
    (old : Fin (m*n) → ℕ) (M : ℕ) (d e : Store) : Prop where
  state : SchurCellState ell h input output e M
  columns : e.reg 40 = n
  rows : e.reg 49 = m
  nextBase : e.reg 41 = (i.val+1)*n
  nextCut : e.reg 45 = (i.val+1)*n
  pivotColumn : e.reg 43 = p.2.val
  pivotBase : e.reg 44 = p.1.val*n
  inverse : e.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored e input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old ((i.val+1)*n) e output
  columnDone : e.reg 42 = n
  countDone : e.reg 47 = 0
  frame : ∀ r,40 ≤ r.val → r ≠ 41 → r ≠ 42 → r ≠ 45 → r ≠ 47 → e.reg r = d.reg r
  io : e.roHead = d.roHead ∧ e.output = d.output


































































































structure RowsInv {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n)
    (old : Fin (m*n) → ℕ) (M : ℕ) (base : Store) (remaining : ℕ) (d : Store) : Prop where
  atMost : remaining ≤ m
  state : SchurCellState ell h input output d M
  columns : d.reg 40 = n
  rows : d.reg 49 = m
  rowBase : d.reg 41 = (m-remaining)*n
  cut : d.reg 45 = (m-remaining)*n
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  inverse : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored d input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old ((m-remaining)*n) d output
  frame : ∀ r,40 ≤ r.val → r ≠ 41 → r ≠ 42 → r ≠ 45 → r ≠ 46 → r ≠ 47 → d.reg r = base.reg r
  io : d.roHead = base.roHead ∧ d.output = base.output

def rowLoop (input output : Fin 2) : TapeProgram 64 2 1495 := TapeProgram.countedLoop (rowBody input output) 46




















































def gridPrepare : TapeProgram 64 2 15 :=
  TapeProgram.seq (TapeMacros.clear 41) (TapeProgram.seq (TapeMacros.clear 45) (TapeMacros.copy 49 46 4))

def gridPrepareStore (d : Store) : Store :=
  (((d.setReg 41 0).setReg 45 0).setReg 46 (d.reg 49)).setReg 4 0



















def materializeGrid (input output : Fin 2) : TapeProgram 64 2 1510 :=
  TapeProgram.seq gridPrepare (rowLoop input output)































































end ExpandingCodes.Computation.GaussianGrid

end FlattenModule85

/-! Inlined whole module: ExpandingCodes.Computation.GaussianPivot -/
section FlattenModule86



set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianPivot
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch

/-- A fixed finite embedding: scanned pivot6 is preserved, its inverse goes
to persistent50, and all other Gaussian caller registers40..63 stay outside. -/
def inverseLayout (i : Fin 31) : Fin 64 :=
  #v[6,1,2,38,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,37,19,20,21,0,36,22,23,50,24,25,26][i.val]








def invertPivot : TapeProgram 64 2 418 := SourceFieldArithmetic.inverse inverseLayout

structure InverseOutcome (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell))
    (d e : Store) (M : ℕ) : Prop where
  value : e.reg 50 = (BinaryField.inverseIndex ell h a).val
  pivot : e.reg 6 = d.reg 6
  setup : FieldSetup ell h e
  frame : ∀ r : Fin 64, 40 ≤ r.val → r ≠ 50 → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : TapeStore.SamePayload e d
  heads : e.bufferHead = d.bufferHead


































def coordinateDigits : List (SamplerOdometer.Digit 64) := [(43,52),(53,54)]




def coordinateStep : TapeProgram 64 2 43 := SamplerOdometer.program 40 59 coordinateDigits

 def decidablePreserves {R B L : ℕ} (r : Fin R) (i : TapeInstr R B L) :
    Decidable (TapeProgram.preservesRegister r i) := by
  cases i <;> simp only [TapeProgram.preservesRegister] <;> infer_instance








def OutsideCoordinates (r : Fin 64) : Prop :=
  r ∉ ([43,52,53,54,55,58,59] : List (Fin 64))

instance (r : Fin 64) : Decidable (OutsideCoordinates r) := by
  unfold OutsideCoordinates
  infer_instance







structure CoordinateInvariant (base : Store) (M remaining : ℕ) (s : Store) : Prop where
  remaining_le : remaining ≤ base.reg 2
  bounded : ∀ r, s.reg r ≤ M
  valid : SamplerOdometer.Valid 40 coordinateDigits s
  radix : s.reg 40 = base.reg 40
  number : Nat.ofDigits (base.reg 40) (SamplerOdometer.readings coordinateDigits s) =
    base.reg 2-remaining
  frame : ∀ r, OutsideCoordinates r → s.reg r = base.reg r
  payload : FieldConvolution.tapeData s = FieldConvolution.tapeData base

































































def coordinateInit : TapeProgram 64 2 42 :=
  TapeProgram.seq (SamplerOdometer.initDigits 40 59 coordinateDigits) (TapeMacros.copy 2 55 58)

def coordinateInitStore (d : Store) : Store :=
  ((SamplerOdometer.initializeStore 40 59 coordinateDigits d).setReg 55 (d.reg 2)).setReg 58 0




















































def coordinates : TapeProgram 64 2 111 :=
  TapeProgram.seq (TapeProgram.seq coordinateInit (TapeProgram.countedLoop coordinateStep 55))
    (UnaryArithmetic.multiply 53 40 44 56 57)

def OutsidePivotCoordinates (r : Fin 64) : Prop :=
  OutsideCoordinates r ∧ r ≠ 44 ∧ r ≠ 56 ∧ r ≠ 57

instance (r : Fin 64) : Decidable (OutsidePivotCoordinates r) := by
  unfold OutsidePivotCoordinates
  infer_instance

structure CoordinateOutcome (d e : Store) (M : ℕ) : Prop where
  col : e.reg 43 = d.reg 2 % d.reg 40
  rowBase : e.reg 44 = d.reg 2 / d.reg 40 * d.reg 40
  frame : ∀ r, OutsidePivotCoordinates r → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : FieldConvolution.tapeData e = FieldConvolution.tapeData d

























































/-- Coordinates must be recovered before inversion, whose ordinary workspace
includes the old flat-index counter. Its persistent results are43,44,50. -/
def preparePivot : TapeProgram 64 2 529 := TapeProgram.seq coordinates invertPivot

structure PivotOutcome (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell))
    (d e : Store) (M : ℕ) : Prop where
  col : e.reg 43 = d.reg 2 % d.reg 40
  rowBase : e.reg 44 = d.reg 2 / d.reg 40 * d.reg 40
  inverse : e.reg 50 = (BinaryField.inverseIndex ell h a).val
  setup : FieldSetup ell h e
  frame : ∀ r, 40 ≤ r.val → OutsidePivotCoordinates r → r ≠ 50 → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : TapeStore.SamePayload e d
  heads : e.bufferHead = d.bufferHead
  pivot : e.reg 6 = d.reg 6



































end ExpandingCodes.Computation.GaussianPivot

end FlattenModule86

/-! Inlined whole module: ExpandingCodes.Computation.PaddedGaussian -/
section FlattenModule87



set_option autoImplicit false

namespace ExpandingCodes.Computation.PaddedGaussian
open GaussianProgram EncodedGaussian
open ExpandingCodes.PolynomialStretch

variable {q m n : ℕ}

theorem scan_nonzero_lt (A : Gaussian.Table (Fin q) m n)
    (h : (scanResult (flatEntry A) 0 (m*n)).2 ≠ 0) :
    (scanResult (flatEntry A) 0 (m*n)).1 < m*n := by
  rcases scanResult_spec (flatEntry A) 0 (m*n) with hs | hs
  · exact (h hs.1).elim
  · simpa using hs.2.1

/-- The exact first-nonzero flat scan used by the physical Gaussian source.
The dependent bound constructs a finite coordinate, not a pivot choice oracle. -/
def pivot (A : Gaussian.Table (Fin q) m n) : Option (Fin m × Fin n) :=
  let s := scanResult (flatEntry A) 0 (m*n)
  if h : s.2 = 0 then none else
    some (finProdFinEquiv.symm ⟨s.1,scan_nonzero_lt A h⟩)




























































/-- Fixed-dimension eager elimination. Each iteration uses the same physical
array dimensions; the fuel bounds only the number of actual pivot attempts. -/
def run (O : Operations (Fin q)) : ℕ → Gaussian.Table (Fin q) m n → ℕ
  | 0,_ => 0
  | fuel+1,A => match pivot A with
    | none => 0
    | some p => run O fuel (paddedSchur O A p)+1

structure State (q m n : ℕ) where
  table : Gaussian.Table (Fin q) m n
  rank : ℕ
  done : Bool

/-- Logical state of one physical driver round. A no-pivot matrix is retained
with a done bit; all later rounds are exact fixed points. -/
def step (O : Operations (Fin q)) (s : State q m n) : State q m n :=
  if s.done then s else match pivot s.table with
    | none => {s with done := true}
    | some p => ⟨paddedSchur O s.table p,s.rank+1,false⟩















variable {F : Type*} [Field F] [DecidableEq F]
variable {O : Operations (Fin q)} {decode : Fin q → F}










































































end ExpandingCodes.Computation.PaddedGaussian

end FlattenModule87

/-! Inlined whole module: ExpandingCodes.Computation.GaussianDriver -/
section FlattenModule88




set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver

open NKtLB GaussianProgram GaussianGrid

section Branch
variable {R B L K : ℕ}

def zeroLabel (K : ℕ) (j : Fin L) : Fin ((L+K)+2) :=
  TapeProgram.leftLabel 2 (TapeProgram.leftLabel K j)
def positiveLabel (L : ℕ) (j : Fin K) : Fin ((L+K)+2) :=
  TapeProgram.leftLabel 2 (TapeProgram.rightLabel L j)
def branchLabel (L K : ℕ) (j : Fin 2) : Fin ((L+K)+2) := TapeProgram.rightLabel (L+K) j

/-- A real preserving zero/positive branch. The positive path decrements and
restores the tested unary counter before entering its finite program. -/
def branchZero (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) :
    TapeProgram R B ((L+K)+2) where
  entry := branchLabel L K 0
  code j := match finSumFinEquiv.symm j with
    | .inl a => match finSumFinEquiv.symm a with
      | .inl i => (P.code i).relabel (zeroLabel K)
      | .inr i => (Q.code i).relabel (positiveLabel L)
    | .inr k => if k = 0 then .dec r (zeroLabel K P.entry) (branchLabel L K 1)
      else .inc r (positiveLabel L Q.entry)





















































end Branch

def skip : TapeProgram 64 2 1 where
  entry := 0
  code _ := .halt




def scanSetup : TapeProgram 64 2 17 :=
  TapeProgram.seq (TapeMacros.clear 2)
    (TapeProgram.seq (TapeMacros.clear 6) (TapeProgram.seq (TapeMacros.clear 8) (TapeMacros.copy 51 7 63)))

def inputBuffer (b : Bool) : Fin 2 := if b then 1 else 0
def outputBuffer (b : Bool) : Fin 2 := if b then 0 else 1
def bit (b : Bool) : ℕ := if b then 1 else 0





def flip (b : Bool) : TapeProgram 64 2 2 := if b then TapeMacros.clear 60 else TapeMacros.increment 60

def afterPivot (b : Bool) : TapeProgram 64 2 2043 :=
  TapeProgram.seq GaussianPivot.preparePivot
    (TapeProgram.seq (materializeGrid (inputBuffer b) (outputBuffer b))
      (TapeProgram.seq (TapeMacros.increment 48) (flip b)))




def scanRound (b : Bool) : TapeProgram 64 2 2118 :=
  TapeProgram.seq scanSetup (TapeProgram.seq (pivotScan (inputBuffer b))
    (branchZero (TapeMacros.increment 61) (afterPivot b) 8))

def scanRound₀ : TapeProgram 64 2 2118 := scanRound false
def scanRound₁ : TapeProgram 64 2 2118 := scanRound true

def round : TapeProgram 64 2 4241 :=
  branchZero (branchZero scanRound₀ scanRound₁ 60) skip 61

def loop : TapeProgram 64 2 4243 := TapeProgram.countedLoop round 62

def initializeProgram : TapeProgram 64 2 17 :=
  TapeProgram.seq (TapeMacros.clear 48)
    (TapeProgram.seq (TapeMacros.clear 60) (TapeProgram.seq (TapeMacros.clear 61) (TapeMacros.copy 49 62 63)))

/-- Actual fixed finite physical Gaussian program. It performs at most the
runtime number of rows, swapping the two buffers only after successful pivots.
The refinement theorem is developed separately against the exact padded run. -/
def rankProgram : TapeProgram 64 2 4260 := TapeProgram.seq initializeProgram loop




def clear3Copy (r : Fin 6 → Fin 64) : TapeProgram 64 2 17 :=
  TapeProgram.seq (TapeMacros.clear (r 0)) (TapeProgram.seq (TapeMacros.clear (r 1))
    (TapeProgram.seq (TapeMacros.clear (r 2)) (TapeMacros.copy (r 3) (r 4) (r 5))))

def clear3CopyStore (r : Fin 6 → Fin 64) (d : Store) : Store :=
  ((((d.setReg (r 0) 0).setReg (r 1) 0).setReg (r 2) 0).setReg (r 4) (d.reg (r 3))).setReg (r 5) 0




























def scanLayout (i : Fin 6) : Fin 64 := #v[2,6,8,51,7,63][i.val]
def initialLayout (i : Fin 6) : Fin 64 := #v[48,60,61,49,62,63][i.val]




def scanSetupStore (d : Store) : Store := clear3CopyStore scanLayout d
def initializeStore (d : Store) : Store := clear3CopyStore initialLayout d





































structure Common (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : Store) : Prop where
  state : SchurCellState ell h 0 1 d M
  columns : d.reg 40 = m
  rows : d.reg 49 = m
  cells : d.reg 51 = m*m
  large : 1 < m




























abbrev Model (ell m : ℕ) := PaddedGaussian.State (2^ell) m m

structure Represents (ell m : ℕ) (b : Bool) (s : Model ell m) (d : Store) : Prop where
  buffer : d.reg 60 = bit b
  done : d.reg 61 = bit s.done
  rank : d.reg 48 = s.rank
  current : MatrixStored d (inputBuffer b) s.table
  spare : ∃ A : Gaussian.Table (Fin (2^ell)) m m,MatrixStored d (outputBuffer b) A










































abbrev ops (ell : ℕ) (h : 0 < ell) := PolynomialStretch.BinaryField.indexOperations ell h










































def gridBudget (m M : ℕ) : ℕ := 20*(M+1)+m*(rowBudget m M+2)+2
def successBudget (m M : ℕ) : ℕ := 21000*(M+1)^7+gridBudget m M+10
def scanBudget (m M : ℕ) : ℕ := m*m*(100*((M+1)^2+1)^2+5)+1
def roundBudget (m M : ℕ) : ℕ := 10*M+13+scanBudget m M+successBudget m M+20









































































































def scanRoundBudget (m M : ℕ) : ℕ := 10*M+13+scanBudget m M+successBudget m M+10































































































































def LoopInv (ell : ℕ) (h : 0 < ell) (m M : ℕ) (initial : Model ell m) (base : Store)
    (remaining : ℕ) (d : Store) : Prop :=
  Common ell h m M d ∧ d.roHead = base.roHead ∧ d.output = base.output ∧
    ∃ (b : Bool) (s : Model ell m),Represents ell m b s d ∧ s.rank+remaining ≤ m ∧
      ((PaddedGaussian.step (ops ell h))^[remaining] s) = ((PaddedGaussian.step (ops ell h))^[m] initial)





































































end ExpandingCodes.Computation.GaussianDriver

end FlattenModule88


section FlattenModule89


set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver
open NKtLB GaussianProgram GaussianGrid EncodedGaussian
open ExpandingCodes.PolynomialStretch






















































































































end ExpandingCodes.Computation.GaussianDriver

end FlattenModule89

/-! Inlined whole module: ExpandingCodes.Computation.TesterProgram -/
section FlattenModule90



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterProgram

open NKtLB

variable {R B : ℕ}

/-- Six fixed labels compare two runtime unary counters and emit exactly one
bit. Each iteration performs actual decrement/test instructions. -/
def compareLE (a b : Fin R) : TapeProgram R B 6 where
  entry := 0
  code j := if j = 0 then .dec a 3 1
    else if j = 1 then .dec b 4 0
    else if j = 3 then .emit true 5
    else if j = 4 then .emit false 5 else .halt

def compareTime : ℕ → ℕ → ℕ
  | 0, _ => 2
  | _+1, 0 => 3
  | a+1, b+1 => compareTime a b+2









def emitStore (d : TapeStore R B) (v : Bool) : TapeStore R B :=
  { d with output := d.output ++ [v] }



















































































/-- A fixed 54-label suffix computes both cross products and emits the exact
natural comparison. Registers 0,1 hold rank and table size; 2,3 hold the fixed
rational denominator and nonnegative numerator. Their initialization is a
separate part of the full tester. Registers 4..7 are scalar scratch. -/
def rankThreshold {B : ℕ} : TapeProgram 8 B 54 :=
  TapeProgram.seq
    (TapeProgram.seq (UnaryArithmetic.multiply 0 2 4 6 7)
      (UnaryArithmetic.multiply 1 3 5 6 7))
    (compareLE 4 5)































































































end ExpandingCodes.Computation.TesterProgram

end FlattenModule90

/-! Inlined whole module: ExpandingCodes.Computation.TesterSuffix -/
section FlattenModule91





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterSuffix
open NKtLB ParameterPrograms
variable {R B : ℕ}

def eta (θ : ℚ) : ℚ := 1/2-θ/2
def loadLabels (c : ℕ) : ℕ := 2+raiseLabels c
def labels (θ : ℚ) : ℕ := loadLabels (eta θ).den+loadLabels (eta θ).num.toNat+54

/-- Rational constants are fixed in the finite code before n. The suffix
loads both by actual increments, then executes the physical rank comparison. -/
def program (θ : ℚ) (r : Fin 8 → Fin R) : TapeProgram R B (labels θ) :=
  TapeProgram.seq (TapeProgram.seq (loadConstant (r 2) (eta θ).den)
    (loadConstant (r 3) (eta θ).num.toNat))
      (TapeProgram.renameStorage r id (TesterProgram.rankThreshold (B := B)))

def constantsStore (θ : ℚ) (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  (d.setReg (r 2) (eta θ).den).setReg (r 3) (eta θ).num.toNat

def envelope (θ : ℚ) (M : ℕ) : ℕ := max M (max (eta θ).den (eta θ).num.toNat)
def timeBound (θ : ℚ) (M : ℕ) : ℕ :=
  2*M+2*(eta θ).den+2*(eta θ).num.toNat+6+100*(envelope θ M+1)^2












































































end ExpandingCodes.Computation.TesterSuffix

end FlattenModule91

/-! Inlined whole module: ExpandingCodes.Computation.TesterBackend -/
section FlattenModule92




set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackend
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch

def suffixLayout : Fin 8 → Fin 64 := ![48,49,52,53,54,55,56,57]


/-- The entire actual Gaussian and acceptance suffix, on a fixed64-register
frame. The final tester lifts this into its larger Gram-construction frame. -/
def program (θ : ℚ) : TapeProgram 64 2 (4260+TesterSuffix.labels θ) :=
  TapeProgram.seq GaussianDriver.rankProgram (TesterSuffix.program θ suffixLayout)

def timeBound (θ : ℚ) (M : ℕ) : ℕ :=
  100000*(M+1)^9+1+TesterSuffix.timeBound θ M

































end ExpandingCodes.Computation.TesterBackend

end FlattenModule92

/-! Inlined whole module: ExpandingCodes.Computation.ZeroTables -/
section FlattenModule93


set_option autoImplicit false

namespace ExpandingCodes.Computation.ZeroTables
open NKtLB TapeArrays
variable {R B K : ℕ}

/-- The existing three-label physical zero writer consumes a runtime cell
count. Neither table length nor field width occurs in the code parameters. -/
def program (r : Fin R) (b : Fin B) : TapeProgram R B 3 := writeRun r b .zero

def result (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B) : TapeStore R B :=
  fillStore b .zero N (d.setReg r 0)


















































































end ExpandingCodes.Computation.ZeroTables

end FlattenModule93

/-! Inlined whole module: ExpandingCodes.Computation.TesterBackendPrep -/
section FlattenModule94





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendPrep
open NKtLB UnaryArithmetic FieldPrograms TapeArrays GaussianProgram
open ExpandingCodes.PolynomialStretch

abbrev BigStore := TapeStore 80 3
abbrev Pair := Fin 80 × Fin 80

def copyLabels : List Pair → ℕ
  | [] => 1
  | _::ps => 11+copyLabels ps

def copies : (ps : List Pair) → TapeProgram 80 3 (copyLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (TapeMacros.copy p.1 p.2 79) (copies ps)

def copyResult : List Pair → BigStore → BigStore
  | [],d => d
  | p::ps,d => copyResult ps ((d.setReg p.2 (d.reg p.1)).setReg 79 0)

def Valid (ps : List Pair) : Prop :=
  ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ 79 ∧ p.2 ≠ 79




























def metadataPairs : List Pair := [(23,0),(24,36),(19,37),(3,38),(70,40),(70,49)]





def beforeZero (d : BigStore) : BigStore :=
  multiplyStore (multiplyStore (copyResult metadataPairs d) 70 70 51 52 53) 51 0 54 55 56

/-- Fixed finite metadata copies, two runtime unary multiplications, and the
physical spare-matrix zero fill. No matrix or runtime size is a code parameter. -/
def program : TapeProgram 80 3 118 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (copies metadataPairs)
    (multiply 70 70 51 52 53)) (multiply 51 0 54 55 56)) (ZeroTables.program 54 1)

def result (d : BigStore) : BigStore :=
  ZeroTables.result 54 1 (d.reg 70*d.reg 70*d.reg 23) (beforeZero d)

def registerResult (d : BigStore) : BigStore :=
  (((((((((((((d.setReg 0 (d.reg 23)).setReg 36 (d.reg 24)).setReg 37 (d.reg 19)).setReg 38 (d.reg 3)).setReg 40 (d.reg 70)).setReg 49 (d.reg 70)).setReg 79 0).setReg 51 (d.reg 70*d.reg 70)).setReg 52 0).setReg 53 0).setReg 54 (d.reg 70*d.reg 70*d.reg 23)).setReg 55 0).setReg 56 0)



































































end ExpandingCodes.Computation.TesterBackendPrep

end FlattenModule94

/-! Inlined whole module: ExpandingCodes.Computation.TesterBackendComplete -/
section FlattenModule95


set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendComplete
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch
open TesterBackendPrep

def registers (i : Fin 64) : Fin 80 := ⟨i.val,by omega⟩
def buffers (i : Fin 2) : Fin 3 := ⟨i.val,by omega⟩





def project (d : BigStore) : Store := d.projectStorage registers buffers

structure Ready (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : BigStore) : Prop where
  bounded : ∀ r,d.reg r ≤ M
  q : d.reg 23 = 2^ell
  qSquared : d.reg 24 = 2^(2*ell)
  coefficientCount : d.reg 19 = 3*ell+1
  monic : d.reg 3 = 2^ell+(BinaryPolynomial.selectedIndex ell h).val
  rows : d.reg 70 = m
  large : 1 < m
  cells : m*m*(2^ell) ≤ M
  gramHead : d.bufferHead 0 ≤ (M+1)^2
  spareHead : d.bufferHead 1 = 1
  gramMarked : BottomMarked d 0
  spareMarked : BottomMarked d 1

























































def zeroTable (ell m : ℕ) : Gaussian.Table (Fin (2^ell)) m m :=
  Gaussian.ofMatrix fun _ _ => ⟨0,pow_pos (by decide) _⟩













/-- The complete fixed tester suffix: physical frame preparation followed by
the actual Gaussian rank routine and rational acceptance comparison. -/
def program (θ : ℚ) : TapeProgram 80 3 (118+(4260+TesterSuffix.labels θ)) :=
  TapeProgram.seq TesterBackendPrep.program ((TesterBackend.program θ).renameStorage registers buffers)

def timeBound (θ : ℚ) (M : ℕ) : ℕ := 150*(M+1)^2+1+TesterBackend.timeBound θ M






































end ExpandingCodes.Computation.TesterBackendComplete

end FlattenModule95

/-! Inlined whole module: ExpandingCodes.Computation.TesterAssembly -/
section FlattenModule96



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterAssembly
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch

def view (degree : ℕ) (d : TapeStore (80+6*degree) 3) : TapeStore 80 3 :=
  d.projectStorage (TesterGram.low degree) id






def backend (θ : ℚ) (degree : ℕ) :=
  (TesterBackendComplete.program θ).renameStorage (TesterGram.low degree) id

def program (θ : ℚ) (degree : ℕ) :=
  TapeProgram.seq (TesterGram.construct degree) (backend θ degree)






































end ExpandingCodes.Computation.TesterAssembly

end FlattenModule96


section FlattenModule97





set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch






























open ExpandingCodes.Computation



























































end ExpandingCodes.PolynomialStretch

end FlattenModule97


section FlattenModule98




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation






















end ExpandingCodes.PolynomialStretch

end FlattenModule98

/-! Inlined whole module: ExpandingCodes.Computation.TesterImplementation -/
section FlattenModule99





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterImplementation
open NKtLB TesterGram
open ExpandingCodes.PolynomialStretch

def clock (θ : ℚ) (d x : ℕ) : ℕ :=
  TesterFrontend.clock d x (testerEnvelope d x)+1+
    programTime d (testerEnvelope d x) x+1+
      TesterBackendComplete.timeBound θ (testerEnvelope d x)






























































end ExpandingCodes.Computation.TesterImplementation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
















end ExpandingCodes.PolynomialStretch

end FlattenModule99

/-! Inlined whole module: ExpandingCodes.Computation.NeighborWriter -/
section FlattenModule100



set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ExpandingCodes.Computation
open NKtLB
namespace NeighborWriter
open TapeProgram ParameterPrograms
variable {R B : ℕ}

def reverse (r : Fin 6 → Fin R) : Fin 6 → Fin R := fun j => r (Equiv.swap 0 1 j)
















/-- Mark the output counter as one if the two preserved inputs agree. A prior
one stays one. Every comparison is an actual unary source program. -/
def markEq (r : Fin 6 → Fin R) (out : Fin R) : TapeProgram R B 77 :=
  TapeProgram.seq (lessThan r)
    (branchZero (r 2)
      (TapeProgram.seq (lessThan (reverse r))
        (branchZero (r 2) (loadConstant out 1) skip)) skip)

def markStore (r : Fin 6 → Fin R) (out : Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := lessThanStore r d
  if c.reg (r 2) = 0 then
    let e := lessThanStore (reverse r) c
    if e.reg (r 2) = 0 then e.setReg out 1 else e
  else c





































































































/-- Emit and consume an already proved Boolean counter. Two charged source
instructions suffice; no arbitrary natural-to-Boolean operation is present. -/
def emitFlag (r : Fin R) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .dec r 1 2 else if j = 1 then .emit false 3
    else if j = 2 then .emit true 3 else .halt

def emitStore (r : Fin R) (d : TapeStore R B) : TapeStore R B :=
  {d with reg := Function.update d.reg r 0, output := d.output ++ [decide (d.reg r = 1)]}




















/-- Eight common registers and one statically allocated neighbor register per
layer. This allocation depends only on fixed k, never on runtime n. -/
structure Layout (R k : ℕ) where
  reg : Fin 8 ⊕ Fin k → Fin R
  injective : Function.Injective reg

namespace Layout
variable {k : ℕ}
abbrev n (l : Layout R k) := l.reg (.inl 0)
abbrev col (l : Layout R k) := l.reg (.inl 1)
abbrev out (l : Layout R k) := l.reg (.inl 2)
abbrev count (l : Layout R k) := l.reg (.inl 7)
abbrev neighbor (l : Layout R k) (i : Fin k) := l.reg (.inr i)

def comparisonIndex (i : Fin k) : Fin 6 → (Fin 8 ⊕ Fin k) :=
  ![.inl 1,.inr i,.inl 3,.inl 4,.inl 5,.inl 6]

def comparison (l : Layout R k) (i : Fin k) : Fin 6 → Fin R :=
  l.reg ∘ comparisonIndex i





























end Layout

def marksLabels : ℕ → ℕ
  | 0 => 1
  | n+1 => 77+marksLabels n

def marks {k : ℕ} (l : Layout R k) : (is : List (Fin k)) → TapeProgram R B (marksLabels is.length)
  | [] => skip
  | i::is => TapeProgram.seq (markEq (l.comparison i) l.out) (marks l is)

def marksStore {k : ℕ} (l : Layout R k) : List (Fin k) → TapeStore R B → TapeStore R B
  | [],d => d
  | i::is,d => marksStore l is (markStore (l.comparison i) l.out d)














































































def bodyLabels (k : ℕ) : ℕ := marksLabels (List.finRange k).length+4+2

/-- One actual column: scan the statically allocated neighbors, emit one bit,
consume its Boolean flag, then increment the preserved column counter. -/
def body {k : ℕ} (l : Layout R k) : TapeProgram R B (bodyLabels k) :=
  TapeProgram.seq (TapeProgram.seq (marks l (List.finRange k)) (emitFlag l.out))
    (TapeMacros.increment l.col)

def bodyStore {k : ℕ} (l : Layout R k) (d : TapeStore R B) : TapeStore R B :=
  let e := emitStore l.out (marksStore l (List.finRange k) d)
  e.setReg l.col (e.reg l.col+1)




































































def loopStore {k : ℕ} (l : Layout R k) : ℕ → TapeStore R B → TapeStore R B
  | 0,d => d
  | n+1,d => loopStore l n (bodyStore l (decStore l.count d))






















































































def prepare {k : ℕ} (l : Layout R k) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear l.col) (TapeMacros.clear l.out))
    (TapeMacros.copy l.n l.count (l.reg (.inl 6)))

def prepareStore {k : ℕ} (l : Layout R k) (d : TapeStore R B) : TapeStore R B :=
  ((((d.setReg l.col 0).setReg l.out 0).setReg l.count (d.reg l.n)).setReg (l.reg (.inl 6)) 0)































































def writeRow {k : ℕ} (l : Layout R k) : TapeProgram R B (15+(bodyLabels k+2)) :=
  TapeProgram.seq (prepare l) (countedLoop (body l) l.count)

def writeRowStore {k : ℕ} (l : Layout R k) (d : TapeStore R B) : TapeStore R B :=
  loopStore l (d.reg l.n) (prepareStore l d)

def writeRowBound (k M : ℕ) : ℕ :=
  16*(M+1)+1+M*(k*(160*(M+1)+1)+7)+1



































































































































































end NeighborWriter
end ExpandingCodes.Computation

end FlattenModule100

/-! Inlined whole module: ExpandingCodes.Computation.SamplerEnvelope -/
section FlattenModule101


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

def samplerBucketCount (k n : ℕ) : ℕ := 2^Nat.log 2 (n/k)









/-- One fixed polynomial envelope for actual sampler scalar values and table
heads. Every summand is a true size bound, not a machine instruction. -/
def samplerEnvelope (d k n : ℕ) : ℕ :=
  2 + ParameterPrograms.setupCounterBound d (n+1) + (2*k*d+d+k+1) +
    (fieldSize d n)^2 + (3*fieldExponent d n+1) + 2*fieldSize d n +
    (2*k*fieldSize d n*d*fieldSize d n+1) +
    (k*(fieldSize d n)^3*samplerBucketCount k n+1) + rowCount d n + n +
    rowCount d n*n + k*samplerBucketCount k n +
    SamplerTables.entropy d n k (Nat.log 2 (n/k))

structure SamplerEnvelopeCovers (d k n M : ℕ) : Prop where
  two : 2 ≤ M
  setup : ParameterPrograms.setupCounterBound d (n+1) ≤ M
  constants : 2*k*d+d+k+1 ≤ M
  square : (fieldSize d n)^2 ≤ M
  coefficients : 3*fieldExponent d n+1 ≤ M
  twiceField : 2*fieldSize d n ≤ M
  forms : 2*k*fieldSize d n*d*fieldSize d n+1 ≤ M
  hashes : k*(fieldSize d n)^3*samplerBucketCount k n+1 ≤ M
  rows : rowCount d n ≤ M
  input : n ≤ M
  output : rowCount d n*n ≤ M
  neighbors : k*samplerBucketCount k n ≤ M
  entropy : SamplerTables.entropy d n k (Nat.log 2 (n/k)) ≤ M























end ExpandingCodes.PolynomialStretch

end FlattenModule101

/-! Inlined whole module: ExpandingCodes.Computation.SamplerRows -/
section FlattenModule102



set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerRows
open ExpandingCodes.PolynomialStretch EncodedTester

variable {q d k b n : ℕ}

def row (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (z : Fin (q^d)) : List Bool :=
  List.ofFn fun j : Fin n => decide (∃ i : Fin k,
    j.val = i.val*b+(EncodedSampler.neighbor O s h i (digits q d z)).val)

def rowsBefore (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (r : ℕ) (hr : r ≤ q^d) : List Bool :=
  (List.ofFn fun i : Fin r => row (n := n) O s h ⟨i.val,lt_of_lt_of_le i.isLt hr⟩).flatten




























































end ExpandingCodes.Computation.SamplerRows

end FlattenModule102

/-! Inlined whole module: ExpandingCodes.Computation.SamplerAssembly -/
section FlattenModule103










set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
namespace ExpandingCodes.Computation.SamplerAssembly
open NKtLB UnaryArithmetic FieldPrograms ParameterPrograms SamplerEvaluation
open ExpandingCodes.PolynomialStretch
variable {R B : ℕ}

/-- The sampler prelude uses the agreed fixed low eighty registers. -/
def sizeLayout (r : Fin 80 → Fin R) (i : Fin 14) : Fin R := r ⟨32+i.val,by omega⟩
def randomRegisters (r : Fin 80 → Fin R) (i : Fin 6) : Fin R := r ⟨46+i.val,by omega⟩

def randomLayout (r : Fin 80 → Fin R) (hr : Function.Injective r) : RandomTables.Layout R where
  random.reg := ⟨randomRegisters r,by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val (hr h)
    simp only [randomRegisters,Fin.val_mk] at hh
    omega⟩
  count := r 52
  fresh j := by
    intro h
    have hh := congrArg Fin.val (hr h)
    have hj := j.isLt
    simp only [randomRegisters,Fin.val_mk] at hh
    omega









/-- Two real preserving copies install the random entry length and width. -/
def prepareRandom (r : Fin 80 → Fin R) (ell width : Fin 80) : TapeProgram R B 22 :=
  TapeProgram.seq (TapeMacros.copy (r ell) (r 46) (r 51))
    (TapeMacros.copy (r width) (r 47) (r 51))

def prepareRandomStore (r : Fin 80 → Fin R) (ell width : Fin 80)
    (s : TapeStore R B) : TapeStore R B :=
  let c := (s.setReg (r 46) (s.reg (r ell))).setReg (r 51) 0
  (c.setReg (r 47) (c.reg (r width))).setReg (r 51) 0






























/-- The bottom marker is written by an actual one-cell source instruction. -/
def initializeStore (s : TapeStore R B) (b : Fin B) : TapeStore R B := TapeArrays.painted s b .bot

def markedFill (l : RandomTables.Layout R) (b : Fin B) : TapeProgram R B 57 :=
  TapeProgram.seq (TapeArrays.initializeBuffer b) (RandomTables.fill l b)

def markedFillStore (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) : TapeStore R B :=
  RandomTables.fillStore l b inp K (initializeStore s b)
















































































/-- Multiplication by a compile-time constant, implemented by a real constant
loader followed by the uniform unary multiplication program. -/
def staticScale (r : Fin 5 → Fin R) (c : ℕ) :
    TapeProgram R B ((2+raiseLabels c)+24) :=
  TapeProgram.seq (loadConstant (r 1) c) (multiply (r 0) (r 1) (r 2) (r 3) (r 4))

def staticScaleStore (r : Fin 5 → Fin R) (c : ℕ) (s : TapeStore R B) : TapeStore R B :=
  multiplyStore (s.setReg (r 1) c) (r 0) (r 1) (r 2) (r 3) (r 4)







































/-- Runtime q cubed, using two actual unary multiplications. No q-dependent
unrolling or field-arithmetic primitive occurs in this finite program. -/
def cube (r : Fin 80 → Fin R) : TapeProgram R B 48 :=
  TapeProgram.seq (multiply (r 35) (r 35) (r 53) (r 54) (r 55))
    (multiply (r 35) (r 53) (r 56) (r 54) (r 55))

def cubeSquare (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  multiplyStore s (r 35) (r 35) (r 53) (r 54) (r 55)
def cubeStore (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  multiplyStore (cubeSquare r s) (r 35) (r 53) (r 56) (r 54) (r 55)



































































































/-- Actual code computing the number 2*k*q*d of random form coefficients. -/
def formCountLayout (r : Fin 80 → Fin R) : Fin 5 → Fin R := r ∘ ![35,53,52,54,55]
def formCountLabels (d k : ℕ) : ℕ := (2+raiseLabels (2*k*d))+24
def formCount (r : Fin 80 → Fin R) (d k : ℕ) : TapeProgram R B (formCountLabels d k) :=
  staticScale (formCountLayout r) (2*k*d)
def formCountStore (r : Fin 80 → Fin R) (d k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  staticScaleStore (formCountLayout r) (2*k*d) s






















/-- Actual code computing k*q^3, with q a runtime unary counter. -/
def hashScaleLayout (r : Fin 80 → Fin R) : Fin 5 → Fin R := r ∘ ![56,57,52,54,55]
def hashCountLabels (k : ℕ) : ℕ := 48+((2+raiseLabels k)+24)
def hashCount (r : Fin 80 → Fin R) (k : ℕ) : TapeProgram R B (hashCountLabels k) :=
  TapeProgram.seq (cube r) (staticScale (hashScaleLayout r) k)
def hashCountStore (r : Fin 80 → Fin R) (k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  staticScaleStore (hashScaleLayout r) k (cubeStore r s)







































































/-- Source code for the entire forms-table stage. -/
def formFillLabels (d k : ℕ) : ℕ := (formCountLabels d k+22)+57
def formFill (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ) (b : Fin B) :
    TapeProgram R B (formFillLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (formCount r d k) (prepareRandom r 34 35))
    (markedFill (randomLayout r hr) b)

def formPrepareStore (r : Fin 80 → Fin R) (d k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  prepareRandomStore r 34 35 (formCountStore r d k s)
def formFillStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  markedFillStore (randomLayout r hr) b inp (2*k*s.reg (r 35)*d) (formPrepareStore r d k s)
































































/-- Source code for the hash-table stage, whose q-cubed entry count is runtime data. -/
def hashFillLabels (k : ℕ) : ℕ := (hashCountLabels k+22)+57
def hashFill (r : Fin 80 → Fin R) (hr : Function.Injective r) (k : ℕ) (b : Fin B) :
    TapeProgram R B (hashFillLabels k) :=
  TapeProgram.seq (TapeProgram.seq (hashCount r k) (prepareRandom r 38 39))
    (markedFill (randomLayout r hr) b)

def hashPrepareStore (r : Fin 80 → Fin R) (k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  prepareRandomStore r 38 39 (hashCountStore r k s)
def hashFillStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (k : ℕ)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  markedFillStore (randomLayout r hr) b inp (k*(s.reg (r 35))^3) (hashPrepareStore r k s)




























































































































































































def tablesLabels (d k : ℕ) : ℕ := formFillLabels d k+hashFillLabels k
/-- Both physical tables use one continuously advanced RO randomness head. -/
def tables (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ) (bf bh : Fin B) :
    TapeProgram R B (tablesLabels d k) :=
  TapeProgram.seq (formFill r hr d k bf) (hashFill r hr k bh)
def tablesStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ)
    (bf bh : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  hashFillStore r hr k bh inp (formFillStore r hr d k bf inp s)






























/-- The actual field setup is embedded in the low32 registers. -/
def fieldLayout (r : Fin 80 → Fin R) (i : Fin 32) : Fin R := r ⟨i.val,by omega⟩
def scalarLayout (r : Fin 80 → Fin R) (i : Fin 31) : Fin R := r ⟨i.val,by omega⟩








def prepareField (r : Fin 80 → Fin R) : TapeProgram R B 22 :=
  TapeProgram.seq (TapeMacros.copy (r 34) (r 20) (r 31))
    (TapeMacros.copy (r 35) (r 23) (r 31))
def prepareFieldStore (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  let c := (s.setReg (r 20) (s.reg (r 34))).setReg (r 31) 0
  (c.setReg (r 23) (c.reg (r 35))).setReg (r 31) 0















def fieldSetup (r : Fin 80 → Fin R) : TapeProgram R B 538 :=
  TapeProgram.seq (prepareField r) (SourceFieldSetup.setup (fieldLayout r))
def fieldSetupStore (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  SourceFieldSetup.setupStore (fieldLayout r) (prepareFieldStore r s)































































/-- The initial source storage is independent of the number of finite labels. -/
def initialStore (R B : ℕ) : TapeStore R B := ⟨fun _ => 0,fun _ => 0,[],fun _ => [],fun _ => 0⟩

def sizeStageStore (r : Fin 80 → Fin R) (d n k : ℕ) : TapeStore R B :=
  setupStore (sizeLayout r) d k (SizeReader.sizeStore (r 32) n (initialStore R B))
def sizeStageTime (d n : ℕ) : ℕ := 2*n+4+setupTimeBound d (n+1)

structure Sizes (r : Fin 80 → Fin R) (d n k : ℕ) (s : TapeStore R B) : Prop where
  input : s.reg (r 32)=n
  power : s.reg (r 33)=n^(2*d)
  ell : s.reg (r 34)=ExpandingCodes.PolynomialStretch.fieldExponent d n
  field : s.reg (r 35)=ExpandingCodes.PolynomialStretch.fieldSize d n
  rows : s.reg (r 36)=ExpandingCodes.PolynomialStretch.rowCount d n
  quotient : s.reg (r 37)=n/k
  beta : s.reg (r 38)=Nat.log 2 (n/k)
  buckets : s.reg (r 39)=2^Nat.log 2 (n/k)








 































































































































































/-- Numeric table readiness used by the actual layer program. These are explicit
physical cell predicates for the exact blocks read from the finite random tape. -/
structure TablesReady (d n k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R 2) : Prop where
  forms : TapeArrays.ThermometerTable s 0 (ExpandingCodes.PolynomialStretch.fieldSize d n)
    (fun i => (RandomTables.sampledValues inp
      (2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)
      (ExpandingCodes.PolynomialStretch.fieldExponent d n) 0 i).val)
  hashes : TapeArrays.ThermometerTable s 1 (2^Nat.log 2 (n/k))
    (fun i => (RandomTables.sampledValues inp
      (k*ExpandingCodes.PolynomialStretch.fieldSize d n*ExpandingCodes.PolynomialStretch.fieldSize d n*
        ExpandingCodes.PolynomialStretch.fieldSize d n) (Nat.log 2 (n/k))
      ((2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)*
        ExpandingCodes.PolynomialStretch.fieldExponent d n) i).val)
  marked : ∀ b,TapeArrays.BottomMarked s b
  heads : ∀ b,s.bufferHead b ≤ M



























































































open ExpandingCodes.PolynomialStretch

structure RuntimeReady (r : Fin 80 → Fin R) (d n k : ℕ) (inp : Inputs) (M : ℕ)
    (s : TapeStore R 2) : Prop where
  sizes : Sizes r d n k s
  environment : SamplerProgram.Environment (scalarLayout r) (fieldExponent d n)
    (BinaryPolynomial.selectedIndex (fieldExponent d n) (fieldExponent_pos d n)) s
  tables : TablesReady d n k inp M s
  counters : ∀ j,s.reg j ≤ M

def preludeLabels (d k : ℕ) : ℕ := ((5+setupLabels d k)+tablesLabels d k)+538
/-- The complete actual frontend, fixed before any runtime size is read. -/
def samplerFrontendProgram (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ) :
    TapeProgram R 2 (preludeLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (setupInput (sizeLayout r) d k) (tables r hr d k 0 1)) (fieldSetup r)
def preludeStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (d n k : ℕ) (inp : Inputs) : TapeStore R 2 :=
  fieldSetupStore r (tablesStore r hr d k 0 1 inp (sizeStageStore r d n k))
def preludeTime (d n M : ℕ) : ℕ := sizeStageTime d n+391*(M+1)^3+40020*(M+1)^7+2













































































































/-- Stable scalar values needed by every row computation. -/
def Protected (j : Fin 80) : Prop :=
  j=3 ∨ j=19 ∨ j=23 ∨ j=24 ∨ (32 ≤ j.val ∧ j.val<40)





























namespace Concrete
open SamplerProgram

def writerIndex : Fin 8 → Fin 80 := ![32,62,63,64,65,66,67,68]

def writerRegisters (d k : ℕ) : Fin 8 ⊕ Fin k → Fin (Storage.registers d k)
  | .inl i => Storage.low d k (writerIndex i)
  | .inr i => Storage.neighbor d k i

theorem writerRegisters_injective (d k : ℕ) : Function.Injective (writerRegisters d k) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      apply congrArg Sum.inl
      apply (show Function.Injective writerIndex by decide)
      exact Storage.low_injective d k hab
    | inr j =>
      have h := congrArg Fin.val hab
      have hj := j.isLt
      fin_cases i <;> simp [writerRegisters,writerIndex,Storage.low_val,Storage.neighbor_val] at h <;> omega
  | inr i =>
    cases b with
    | inl j =>
      have h := congrArg Fin.val hab
      have hi := i.isLt
      fin_cases j <;> simp [writerRegisters,writerIndex,Storage.low_val,Storage.neighbor_val] at h <;> omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      have h := congrArg Fin.val hab
      simp only [writerRegisters,Storage.neighbor_val] at h
      omega

def writerLayout (d k : ℕ) : NeighborWriter.Layout (Storage.registers d k) k :=
  ⟨writerRegisters d k,writerRegisters_injective d k⟩

def layersLabels (d k : ℕ) : List (Fin k) → ℕ
  | [] => 1
  | i::is => layerLabels d k i+layersLabels d k is

def layers (d k : ℕ) : (is : List (Fin k)) → TapeProgram (Storage.registers d k) 2 (layersLabels d k is)
  | [] => TapeProgram.skip
  | i::is => TapeProgram.seq (layer d k i) (layers d k is)

def rowBodyLabels (d k : ℕ) : ℕ :=
  (layersLabels d k (List.finRange k)+(15+(NeighborWriter.bodyLabels k+2)))+
    SamplerOdometer.labels (Storage.pointPairs d k)

/-- One complete actual row: all k layer evaluations, physical n-bit row writer,
and physical little-endian carry. None of n,q,ell,m,b enters this code table. -/
def rowBody (d k : ℕ) : TapeProgram (Storage.registers d k) 2 (rowBodyLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (layers d k (List.finRange k)) (NeighborWriter.writeRow (writerLayout d k)))
    (SamplerOdometer.program (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k))

def finishLabels (d k : ℕ) : ℕ :=
  (SamplerOdometer.initializeLabels (Storage.pointPairs d k)+11)+(rowBodyLabels d k+2)

def finish (d k : ℕ) : TapeProgram (Storage.registers d k) 2 (finishLabels d k) :=
  TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k))
    (TapeMacros.copy (Storage.low d k 36) (Storage.low d k 60) (Storage.low d k 61)))
    (TapeProgram.countedLoop (rowBody d k) (Storage.low d k 60))

def samplerLabels (d k : ℕ) : ℕ := preludeLabels d k+finishLabels d k

/-- Fully concrete finite sampler source, including its unary frontend, physical
random tables, field construction, runtime row loop, and physical output writes. -/
def sampler (d k : ℕ) : TapeProgram (Storage.registers d k) 2 (samplerLabels d k) :=
  TapeProgram.seq (samplerFrontendProgram (Storage.low d k) (Storage.low_injective d k) d k) (finish d k)





































































































































































































































def operations (d n : ℕ) : EncodedGaussian.Operations (Fin (fieldSize d n)) := BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n)
def formValues (d n k : ℕ) (inp : Inputs) : Fin (2*k*fieldSize d n*d) → Fin (fieldSize d n) :=
  RandomTables.sampledValues inp (2*k*fieldSize d n*d) (fieldExponent d n) 0
def hashValues (d n k : ℕ) (inp : Inputs) :
    Fin (k*fieldSize d n*fieldSize d n*fieldSize d n) → Fin (2^Nat.log 2 (n/k)) :=
  RandomTables.sampledValues inp (k*fieldSize d n*fieldSize d n*fieldSize d n) (Nat.log 2 (n/k))
    ((2*k*fieldSize d n*d)*fieldExponent d n)

structure RowState (d n k M : ℕ) (inp : Inputs) (r : ℕ) (hr : r ≤ rowCount d n)
    (s : TapeStore (Storage.registers d k) 2) : Prop where
  ready : RuntimeReady (Storage.low d k) d n k inp M s
  valid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s
  number : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) s)=r%rowCount d n
  output : s.output=SamplerRows.rowsBefore (n:=n) (operations d n) (formValues d n k inp)
    (hashValues d n k inp) r hr












/-- The operational contract for the k actual layer fragments within one row.
All fields are postconditions over actual source configurations and table cells. -/
structure LayerBlockPost (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d))
    (e : TapeStore (Storage.registers d k) 2) : Prop where
  ready : RuntimeReady (Storage.low d k) d n k inp M e
  valid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) e
  readings : SamplerOdometer.readings (Storage.pointPairs d k) e=SamplerOdometer.readings (Storage.pointPairs d k) s
  remaining : e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60)
  output : e.output=s.output
  neighbors : ∀ i,e.reg (Storage.neighbor d k i)=i.val*(2^Nat.log 2 (n/k))+
    (EncodedSampler.neighbor (operations d n) (formValues d n k inp) (hashValues d n k inp) i
      (EncodedTester.digits (fieldSize d n) d z)).val

def rowBodyTime (d k C M : ℕ) : ℕ := C+NeighborWriter.writeRowBound k M+d*(8*M+20)+2




































































































def LayerBlockContract (d n k M : ℕ) (inp : Inputs) (C : ℕ) : Prop :=
  ∀ (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d)),
    RuntimeReady (Storage.low d k) d n k inp M s →
    SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s →
    (∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) →
    ∃ t e,t ≤ C ∧ (layers d k (List.finRange k)).Stops inp
      (s.toCfg (layers d k (List.finRange k)).entry) t e ∧ LayerBlockPost d n k M inp s z e.store

def finishTime (d n k C M : ℕ) : ℕ :=
  d*(8*M+20)+(7*M+7)+2+rowCount d n*(rowBodyTime d k C M+2)+1



































































































































structure StablePost (d n k M : ℕ) (inp : Inputs)
    (s e : TapeStore (Storage.registers d k) 2) : Prop where
  ready : RuntimeReady (Storage.low d k) d n k inp M e
  points : ∀ j,e.reg (Storage.point d k j)=s.reg (Storage.point d k j)
  countdowns : ∀ j,e.reg (Storage.countdown d k j)=s.reg (Storage.countdown d k j)
  remaining : e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60)
  output : e.output=s.output











structure StepPost (d n k M : ℕ) (inp : Inputs) (i : Fin k)
    (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d))
    (e : TapeStore (Storage.registers d k) 2) : Prop where
  stable : StablePost d n k M inp s e
  neighbor : e.reg (Storage.neighbor d k i)=i.val*(2^Nat.log 2 (n/k))+
    (EncodedSampler.neighbor (operations d n) (formValues d n k inp) (hashValues d n k inp) i
      (EncodedTester.digits (fieldSize d n) d z)).val
  other : ∀ j,j≠i → e.reg (Storage.neighbor d k j)=s.reg (Storage.neighbor d k j)

def StepContract (d n k M : ℕ) (inp : Inputs) (C : ℕ) : Prop :=
  ∀ (i : Fin k) (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d)),
    RuntimeReady (Storage.low d k) d n k inp M s →
    (∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) →
    ∃ t e,t ≤ C ∧ (layer d k i).Stops inp (s.toCfg (layer d k i).entry) t e ∧
      StepPost d n k M inp i s z e.store


































def blockTime (d k M : ℕ) : ℕ := k*(layerTimeUniform d k M+1)
def sourceTime (d n k : ℕ) : ℕ :=
  preludeTime d n (samplerEnvelope d k n)+1+
    finishTime d n k (blockTime d k (samplerEnvelope d k n)) (samplerEnvelope d k n)





























































































end Concrete
end ExpandingCodes.Computation.SamplerAssembly

end FlattenModule103


section FlattenModule104




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation








































end ExpandingCodes.PolynomialStretch

end FlattenModule104


section FlattenModule105




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
open SamplerAssembly.Concrete







































end ExpandingCodes.PolynomialStretch

end FlattenModule105


section FlattenModule106





set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch















end ExpandingCodes.PolynomialStretch

end FlattenModule106


section FlattenModule107


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch







end ExpandingCodes.PolynomialStretch

end FlattenModule107


section FlattenModule108


set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch
























































end ExpandingCodes.PolynomialStretch

end FlattenModule108


section FlattenModule109










set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] [DecidableEq σ]

































































end ExpandingCodes

end FlattenModule109


section FlattenModule110









set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ ι : Type*} [Field K]






















variable [Fintype K]










































































end ExpandingCodes

end FlattenModule110


section FlattenModule111








set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch























































































end ExpandingCodes.PolynomialStretch

end FlattenModule111


section FlattenModule112


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch























end ExpandingCodes.PolynomialStretch

end FlattenModule112


section FlattenModule113



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch








































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule113


section FlattenModule114















set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module




























































































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule114


section FlattenModule115



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module











































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule115


section FlattenModule116



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





























































































































end ExpandingCodes.PolynomialStretch

end FlattenModule116


section FlattenModule117



set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch





















































end ExpandingCodes.PolynomialStretch

end FlattenModule117


section FlattenModule118


set_option autoImplicit false
open scoped Classical BigOperators Topology
open Set MeasureTheory

namespace ExpandingCodes.PolynomialStretch
















































































































end ExpandingCodes.PolynomialStretch

end FlattenModule118


section FlattenModule119


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

































































































end ExpandingCodes.PolynomialStretch

end FlattenModule119


section FlattenModule120




set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch




















































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule120


section FlattenModule121



















set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.Erasure

open Module Filter Finset

variable {K I : Type*} [Field K]































































































































variable [Fintype I]





























































































































































































































































































































































































































































































































end ExpandingCodes.Erasure

end FlattenModule121


section FlattenModule122

















set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]












































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule122


section FlattenModule123









set_option autoImplicit false
namespace ExpandingCodes.SharpThreshold

















































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule123


section FlattenModule124



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]






































































































































































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule124


section FlattenModule125


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]










end ExpandingCodes.SharpThreshold

end FlattenModule125


section FlattenModule126






set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]
































































































































end ExpandingCodes.SharpThreshold

end FlattenModule126


section FlattenModule127


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

























end ExpandingCodes.SharpThreshold

end FlattenModule127


section FlattenModule128




set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule128


section FlattenModule129


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]













end ExpandingCodes.SharpThreshold

end FlattenModule129


section FlattenModule130


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]


















end ExpandingCodes.SharpThreshold

end FlattenModule130


section FlattenModule131


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure
open scoped Classical

variable {I : Type*} [Fintype I]







































































end ExpandingCodes.SharpThreshold

end FlattenModule131


section FlattenModule132
















set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]





















































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule132


section FlattenModule133













set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter


























































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule133


section FlattenModule134





set_option autoImplicit false
open scoped Classical Topology
open Filter

namespace ExpandingCodes.PolynomialStretch































end ExpandingCodes.PolynomialStretch

end FlattenModule134


section FlattenModule135




set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch



















end ExpandingCodes.PolynomialStretch

end FlattenModule135


section FlattenModule136


end FlattenModule136


section FlattenModule137

















set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Filter Module



















































































































open MeasureTheory
























































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule137


section FlattenModule138


set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch


















end ExpandingCodes.PolynomialStretch

end FlattenModule138


section FlattenModule139





end FlattenModule139


section FlattenModule140



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter

















end ExpandingCodes.PolynomialStretch

end FlattenModule140


section FlattenModule141



set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch




















end ExpandingCodes.PolynomialStretch

end FlattenModule141


section FlattenModule142


set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch




































end ExpandingCodes.PolynomialStretch

end FlattenModule142


section FlattenModule143




set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch


























































end ExpandingCodes.PolynomialStretch

end FlattenModule143


section FlattenModule144


end FlattenModule144


section FlattenModule145



set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch



















end FlattenModule145
