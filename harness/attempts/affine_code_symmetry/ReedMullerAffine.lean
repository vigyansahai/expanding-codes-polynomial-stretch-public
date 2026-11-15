import ExpandingCodes.Algebra.ReedMullerDimension
import ExpandingCodes.Algebra.FlatIndicator
import ExpandingCodes.Algebra.CodeReindex

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Degree of the unique reduced positive power, with zero preserved. -/
def reducedPower (q n : ℕ) : ℕ := if n = 0 then 0 else 1 + (n - 1) % (q - 1)

theorem reducedPower_lt {q : ℕ} (hq : 1 < q) (n : ℕ) : reducedPower q n < q := by
  unfold reducedPower
  split_ifs with hn
  · omega
  · have := Nat.mod_lt (n - 1) (by omega : 0 < q - 1)
    omega

theorem reducedPower_le (q n : ℕ) : reducedPower q n ≤ n := by
  unfold reducedPower
  split_ifs with hn
  · omega
  · have := Nat.mod_le (n - 1) (q - 1)
    omega

theorem pow_reducedPower {F : Type*} [Field F] [Fintype F] (x : F) (n : ℕ) :
    x ^ reducedPower (Fintype.card F) n = x ^ n := by
  by_cases hn : n = 0
  · simp [reducedPower, hn]
  by_cases hx : x = 0
  · simp [hx, reducedPower, hn]
  have hp := FiniteField.pow_card_sub_one_eq_one x hx
  have he : x ^ ((n - 1) % (Fintype.card F - 1)) = x ^ (n - 1) := by
    conv_rhs => rw [← Nat.mod_add_div (n - 1) (Fintype.card F - 1)]
    rw [pow_add, pow_mul, hp, one_pow, mul_one]
  rw [reducedPower, if_neg hn, pow_add, he, pow_one, ← pow_succ']
  congr 1
  omega

/-- Reduction of a support exponent never raises its total degree. -/
noncomputable def reducedExponentMonomial {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (e : Fin d →₀ ℕ) (he : e.sum (fun _ n => n) ≤ R) : Monomials F d R :=
  ⟨fun i => ⟨reducedPower (Fintype.card F) (e i),
    reducedPower_lt (Fintype.one_lt_card (α := F)) (e i)⟩, by
    calc
      (∑ i, reducedPower (Fintype.card F) (e i)) ≤ ∑ i, e i :=
        Finset.sum_le_sum (fun i _ => reducedPower_le _ _)
      _ = e.sum (fun _ n => n) := (Finsupp.sum_fintype e (fun _ n => n) (fun _ => rfl)).symm
      _ ≤ R := he⟩

theorem monomial_eval_mem_reedMuller {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (e : Fin d →₀ ℕ) (c : F) (he : e.sum (fun _ n => n) ≤ R) :
    (fun z => MvPolynomial.eval z (MvPolynomial.monomial e c)) ∈ reedMuller F d R := by
  let a := reducedExponentMonomial (F := F) e he
  have ha : monomialEval a ∈ reedMuller F d R := Submodule.subset_span ⟨a, rfl⟩
  have hfun : (fun z => MvPolynomial.eval z (MvPolynomial.monomial e c)) =
      c • monomialEval a := by
    funext z
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Pi.smul_apply, smul_eq_mul, monomialEval, a, reducedExponentMonomial]
    simp_rw [pow_reducedPower]
  rw [hfun]
  exact Submodule.smul_mem _ c ha

/-- Evaluation of every polynomial of bounded total degree lies in the canonical span.
Its unreduced individual degrees may exceed the field cardinality. -/
theorem eval_mem_reedMuller {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (p : MvPolynomial (Fin d) F) (hp : p.totalDegree ≤ R) :
    (fun z => MvPolynomial.eval z p) ∈ reedMuller F d R := by
  have heq : (fun z => MvPolynomial.eval z p) =
      ∑ e ∈ p.support, (fun z => MvPolynomial.eval z (MvPolynomial.monomial e (p.coeff e))) := by
    funext z
    simpa only [map_sum, Finset.sum_apply] using congrArg (MvPolynomial.eval z) p.as_sum
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  exact monomial_eval_mem_reedMuller e _ ((MvPolynomial.le_totalDegree he).trans hp)

/-- Every coordinatewise affine substitution preserves the Reed--Muller space;
invertibility is only needed later for the permutation group. -/
theorem reedMuller_comp_affine_mem {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (A : Fin d → Fin d → F) (b : Fin d → F) (c : (Fin d → F) → F)
    (hc : c ∈ reedMuller F d R) :
    (fun z => c (fun i => b i + ∑ j, A i j * z j)) ∈ reedMuller F d R := by
  induction hc using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    let p : MvPolynomial (Fin d) F :=
      ∏ i, ExpandingCodes.affinePolynomial (A i) (b i) ^ (a.val i).val
    have hp : p.totalDegree ≤ R := by
      calc
        p.totalDegree ≤ ∑ i, (ExpandingCodes.affinePolynomial (A i) (b i) ^ (a.val i).val).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ i, (a.val i).val := by
          apply Finset.sum_le_sum
          intro i _
          exact (MvPolynomial.totalDegree_pow _ _).trans
            (by simpa using (Nat.mul_le_mul_left ((a.val i).val)
              (ExpandingCodes.totalDegree_affinePolynomial_le (A i) (b i))))
        _ ≤ R := a.property
    have he : (fun z => monomialEval a (fun i => b i + ∑ j, A i j * z j)) =
        (fun z => MvPolynomial.eval z p) := by
      funext z
      simp [p, monomialEval, ExpandingCodes.eval_affinePolynomial]
    rw [he]
    exact eval_mem_reedMuller p hp
  | zero => exact (reedMuller F d R).zero_mem
  | add x y hx hy ihx ihy => exact (reedMuller F d R).add_mem ihx ihy
  | smul r x hx ih => exact (reedMuller F d R).smul_mem r ih

/-- A linear automorphism takes any nonzero vector to any other. -/
theorem exists_linearEquiv_apply_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ T : V ≃ₗ[F] V, T u = v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton F V u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton F V v hv
  let f := eu.symm.trans ev
  obtain ⟨T, hT⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨T, ?_⟩
  have h := hT (eu 1)
  have he : (f (eu 1) : V) = v := by simp [f, ev]
  have hu' : (eu 1 : V) = u := by simp [eu]
  rw [he, hu'] at h
  exact h.symm

/-- Every linear map on the coordinate space has a degree-one polynomial representation. -/
theorem reedMuller_comp_linear_add_mem {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (T : (Fin d → F) →ₗ[F] (Fin d → F)) (b : Fin d → F)
    (c : (Fin d → F) → F) (hc : c ∈ reedMuller F d R) :
    (fun z => c (T z + b)) ∈ reedMuller F d R := by
  let A : Fin d → Fin d → F := fun i j => T (fun k => if j = k then 1 else 0) i
  have hT : ∀ z, T z + b = (fun i => b i + ∑ j, A i j * z j) := by
    intro z
    funext i
    rw [LinearMap.pi_apply_eq_sum_univ T z]
    simp [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm, add_comm]
  simpa only [← hT] using reedMuller_comp_affine_mem A b c hc

/-- An affine permutation with prescribed linear and translation parts. -/
noncomputable def affineCoordinatePerm {F : Type*} [Field F] {d : ℕ}
    (T : (Fin d → F) ≃ₗ[F] (Fin d → F)) (a b : Fin d → F) :
    Equiv.Perm (Fin d → F) where
  toFun z := T (z - a) + b
  invFun z := T.symm (z - b) + a
  left_inv z := by simp
  right_inv z := by simp

theorem affineCoordinatePerm_mem_codePreservingSubgroup {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (T : (Fin d → F) ≃ₗ[F] (Fin d → F)) (a b : Fin d → F) :
    affineCoordinatePerm T a b ∈ codePreservingSubgroup (reedMuller F d R) := by
  intro c
  constructor
  · intro hc
    have h := reedMuller_comp_linear_add_mem T.toLinearMap (b - T a) c hc
    change (fun z => c (T z + (b - T a))) ∈ reedMuller F d R at h
    have he : (fun z => c (T z + (b - T a))) =
        (fun z => c (affineCoordinatePerm T a b z)) := by
      funext z
      congr 1
      change T z + (b - T a) = T (z - a) + b
      rw [map_sub]
      abel
    rwa [he] at h
  · intro hc
    have h := reedMuller_comp_linear_add_mem T.symm.toLinearMap (a - T.symm b)
      (fun z => c (affineCoordinatePerm T a b z)) hc
    have he : (fun z => c (affineCoordinatePerm T a b (T.symm z + (a - T.symm b)))) = c := by
      funext z
      congr 1
      simp [affineCoordinatePerm, map_add, map_sub]
      abel
    change (fun z => c (affineCoordinatePerm T a b (T.symm z + (a - T.symm b)))) ∈
      reedMuller F d R at h
    rwa [he] at h

/-- The code-preserving affine permutations act doubly transitively on points. -/
theorem reedMuller_pair_transitive {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a b a' b' : Fin d → F) (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ ∈ codePreservingSubgroup (reedMuller F d R), σ a = a' ∧ σ b = b' := by
  obtain ⟨T, hT⟩ := exists_linearEquiv_apply_eq (F := F) (b - a) (b' - a')
    (sub_ne_zero.mpr (Ne.symm hab)) (sub_ne_zero.mpr (Ne.symm hab'))
  refine ⟨affineCoordinatePerm T a a', affineCoordinatePerm_mem_codePreservingSubgroup T a a', ?_, ?_⟩
  · simp [affineCoordinatePerm]
  · change T (b - a) + a' = b'
    rw [hT]
    exact sub_add_cancel _ _

end ExpandingCodes.PolynomialStretch
