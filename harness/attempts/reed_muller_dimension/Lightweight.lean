import Mathlib.FieldTheory.Finite.Polynomial

set_option autoImplicit false
open scoped Classical BigOperators

namespace ReedMullerDimensionAttempt

-- Exact text of the three canonical definitions for lightweight elaboration only.
-- This attempt namespace is provisional and does not replace the platform definitions.
abbrev Monomials (F : Type*) [Fintype F] (d R : ℕ) :=
  {a : Fin d → Fin (Fintype.card F) // ∑ i, (a i).val ≤ R}
noncomputable def monomialEval {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (z : Fin d → F) : F := ∏ i, z i ^ (a.val i).val
noncomputable def reedMuller (F : Type*) [Field F] [Fintype F] (d R : ℕ) :
    Submodule F ((Fin d → F) → F) :=
  Submodule.span F (Set.range (monomialEval (F := F) (d := d) (R := R)))

universe u

/-- Finite-variable evaluation injectivity, including fields in arbitrary universes.
The lift only aligns the two universe parameters of Mathlib's finite-field theorem. -/
theorem eq_zero_of_eval_eq_zero_fin {F : Type u} [Field F] [Fintype F] {d : ℕ}
    (p : MvPolynomial (Fin d) F)
    (h : ∀ z : Fin d → F, MvPolynomial.eval z p = 0)
    (hp : p ∈ MvPolynomial.restrictDegree (Fin d) F (Fintype.card F - 1)) : p = 0 := by
  classical
  have hrename : MvPolynomial.rename (ULift.up : Fin d → ULift.{u} (Fin d)) p = 0 := by
    apply MvPolynomial.eq_zero_of_eval_eq_zero (ULift.{u} (Fin d)) F
    · intro z
      rw [MvPolynomial.eval_rename]
      exact h _
    · rw [MvPolynomial.mem_restrictDegree_iff_sup]
      intro i
      obtain ⟨i⟩ := i
      rw [← MvPolynomial.degreeOf_def,
        MvPolynomial.degreeOf_rename_of_injective ULift.up_injective]
      simpa only [MvPolynomial.degreeOf_def] using
        (MvPolynomial.mem_restrictDegree_iff_sup _ _ _).mp hp i
  apply MvPolynomial.rename_injective (ULift.up : Fin d → ULift.{u} (Fin d))
    ULift.up_injective
  simpa only [map_zero] using hrename

/-- The exponent vector of an exact canonical monomial, as a finitely supported function. -/
noncomputable def reducedMonomialExponent {F : Type*} [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a.val i).val)

@[simp] theorem reducedMonomialExponent_apply {F : Type*} [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (i : Fin d) :
    reducedMonomialExponent a i = (a.val i).val := rfl

theorem reducedMonomialExponent_injective {F : Type*} [Fintype F] {d R : ℕ} :
    Function.Injective (reducedMonomialExponent (F := F) (d := d) (R := R)) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun e : Fin d →₀ ℕ => e i) h

/-- A polynomial representative of each exact canonical monomial row. -/
noncomputable def reducedMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : MvPolynomial (Fin d) F :=
  MvPolynomial.monomial (reducedMonomialExponent a) 1

theorem eval_reducedMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (z : Fin d → F) :
    MvPolynomial.eval z (reducedMonomialPolynomial a) = monomialEval a z := by
  rw [reducedMonomialPolynomial, MvPolynomial.eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem reducedMonomialPolynomial_mem_restrictDegree {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (a : Monomials F d R) :
    reducedMonomialPolynomial a ∈
      MvPolynomial.restrictDegree (Fin d) F (Fintype.card F - 1) := by
  rw [MvPolynomial.mem_restrictDegree]
  intro b hb i
  have hba : b = reducedMonomialExponent a := by
    simpa [reducedMonomialPolynomial, MvPolynomial.support_monomial] using hb
  subst b
  exact Nat.le_sub_one_of_lt (a.val i).isLt

theorem linearIndependent_reducedMonomialPolynomial {F : Type*} [Field F] [Fintype F]
    (d R : ℕ) :
    LinearIndependent F (reducedMonomialPolynomial (F := F) (d := d) (R := R)) := by
  exact (MvPolynomial.basisMonomials (Fin d) F).linearIndependent.comp
    (reducedMonomialExponent (F := F) (d := d) (R := R))
    reducedMonomialExponent_injective

/-- Reduced monomials remain independent after evaluation on every point of the finite field. -/
theorem linearIndependent_monomialEval {F : Type*} [Field F] [Fintype F] (d R : ℕ) :
    LinearIndependent F (monomialEval (F := F) (d := d) (R := R)) := by
  have hspan : Submodule.span F
      (Set.range (reducedMonomialPolynomial (F := F) (d := d) (R := R))) ≤
      MvPolynomial.restrictDegree (Fin d) F (Fintype.card F - 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact reducedMonomialPolynomial_mem_restrictDegree a
  have hinj : Set.InjOn (MvPolynomial.evalₗ F (Fin d))
      (Submodule.span F
        (Set.range (reducedMonomialPolynomial (F := F) (d := d) (R := R)))) := by
    intro p hp q hq hpq
    apply sub_eq_zero.mp
    apply eq_zero_of_eval_eq_zero_fin (p - q)
    · intro z
      simpa only [map_sub, sub_eq_zero, MvPolynomial.evalₗ_apply] using congrFun hpq z
    · exact Submodule.sub_mem _ (hspan hp) (hspan hq)
  have h := (linearIndependent_reducedMonomialPolynomial (F := F) d R).map_injOn
    (MvPolynomial.evalₗ F (Fin d)) hinj
  have heval : (MvPolynomial.evalₗ F (Fin d)) ∘
      (reducedMonomialPolynomial (F := F) (d := d) (R := R)) =
      monomialEval (F := F) (d := d) (R := R) := by
    funext a z
    exact eval_reducedMonomialPolynomial a z
  rwa [heval] at h

/-- The exact Reed--Muller code dimension is the number of canonical reduced monomials. -/
theorem finrank_reedMuller {F : Type*} [Field F] [Fintype F] (d R : ℕ) :
    Module.finrank F (reedMuller F d R) = Fintype.card (Monomials F d R) := by
  exact finrank_span_eq_card (linearIndependent_monomialEval (F := F) d R)

end ReedMullerDimensionAttempt
