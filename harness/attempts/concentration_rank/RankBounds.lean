import ExpandingCodes.Algebra.CombinedOrthogonality
import Definitions.Def_ExpandingCodes_PolynomialStretch_ErasureModel
import ExpandingCodes.Probability.BoundedDifferences

/-!
# Algebraic rank ingredients for the canonical polynomial test

The statements use the mission's exact matrices, auxiliary code and ambiguity.
The point support is transported through the exact `Geometry.rowOrder` equivalence.
Sylvester's inequality, coordinate restriction rank-nullity, and a restricted
Gram factorization prove the rank lower bound. A one-coordinate difference has
weight at most one, which proves the real-valued rank has unit bounded differences.
No erasure or probabilistic hypotheses occur in these algebraic statements.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module

/-- Sylvester's inequality for finite matrices over an arbitrary field. -/
theorem matrix_rank_add_rank_le_rank_mul_add {F I J K : Type*} [Field F]
    [Fintype I] [Fintype J] [Fintype K]
    (A : Matrix I J F) (B : Matrix J K F) :
    A.rank + B.rank ≤ (A*B).rank + Fintype.card J := by
  let f := A.mulVecLin
  let g := B.mulVecLin
  let h := f.domRestrict (LinearMap.range g)
  let e : LinearMap.ker h →ₗ[F] LinearMap.ker f :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f => z.val) hxy
  have hk := LinearMap.finrank_le_finrank_of_injective he
  have hn := h.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range h = LinearMap.range (f.comp g) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  rw [hr] at hn
  change A.rank + B.rank ≤ (A*B).rank + Fintype.card J
  change Module.finrank F (LinearMap.range f) + Module.finrank F (LinearMap.range g) ≤
    Module.finrank F (LinearMap.range (A*B).mulVecLin) + Fintype.card J
  rw [Matrix.mulVecLin_mul]
  change Module.finrank F (LinearMap.range f) + Module.finrank F (LinearMap.range g) ≤
    Module.finrank F (LinearMap.range (f.comp g)) + Fintype.card J
  rw [Module.finrank_pi] at hf
  omega

/-- Subadditivity of matrix rank, using the sum of the two image spaces. -/
theorem matrix_rank_add_le {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (A B : Matrix I J F) : (A+B).rank ≤ A.rank + B.rank := by
  have hr : LinearMap.range (A+B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  exact (Submodule.finrank_mono hr).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Restrict a codeword to a finite set of observed coordinates. -/
def codeRestriction {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (S : Finset I) : C →ₗ[F] (S → F) where
  toFun c i := c.val i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem codeRestriction_ker {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (C : Submodule F (I → F)) (S : Finset I) :
    LinearMap.ker (codeRestriction C S) = (ambiguity C Sᶜ).comap C.subtype := by
  ext c
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    exact ⟨c.property, fun i hi => congrFun h ⟨i, by simpa using hi⟩⟩
  · intro h
    funext i
    exact h.2 i.val (by simp)

/-- Rank-nullity identifies the exact loss under coordinate restriction. -/
theorem finrank_codeRestriction_add_ambiguity {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (C : Submodule F (I → F)) (S : Finset I) :
    finrank F (LinearMap.range (codeRestriction C S)) +
      finrank F (ambiguity C Sᶜ) = finrank F C := by
  have hle : ambiguity C Sᶜ ≤ C := fun _ hc => hc.1
  have he := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [← he, ← codeRestriction_ker]
  exact LinearMap.finrank_range_add_finrank_ker _

/-- Restricting a row generator matrix is exactly restriction of its row code. -/
theorem matrix_restriction_rank_add_ambiguity {F I J : Type*} [Field F]
    [Fintype I] [Fintype J] [DecidableEq I] (A : Matrix J I F) (S : Finset I) :
    (A.submatrix id (Subtype.val : S → I)).rank +
      finrank F (ambiguity (Submodule.span F (Set.range A.row)) Sᶜ) =
        finrank F (Submodule.span F (Set.range A.row)) := by
  let C := Submodule.span F (Set.range A.row)
  let r : (I → F) →ₗ[F] (S → F) := LinearMap.funLeft F F Subtype.val
  have hr : LinearMap.range (codeRestriction C S) =
      Submodule.span F (Set.range (A.submatrix id (Subtype.val : S → I)).row) := by
    change LinearMap.range (r.domRestrict C) = _
    rw [LinearMap.range_domRestrict]
    dsimp [C]
    rw [LinearMap.map_span]
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨A.row j, ⟨j, rfl⟩, rfl⟩
  rw [Matrix.rank_eq_finrank_span_row, ← hr]
  exact finrank_codeRestriction_add_ambiguity C S

/-- Actual support of a binary word, indexed by the canonical geometric points. -/
noncomputable def supportPoints {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) : Finset (Fin d → g.F) :=
  (Finset.univ.filter (fun z => y z ≠ 0)).image g.rowOrder

@[simp] theorem mem_supportPoints {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) (z : Fin d → g.F) :
    z ∈ supportPoints g y ↔ y (g.rowOrder.symm z) ≠ 0 := by
  simp only [supportPoints, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hiz⟩
    simpa only [← hiz, g.rowOrder.symm_apply_apply] using hi
  · intro hz
    exact ⟨g.rowOrder.symm z, hz, g.rowOrder.apply_symm_apply z⟩

@[simp] theorem card_supportPoints {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) : (supportPoints g y).card = weight y := by
  unfold supportPoints
  rw [Finset.card_image_of_injective _ g.rowOrder.injective]
  unfold weight
  congr 1
  ext z
  simp

/-- Evaluation matrix with precisely the columns on a specified geometric set. -/
noncomputable def restrictedEvaluationMatrix {d n : ℕ} (g : Geometry d n)
    (S : Finset (Fin d → g.F)) :
    Matrix (Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d)) S g.F :=
  fun a z => monomialEval a z.val

/-- The canonical row enumeration preserves the exact auxiliary-code dimension. -/
theorem evaluationMatrix_rank {d n : ℕ} (g : Geometry d n) :
    (evaluationMatrix g).rank = finrank g.F (auxiliaryCode g) := by
  let A : Matrix (Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d))
      (Fin d → g.F) g.F := fun a z => monomialEval a z
  change (A.submatrix (Equiv.refl _) g.rowOrder).rank = _
  rw [Matrix.rank_submatrix]
  exact Matrix.rank_eq_finrank_span_row A

/-- Restriction loses exactly the ambiguity supported outside the observed points. -/
theorem restrictedEvaluationMatrix_rank_add_ambiguity {d n : ℕ} (g : Geometry d n)
    (S : Finset (Fin d → g.F)) :
    (restrictedEvaluationMatrix g S).rank +
      finrank g.F (ambiguity (auxiliaryCode g) Sᶜ) = finrank g.F (auxiliaryCode g) := by
  exact matrix_restriction_rank_add_ambiguity
    (fun a z => monomialEval (F := g.F) (d := d)
      (R := auxiliaryDegree (Fintype.card g.F) d) a z) S

/-- Subtractive form of the exact restriction rank formula. -/
theorem restrictedEvaluationMatrix_rank {d n : ℕ} (g : Geometry d n)
    (S : Finset (Fin d → g.F)) :
    (restrictedEvaluationMatrix g S).rank = finrank g.F (auxiliaryCode g) -
      finrank g.F (ambiguity (auxiliaryCode g) Sᶜ) :=
  Nat.eq_sub_of_add_eq (restrictedEvaluationMatrix_rank_add_ambiguity g S)

/-- The diagonal binary mask is exactly restriction to the nonzero columns. -/
theorem testMatrix_eq_restricted_mul_transpose {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    testMatrix g y = restrictedEvaluationMatrix g (supportPoints g y) *
      (restrictedEvaluationMatrix g (supportPoints g y)).transpose := by
  ext a b
  rw [testMatrix_apply, Matrix.mul_apply]
  simp only [restrictedEvaluationMatrix, Matrix.transpose_apply]
  rw [Finset.sum_coe_sort (supportPoints g y)
    (fun z => monomialEval a z * monomialEval b z)]
  have he : (∑ i, monomialEval a (g.rowOrder i) * monomialEval b (g.rowOrder i) *
      bitToField g.F (y i)) =
      ∑ z : Fin d → g.F, monomialEval a z * monomialEval b z *
        bitToField g.F (y (g.rowOrder.symm z)) := by
    exact Fintype.sum_equiv g.rowOrder _ _ (by intro i; simp)
  rw [he]
  calc
    _ = ∑ z ∈ supportPoints g y, monomialEval a z * monomialEval b z *
          bitToField g.F (y (g.rowOrder.symm z)) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ hz
      have hy : y (g.rowOrder.symm z) = 0 := by simpa using hz
      simp [hy]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [bitToField_apply, if_neg ((mem_supportPoints g y z).mp hz), mul_one]

/-- The algebraic rank lower bound used in Proposition 2.5, in additive natural form. -/
theorem testMatrix_rank_lower_additive {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    2 * finrank g.F (auxiliaryCode g) ≤ (testMatrix g y).rank +
      2 * finrank g.F (ambiguity (auxiliaryCode g) (supportPoints g y)ᶜ) + weight y := by
  have hs := matrix_rank_add_rank_le_rank_mul_add
    (restrictedEvaluationMatrix g (supportPoints g y))
    (restrictedEvaluationMatrix g (supportPoints g y)).transpose
  rw [Matrix.rank_transpose, ← testMatrix_eq_restricted_mul_transpose,
    Fintype.card_coe, card_supportPoints] at hs
  have hr := restrictedEvaluationMatrix_rank_add_ambiguity g (supportPoints g y)
  omega

/-- Real-valued form avoids truncation in the two ambiguity corrections. -/
theorem testMatrix_rank_lower {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    2 * (finrank g.F (auxiliaryCode g) : ℝ) -
      2 * (finrank g.F (ambiguity (auxiliaryCode g) (supportPoints g y)ᶜ) : ℝ) -
        (weight y : ℝ) ≤ ((testMatrix g y).rank : ℝ) := by
  have h : 2 * (finrank g.F (auxiliaryCode g) : ℝ) ≤
      ((testMatrix g y).rank : ℝ) + 2 * (finrank g.F
        (ambiguity (auxiliaryCode g) (supportPoints g y)ᶜ) : ℝ) + (weight y : ℝ) := by
    exact_mod_cast testMatrix_rank_lower_additive g y
  linarith

/-- A word supported at one coordinate has Hamming weight at most one. -/
theorem weight_le_one_of_eq_zero_off {m : ℕ} (e : Word m) (i : Fin m)
    (he : ∀ j, j ≠ i → e j = 0) : weight e ≤ 1 := by
  unfold weight
  have hsub : (Finset.univ.filter (fun j => e j ≠ 0)) ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_singleton]
    by_contra hji
    exact (Finset.mem_filter.mp hj).2 (he j hji)
  simpa using Finset.card_le_card hsub

/-- Changing one coordinate changes the matrix rank by at most one. -/
theorem testMatrix_rank_abs_sub_le_one {d n : ℕ} (g : Geometry d n)
    (y y' : Word (rowCount d n)) (i : Fin (rowCount d n))
    (h : ∀ j, j ≠ i → y' j = y j) :
    |((testMatrix g y').rank : ℝ) - ((testMatrix g y).rank : ℝ)| ≤ 1 := by
  have hdir (u v : Word (rowCount d n)) (huv : ∀ j, j ≠ i → v j = u j) :
      (testMatrix g v).rank ≤ (testMatrix g u).rank + 1 := by
    have hw : weight (v-u) ≤ 1 := weight_le_one_of_eq_zero_off _ i (by
      intro j hj
      simp [huv j hj])
    have hv : v = u + (v-u) := by abel
    calc
      _ = (testMatrix g u + testMatrix g (v-u)).rank := by
        rw [← testMatrix_add, ← hv]
      _ ≤ (testMatrix g u).rank + (testMatrix g (v-u)).rank := matrix_rank_add_le _ _
      _ ≤ (testMatrix g u).rank + 1 :=
        Nat.add_le_add_left ((testMatrix_rank_le_weight g _).trans hw) _
  have h₁ : ((testMatrix g y').rank : ℝ) ≤ ((testMatrix g y).rank : ℝ) + 1 := by
    exact_mod_cast hdir y y' h
  have h₂ : ((testMatrix g y).rank : ℝ) ≤ ((testMatrix g y').rank : ℝ) + 1 := by
    exact_mod_cast hdir y' y (fun j hj => (h j hj).symm)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Identify a Boolean cube point with the mission's binary word. -/
def boolWord {m : ℕ} (x : Fin m → Bool) : Word m := fun i => if x i then 1 else 0

theorem testMatrix_rank_boundedDifferences {d n : ℕ} (g : Geometry d n) :
    HasUnitBoundedDifferences
      (fun x : Fin (rowCount d n) → Bool => ((testMatrix g (boolWord x)).rank : ℝ)) := by
  intro x i b
  apply testMatrix_rank_abs_sub_le_one g (boolWord x) (boolWord (Function.update x i b)) i
  intro j hj
  simp [boolWord, Function.update_of_ne hj]

end ExpandingCodes.PolynomialStretch
