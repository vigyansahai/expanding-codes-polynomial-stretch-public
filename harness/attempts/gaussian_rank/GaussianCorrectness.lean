import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import ExpandingCodes.Computation.GaussianElimination
import Mathlib.Tactic

set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

open Matrix Module LinearMap
open scoped Matrix

variable {F : Type*} [Field F]

private def prodSubmoduleEquiv {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    (p : Submodule F M) (q : Submodule F N) : p.prod q ≃ₗ[F] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1,x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Direct-sum rank identity used to discharge exactly one Gaussian pivot. -/
theorem rank_fromBlocks_zero {m n o p : Type*}
    [Fintype m] [Fintype n] [Fintype o] [Fintype p]
    (A : Matrix m n F) (D : Matrix o p F) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow m o F F
  let f := LinearEquiv.sumArrowLequivProdArrow n p F F
  have hcomp : e.toLinearMap.comp (Matrix.fromBlocks A 0 0 D).mulVecLin =
      (A.mulVecLin.prodMap D.mulVecLin).comp f.toLinearMap := by
    ext v i <;> simp [e, f, Matrix.fromBlocks_mulVec] <;> rfl
  have hr : ((Matrix.fromBlocks A 0 0 D).mulVecLin.range).map e.toLinearMap =
      A.mulVecLin.range.prod D.mulVecLin.range := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearMap.range_prodMap]
  calc
    (Matrix.fromBlocks A 0 0 D).rank =
        finrank F (((Matrix.fromBlocks A 0 0 D).mulVecLin.range).map e.toLinearMap) :=
      (e.finrank_map_eq _).symm
    _ = finrank F (A.mulVecLin.range.prod D.mulVecLin.range) := by rw [hr]
    _ = finrank F (A.mulVecLin.range × D.mulVecLin.range) :=
      (prodSubmoduleEquiv _ _).finrank_eq
    _ = A.rank + D.rank := Module.finrank_prod

/-- Invertible block factors implement Gaussian elimination without changing
rank. This is a proof identity, not an algorithm choosing certificates. -/
theorem rank_fromBlocks_schur {m n o : Type*}
    [Fintype m] [Fintype n] [Fintype o]
    [DecidableEq m] [DecidableEq n] [DecidableEq o]
    (A : Matrix m m F) (B : Matrix m n F) (C : Matrix o m F)
    (D : Matrix o n F) [Invertible A] :
    (Matrix.fromBlocks A B C D).rank = A.rank + (D - C * ⅟A * B).rank := by
  let L := Matrix.fromBlocks (1 : Matrix m m F) 0 (C * ⅟A) (1 : Matrix o o F)
  let U := Matrix.fromBlocks (1 : Matrix m m F) (⅟A * B) 0 (1 : Matrix n n F)
  have hL : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp (by
    dsimp [L]
    rw [Matrix.isUnit_fromBlocks_zero₁₂]
    exact ⟨isUnit_one, isUnit_one⟩)
  have hU : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp (by
    dsimp [U]
    rw [Matrix.isUnit_fromBlocks_zero₂₁]
    exact ⟨isUnit_one, isUnit_one⟩)
  rw [Matrix.fromBlocks_eq_of_invertible₁₁ A B C D]
  change ((L * Matrix.fromBlocks A 0 0 (D - C * ⅟A * B)) * U).rank = _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det U _ hU,
    Matrix.rank_mul_eq_right_of_isUnit_det L _ hL, rank_fromBlocks_zero]

/-- Explicit reindexing that puts the selected pivot at the distinguished
singleton. All other indices occur in their original order. -/
def pivotEquiv {m : ℕ} (p : Fin (m+1)) : PUnit.{1} ⊕ Fin m ≃ Fin (m+1) :=
  (Equiv.sumComm PUnit.{1} (Fin m)).trans
    ((Equiv.optionEquivSumPUnit (Fin m)).symm.trans (finSuccEquiv' p).symm)

@[simp] theorem pivotEquiv_inl {m : ℕ} (p : Fin (m+1)) (u : PUnit.{1}) :
    pivotEquiv p (Sum.inl u) = p := by
  simp [pivotEquiv]

@[simp] theorem pivotEquiv_inr {m : ℕ} (p : Fin (m+1)) (i : Fin m) :
    pivotEquiv p (Sum.inr i) = p.succAbove i := by
  simp [pivotEquiv]

/-- A nonzero scalar pivot contributes exactly one to rank; the remaining
rank is the rank of the concretely computed Schur complement. -/
theorem rank_eq_schur_add_one [DecidableEq F] {m n : ℕ}
    (T : Table F (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : toMatrix T p.1 p.2 ≠ 0) :
    (toMatrix T).rank = (toMatrix (schur T p)).rank + 1 := by
  let M := toMatrix T
  let A : Matrix PUnit.{1} PUnit.{1} F := fun _ _ => M p.1 p.2
  let B : Matrix PUnit.{1} (Fin n) F := fun _ j => M p.1 (p.2.succAbove j)
  let C : Matrix (Fin m) PUnit.{1} F := fun i _ => M (p.1.succAbove i) p.2
  let D : Matrix (Fin m) (Fin n) F :=
    fun i j => M (p.1.succAbove i) (p.2.succAbove j)
  let : Invertible A := {
    invOf := fun _ _ => (M p.1 p.2)⁻¹
    invOf_mul_self := by
      ext i j
      change (∑ _ : PUnit.{1}, (M p.1 p.2)⁻¹ * M p.1 p.2) = _
      simp [M, hp]
    mul_invOf_self := by
      ext i j
      change (∑ _ : PUnit.{1}, M p.1 p.2 * (M p.1 p.2)⁻¹) = _
      simp [M, hp] }
  have hA : A.rank = 1 := by
    simpa using Matrix.rank_of_isUnit A (isUnit_of_invertible A)
  have hM : M.submatrix (pivotEquiv p.1) (pivotEquiv p.2) =
      Matrix.fromBlocks A B C D := by
    ext (i | i) (j | j) <;> simp [Matrix.submatrix_apply, Matrix.fromBlocks, A, B, C, D]
  have hS : D - C * ⅟A * B = toMatrix (schur T p) := by
    have hi : ⅟A = (fun _ _ => (M p.1 p.2)⁻¹ : Matrix PUnit.{1} PUnit.{1} F) := rfl
    rw [hi]
    ext i j
    change D i j - ∑ k : PUnit.{1}, (∑ l : PUnit.{1}, C i l * (M p.1 p.2)⁻¹) * B k j = _
    simp [schur, B, C, D, M, toMatrix, ofMatrix]
  calc
    (toMatrix T).rank = (M.submatrix (pivotEquiv p.1) (pivotEquiv p.2)).rank :=
      (Matrix.rank_submatrix M _ _).symm
    _ = (Matrix.fromBlocks A B C D).rank := by rw [hM]
    _ = A.rank + (D - C * ⅟A * B).rank := rank_fromBlocks_schur A B C D
    _ = (toMatrix (schur T p)).rank + 1 := by rw [hA, hS, Nat.add_comm]

/-- Exact correctness of the deterministic pivot-count algorithm. -/
theorem rank_correct [DecidableEq F] {m n : ℕ} (T : Table F m n) :
    rank T = (toMatrix T).rank := by
  induction m generalizing n with
  | zero =>
    have hz : toMatrix T = 0 := by ext i; exact Fin.elim0 i
    simp [rank, hz]
  | succ m ih =>
    cases n with
    | zero =>
      have hz : toMatrix T = 0 := by ext i j; exact Fin.elim0 j
      simp [rank, hz]
    | succ n =>
      simp only [rank]
      split
      next h => simp [pivot_none h]
      next p h =>
        rw [ih, rank_eq_schur_add_one T p (pivot_some h)]

#print axioms rank_correct

theorem run_correct [DecidableEq F] {m n : ℕ} (T : Table F m n) :
    (run T).1 = (toMatrix T).rank :=
  (run_rank T).trans (rank_correct T)

#print axioms run_correct

end ExpandingCodes.Computation.Gaussian
