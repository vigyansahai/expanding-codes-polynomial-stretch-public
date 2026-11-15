import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
set_option autoImplicit false
namespace ExpandingCodes.Computation.Gaussian
open Matrix Module LinearMap
open scoped Matrix
variable {F : Type*} [Field F]
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
end ExpandingCodes.Computation.Gaussian
