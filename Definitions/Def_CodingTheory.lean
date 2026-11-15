import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Matrix.Notation

namespace CodingTheory

open scoped BigOperators

/-- A word over the alphabet `F`, with coordinates indexed by `ι`. -/
abbrev Word (F ι : Type*) := ι → F

/-- A linear code of length indexed by `ι` over the finite field `F`. -/
abbrev LinearCode (F ι : Type*) [Field F] := Submodule F (Word F ι)

/-- The standard coordinatewise bilinear form on words. -/
def dotForm (F ι : Type*) [Field F] [Fintype ι] :
    LinearMap.BilinForm F (Word F ι) :=
  dotProductBilin F F

/-- The dual of a linear code under the standard coordinatewise bilinear form. -/
def dualCode (F ι : Type*) [Field F] [Fintype ι]
    (C : LinearCode F ι) : LinearCode F ι :=
  (dotForm F ι).orthogonal C

/-- The homogeneous Hamming weight enumerator as a bivariate polynomial over `ℤ`. -/
noncomputable def hammingWeightEnumeratorPolynomial (F ι : Type*) [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] [DecidableEq ι]
    (C : LinearCode F ι) : MvPolynomial (Fin 2) ℤ :=
  letI := Fintype.ofFinite C
  ∑ c : C,
    MvPolynomial.X 0 ^ (Fintype.card ι - hammingNorm (c : ι → F)) *
      MvPolynomial.X 1 ^ hammingNorm (c : ι → F)

/-- The homogeneous Hamming weight enumerator evaluated at two complex variables. -/
noncomputable def hammingWeightEnumerator (F ι : Type*) [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] [DecidableEq ι]
    (C : LinearCode F ι) (X Y : ℂ) : ℂ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℂ) ![X, Y]
    (hammingWeightEnumeratorPolynomial F ι C)

/-- Evaluating the polynomial weight enumerator gives the complex weight enumerator. -/
@[simp] theorem hammingWeightEnumeratorPolynomial_eval
    (F ι : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (C : LinearCode F ι) (X Y : ℂ) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℂ) ![X, Y]
        (hammingWeightEnumeratorPolynomial F ι C) =
      hammingWeightEnumerator F ι C X Y := rfl

end CodingTheory
