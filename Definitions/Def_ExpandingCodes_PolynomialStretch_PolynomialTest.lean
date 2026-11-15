import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_Sampler
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open scoped BigOperators
abbrev Monomials (F : Type*) [Fintype F] (d R : ℕ) :=
  {a : Fin d → Fin (Fintype.card F) // ∑ i, (a i).val ≤ R}
noncomputable def monomialEval {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (z : Fin d → F) : F := ∏ i, z i ^ (a.val i).val
noncomputable def reedMuller (F : Type*) [Field F] [Fintype F] (d R : ℕ) :
    Submodule F ((Fin d → F) → F) :=
  Submodule.span F (Set.range (monomialEval (F := F) (d := d) (R := R)))
/-- Integer floor before conversion; construction parameters make the numerator positive. -/
def auxiliaryDegree (q d : ℕ) : ℕ :=
  ((((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2).toNat
noncomputable def evaluationMatrix {d n : ℕ} (g : Geometry d n) :
    Matrix (Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d))
      (Fin (rowCount d n)) g.F :=
  fun a z => monomialEval a (g.rowOrder z)
noncomputable def testMatrix {d n : ℕ} (g : Geometry d n) (y : Word (rowCount d n)) :=
  (evaluationMatrix g * Matrix.diagonal (fun z => if y z = 0 then (0 : g.F) else 1)) *
    (evaluationMatrix g).transpose
noncomputable def rankTest (ε : ℝ) {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) : Bool := by
  classical
  exact decide ((testMatrix g y).rank ≤ (1 / 2 - ε / 2) * (rowCount d n : ℝ))

end ExpandingCodes.PolynomialStretch
