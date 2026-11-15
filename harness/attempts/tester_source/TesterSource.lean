import ExpandingCodes.Computation.SourceBridge
import ExpandingCodes.Computation.PolynomialBounds
import ExpandingCodes.Construction.BinaryGeometry

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

/-- Assemble the actual source runtime theorem, a polynomial envelope in
m+n, and the proved source compiler into the exact canonical tester clause. -/
theorem binary_tester_of_source {R B L : ℕ} (θ : ℚ)
    (P : TapeProgram R B L) (time : ℕ → ℕ) (N : ℕ)
    (htime : PolynomialBound time)
    (hsource : ∀ n ≥ N, ∀ y : Word (rowCount (dimension (θ : ℝ)) n),
      ∃ t ≤ time (rowCount (dimension (θ : ℝ)) n+n),
        P.halted (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t) ∧
          (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t).output =
            [rankTest (θ : ℝ) (binaryGeometry (dimension (θ : ℝ)) n) y]) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  obtain ⟨C,a,hbound⟩ := htime
  apply testerImplementation_of_tape θ (fun n => binaryGeometry (dimension (θ : ℝ)) n)
    P C a (max N 2) (le_max_right _ _)
  intro n hn y
  obtain ⟨t,ht,hh,hout⟩ := hsource n ((le_max_left N 2).trans hn) y
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hx : 2 ≤ rowCount (dimension (θ : ℝ)) n+n := by omega
  exact ⟨t,ht.trans (hbound _ hx),hh,hout⟩

#print axioms binary_tester_of_source
end ExpandingCodes.PolynomialStretch
