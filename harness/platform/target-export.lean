import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

/-- Theorem 1.1: constant arity, polynomial stretch and runtime, and the unconditional
near-half arbitrary-error test. The absolute arity constant precedes ε. -/
theorem expanding_codes :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := by sorry

end ExpandingCodes.PolynomialStretch

