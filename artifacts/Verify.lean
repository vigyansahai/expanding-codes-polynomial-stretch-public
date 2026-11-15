import Solutions.Sol_ExpandingCodes_PolynomialStretch_expanding_codes

set_option autoImplicit false
open scoped Classical BigOperators

example : (∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (ExpandingCodes.PolynomialStretch.Generator (m n) n))
        (D : ∀ n, ExpandingCodes.PolynomialStretch.Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ ExpandingCodes.PolynomialStretch.EfficientFamily ε k m P D) := @solution

#print axioms solution
