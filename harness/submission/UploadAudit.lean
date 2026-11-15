import harness.submission.Upload
set_option autoImplicit false

-- Local audit, omitted from the upload artifact.
open ExpandingCodes.PolynomialStretch in
example :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := @solution

set_option pp.universes true in
set_option pp.explicit true in
#check @solution
#print axioms solution
