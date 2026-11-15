import Mathlib
import Theorems.Thm_ExpandingCodes_PolynomialStretch_construction

set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch

/-! The precise construction supplies the actual sampler and tester machines,
expansion and decoding estimates, and the uniform constant. This final packaging
step selects its family and retains the headline polynomial-stretch bound. -/

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := by
  obtain ⟨Cd, Ck, _hCd, hCk, hconstruction⟩ := construction
  refine ⟨Ck, hCk, ?_⟩
  intro ε hε hhalf
  obtain ⟨θ, _hθlower, _hθupper, _hd, hk, g, hefficient, _hgrowth⟩ :=
    hconstruction ε hε hhalf
  exact ⟨arity (θ : ℝ), rowCount (dimension (θ : ℝ)),
    (fun n => sampleLaw (θ : ℝ) n (g n)),
    (fun n => rankTest (θ : ℝ) (g n)), hk, hefficient⟩
