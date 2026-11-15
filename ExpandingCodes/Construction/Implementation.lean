import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

/-- The two exact sampling clauses of `EfficientFamily`, with one fixed finite
transition table and polynomial bound before the size and random tape. -/
noncomputable def SamplerImplementation (θ : ℚ)
    (g : ∀ n, Geometry (dimension (θ : ℝ)) n) : Prop :=
  ∃ (sampler : NKtLB.Machine) (A a N : ℕ), 0 < A ∧ 2 ≤ N ∧ ∀ n ≥ N,
    (∀ ω : Fin (A * (n + 1) ^ a) → Bool,
      ∃ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
        sampledRun sampler n (A * (n + 1) ^ a) (A * (n + 1) ^ a) ω (matrixBits G)) ∧
    (∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
      uniformProb (fun ω : Fin (A * (n + 1) ^ a) → Bool =>
        sampledRun sampler n (A * (n + 1) ^ a) (A * (n + 1) ^ a) ω (matrixBits G)) =
          (sampleLaw (θ : ℝ) n (g n) G).toReal)

/-- The exact deterministic transition-table clause of `EfficientFamily`.
Rational θ is the parameter embedded in the finite tester program. -/
noncomputable def TesterImplementation (θ : ℚ)
    (g : ∀ n, Geometry (dimension (θ : ℝ)) n) : Prop :=
  ∃ (tester : NKtLB.Machine) (B b N : ℕ), 0 < B ∧ 2 ≤ N ∧ ∀ n ≥ N,
    ∀ y : Word (rowCount (dimension (θ : ℝ)) n),
      tester.Computes (B * (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b)
        (sizeInput n ++ wordBits y) [rankTest (θ : ℝ) (g n) y]

end ExpandingCodes.PolynomialStretch
