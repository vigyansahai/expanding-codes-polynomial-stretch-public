import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_ErasureModel
import Definitions.Def_NKtLB_Machine
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open scoped BigOperators
/-- Unary size prefix, followed by the received word when present. -/
def sizeInput (n : ℕ) : List Bool := List.replicate n true ++ [false]
def wordBits {m : ℕ} (y : Word m) : List Bool := List.ofFn fun i => decide (y i ≠ 0)
def matrixBits {m n : ℕ} (G : Generator m n) : List Bool :=
  (List.ofFn fun i => List.ofFn fun j => decide (G i j ≠ 0)).flatten
noncomputable def sampledRun (M : NKtLB.Machine) (n T L : ℕ) (ω : Fin L → Bool)
    (out : List Bool) : Prop :=
  M.HaltsWith ∅ ⟨sizeInput n, [], [], List.ofFn ω⟩ T (NKtLB.bitsSym out)
/-- Actual transition-table implementations, including output-writing cost. All bounds
are fixed before n, the random tape, G, and y. No implementation property is a premise. -/
noncomputable def EfficientFamily (ε : ℝ) (k : ℕ) (m : ℕ → ℕ)
    (P : ∀ n, PMF (Generator (m n) n)) (D : ∀ n, Word (m n) → Bool) : Prop :=
  ∃ (sampler tester : NKtLB.Machine) (A a B b N : ℕ),
    0 < A ∧ 0 < B ∧ 2 ≤ N ∧
    ∀ n ≥ N,
      n < m n ∧ m n < n ^ k ∧
      (∀ ω : Fin (A * (n + 1) ^ a) → Bool, ∃ G : Generator (m n) n,
        sampledRun sampler n (A * (n + 1) ^ a) (A * (n + 1) ^ a) ω (matrixBits G)) ∧
      (∀ G : Generator (m n) n,
        uniformProb (fun ω : Fin (A * (n + 1) ^ a) → Bool =>
          sampledRun sampler n (A * (n + 1) ^ a) (A * (n + 1) ^ a) ω (matrixBits G)) = (P n G).toReal) ∧
      (∀ y : Word (m n), tester.Computes (B * (m n + n + 1) ^ b)
        (sizeInput n ++ wordBits y) [D n y]) ∧
      (∀ G : Generator (m n) n, P n G ≠ 0 → RowWeight G k) ∧
      1 - (n : ℝ) ^ (-1 / ε) ≤ eventProb (P n)
        (fun G => Expanding G (1 - ε) k ((n : ℝ) ^ (1 - ε))) ∧
      (∀ G : Generator (m n) n, P n G ≠ 0 →
        ∀ (x : Word n) (e : Word (m n)),
          (weight e : ℝ) ≤ (1 / 2 - ε) * m n → D n (G.mulVec x + e) = true) ∧
      uniformProb (fun y : Word (m n) => D n y = true) ≤
        Real.exp (-(ε ^ 2 / 128) * m n)

end ExpandingCodes.PolynomialStretch
