import ExpandingCodes.Construction.Implementation
import ExpandingCodes.Construction.ExpansionTransfer
import ExpandingCodes.Computation.TapeCompiler
import ExpandingCodes.Computation.Basic

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem wordBits_injective {m : ℕ} : Function.Injective (wordBits (m := m)) := by
  intro v w h
  have hh := List.ofFn_injective h
  funext i
  have hi := congrFun hh i
  have hcases (a : Bit) : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (v i) with hv | hv <;> rcases hcases (w i) with hw | hw <;> simp_all

theorem matrixBits_injective {m n : ℕ} :
    Function.Injective (matrixBits (m := m) (n := n)) := by
  induction m with
  | zero =>
    intro G H h
    funext i
    exact Fin.elim0 i
  | succ m ih =>
    intro G H h
    have hs : wordBits (G 0) ++ matrixBits (fun i => G i.succ) =
        wordBits (H 0) ++ matrixBits (fun i => H i.succ) := by
      simpa only [matrixBits, wordBits, List.ofFn_succ, List.flatten_cons] using h
    obtain ⟨hzero, htail⟩ := List.append_inj hs (by simp [wordBits])
    have hz := wordBits_injective hzero
    have ht := ih htail
    funext i
    exact Fin.cases hz (fun j => congrFun ht j) i

open ExpandingCodes.Computation

/-- Convert an actual finite source program's uniform source-step bound to the
canonical finite transition-table tester clause, with explicit constant overhead. -/
theorem testerImplementation_of_tape {R B L : ℕ}
    (θ : ℚ) (g : ∀ n, Geometry (dimension (θ : ℝ)) n)
    (P : TapeProgram R B L) (C b N : ℕ) (hN : 2 ≤ N)
    (h : ∀ n ≥ N, ∀ y : Word (rowCount (dimension (θ : ℝ)) n),
      ∃ t ≤ C * (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b,
        P.halted (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t) ∧
          (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t).output =
            [rankTest (θ : ℝ) (g n) y]) : TesterImplementation θ g := by
  refine ⟨TapeCompiler.compile P, 2*C+1, b, N, by omega, hN, ?_⟩
  intro n hn y
  obtain ⟨t, ht, hh, hout⟩ := h n hn y
  have hp : 1 ≤ (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b :=
    one_le_pow₀ (by omega)
  have htime : 1+2*t ≤ (2*C+1) * (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b := by
    nlinarith
  have hm := (TapeCompiler.compile_computes P (sizeInput n ++ wordBits y) t hh).mono htime
  simpa only [hout] using hm

/-- The sampler compiler bridge separates source execution from the independently
provable finite uniform law of its mathematical output function. -/
theorem samplerImplementation_of_tape {R B L : ℕ}
    (θ : ℚ) (g : ∀ n, Geometry (dimension (θ : ℝ)) n)
    (P : TapeProgram R B L) (C a N : ℕ) (hN : 2 ≤ N)
    (f : ∀ n, (Fin ((2*C+1) * (n+1)^a) → Bool) →
      Generator (rowCount (dimension (θ : ℝ)) n) n)
    (h : ∀ n ≥ N, ∀ ω : Fin ((2*C+1) * (n+1)^a) → Bool,
      ∃ t ≤ C * (n+1)^a,
        P.halted (P.run ⟨sizeInput n, [], [], List.ofFn ω⟩ t) ∧
          (P.run ⟨sizeInput n, [], [], List.ofFn ω⟩ t).output = matrixBits (f n ω))
    (hlaw : ∀ n ≥ N, ∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
      uniformProb (fun ω : Fin ((2*C+1) * (n+1)^a) → Bool => f n ω = G) =
        (sampleLaw (θ : ℝ) n (g n) G).toReal) : SamplerImplementation θ g := by
  let M := TapeCompiler.compile P
  have hr (n : ℕ) (hn : N ≤ n) (ω : Fin ((2*C+1) * (n+1)^a) → Bool) :
      sampledRun M n ((2*C+1) * (n+1)^a) ((2*C+1) * (n+1)^a) ω
        (matrixBits (f n ω)) := by
    obtain ⟨t, ht, hh, hout⟩ := h n hn ω
    have hp : 1 ≤ (n+1)^a := one_le_pow₀ (by omega)
    have htime : 1+2*t ≤ (2*C+1) * (n+1)^a := by nlinarith
    have hm := (TapeCompiler.compile_halts P ∅ ⟨sizeInput n, [], [], List.ofFn ω⟩ t hh).mono htime
    simpa only [sampledRun, M, hout] using hm
  refine ⟨M, 2*C+1, a, N, by omega, hN, ?_⟩
  intro n hn
  refine ⟨fun ω => ⟨f n ω, hr n hn ω⟩, ?_⟩
  intro G
  rw [← hlaw n hn G]
  apply uniformProb_congr
  intro ω
  constructor
  · intro hrun
    have hb := NKtLB.Machine.HaltsWith.output_unique hrun (hr n hn ω)
    exact (matrixBits_injective (NKtLB.Machine.bitsSym_injective hb)).symm
  · intro heq
    rw [← heq]
    exact hr n hn ω

end ExpandingCodes.PolynomialStretch
