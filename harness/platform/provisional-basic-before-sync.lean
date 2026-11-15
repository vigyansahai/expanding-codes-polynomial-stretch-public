import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Computability.TuringMachine.Computable

/-!
Provisional interfaces for the public Prove2 mission and Section 2 of the paper.
These definitions spell out the mathematical and finite-machine obligations;
they are not represented as an authenticated export of the platform preamble.
All data and predicates in this module have actual definitions, without holes.
-/

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

abbrev Bit := ZMod 2
abbrev Word (m : ℕ) := Fin m → Bit
abbrev Generator (m n : ℕ) := Matrix (Fin m) (Fin n) Bit
abbrev RandomTape (r : ℕ) := Fin r → Bool

noncomputable def weight {m : ℕ} (y : Word m) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => y i ≠ 0).card

noncomputable def neighbors {m n : ℕ} (G : Generator m n)
    (S : Finset (Fin m)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => ∃ i ∈ S, G i j ≠ 0

def RowWeight {m n : ℕ} (k : ℕ) (G : Generator m n) : Prop :=
  ∀ i, weight (G i) = k

/-- The expansion cutoff is real; it is not rounded before testing row sets. -/
def Expanding {m n : ℕ} (γ : ℝ) (k : ℕ) (t : ℝ)
    (G : Generator m n) : Prop :=
  RowWeight k G ∧ ∀ S : Finset (Fin m), (S.card : ℝ) ≤ t →
    γ * k * S.card ≤ (neighbors G S).card

/-- Finite event probability, expressed as a sum rather than an implicit oracle. -/
noncomputable def eventProbability {α : Type*} [Fintype α]
    (P : PMF α) (A : α → Prop) : ℝ := by
  classical
  exact ∑ a, if A a then (P a).toReal else 0

noncomputable def uniformAcceptance {m : ℕ} (D : Word m → Bool) : ℝ :=
  eventProbability (PMF.uniformOfFintype (Word m)) fun y => D y = true

/-- Standard encodings: unary size, a zero delimiter, then ordered bits. -/
def encodeSize (n : ℕ) : List Bool := List.replicate n true ++ [false]

def encodeWord {m : ℕ} (y : Word m) : List Bool :=
  List.ofFn fun i => decide (y i = 1)

def encodeGenerator {m n : ℕ} (G : Generator m n) : List Bool :=
  (List.finRange m).flatMap fun i => encodeWord (G i)

abbrev SamplerInput (r : Polynomial ℕ) := Σ n : ℕ, RandomTape (r.eval n)
abbrev SamplerOutput (m : ℕ → ℕ) := Σ n : ℕ, Generator (m n) n
abbrev TesterInput (m : ℕ → ℕ) := Σ n : ℕ, Word (m n)

def encodeSamplerInput (r : Polynomial ℕ) (a : SamplerInput r) : List Bool :=
  encodeSize a.1 ++ List.ofFn a.2

def encodeSamplerOutput (m : ℕ → ℕ) (a : SamplerOutput m) : List Bool :=
  encodeSize a.1 ++ encodeGenerator a.2

def encodeTesterInput (m : ℕ → ℕ) (a : TesterInput m) : List Bool :=
  encodeSize a.1 ++ encodeWord a.2

/-- Fixed finite programs, exact sampler law, and actual transition bounds.
The random tape length is the sampler's polynomial step budget. The tester
receives the size and ordered word, with no sampled matrix or transcript. -/
def HasFinitePrograms (m : ℕ → ℕ)
    (P : ∀ n, PMF (Generator (m n) n)) (D : ∀ n, Word (m n) → Bool) : Prop :=
  ∃ (r : Polynomial ℕ) (S : ∀ n, RandomTape (r.eval n) → Generator (m n) n)
    (sampler tester : Turing.TM2ComputableAux Bool Bool) (t : Polynomial ℕ),
    (∀ n, P n = (PMF.uniformOfFintype (RandomTape (r.eval n))).map (S n)) ∧
    (∀ n ω, Turing.TM2OutputsInTime sampler.tm
      ((encodeSamplerInput r ⟨n, ω⟩).map sampler.inputAlphabet.symm)
      (some ((encodeSamplerOutput m ⟨n, S n ω⟩).map sampler.outputAlphabet.symm))
      (r.eval n)) ∧
    (∀ n y, Turing.TM2OutputsInTime tester.tm
      ((encodeTesterInput m ⟨n, y⟩).map tester.inputAlphabet.symm)
      (some ([D n y].map tester.outputAlphabet.symm)) (t.eval (m n + n)))

def GuaranteesAt (ε : ℝ) (k : ℕ) (m : ℕ → ℕ)
    (P : ∀ n, PMF (Generator (m n) n)) (D : ∀ n, Word (m n) → Bool)
    (n : ℕ) : Prop :=
  n < m n ∧ m n < n ^ k ∧
  (∀ G ∈ (P n).support, RowWeight k G) ∧
  1 - (n : ℝ) ^ (-1 / ε) ≤
    eventProbability (P n) (Expanding (1 - ε) k ((n : ℝ) ^ (1 - ε))) ∧
  (∀ G ∈ (P n).support, ∀ x : Word n, ∀ e : Word (m n),
    (weight e : ℝ) ≤ (1 / 2 - ε) * m n → D n (G.mulVec x + e) = true) ∧
  uniformAcceptance (D n) ≤ Real.exp (-ε ^ 2 * m n / 128)

def EfficientFamily (ε : ℝ) (k : ℕ) (m : ℕ → ℕ)
    (P : ∀ n, PMF (Generator (m n) n)) (D : ∀ n, Word (m n) → Bool) : Prop :=
  HasFinitePrograms m P D ∧ ∀ᶠ n in Filter.atTop, GuaranteesAt ε k m P D n

@[simp] theorem neighbors_empty {m n : ℕ} (G : Generator m n) :
    neighbors G ∅ = ∅ := by
  classical
  simp [neighbors]

@[simp] theorem weight_zero (m : ℕ) : weight (0 : Word m) = 0 := by
  classical
  simp [weight]

theorem empty_set_expands {m n : ℕ} (G : Generator m n) (γ : ℝ) (k : ℕ) :
    γ * k * ((∅ : Finset (Fin m)).card : ℝ) ≤ (neighbors G ∅).card := by
  simp

end ExpandingCodes.PolynomialStretch
