import Mathlib
import Definitions.Def_QuantumExpander_Decoder_Setting
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open scoped BigOperators
abbrev Bit := ZMod 2
abbrev Word (m : ℕ) := Fin m → Bit
abbrev Generator (m n : ℕ) := Matrix (Fin m) (Fin n) Bit
noncomputable def weight {I K : Type*} [Fintype I] [Zero K] (v : I → K) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => v i ≠ 0).card
noncomputable def neighbors {I J : Type*} [Fintype I] [Fintype J]
    (G : Matrix I J Bit) (S : Finset I) : Finset J := by
  classical
  exact QuantumExpander.Decoder.nbhdA (fun i j => G i j ≠ 0) S
noncomputable def RowWeight {I J : Type*} [Fintype J] (G : Matrix I J Bit) (k : ℕ) : Prop :=
  ∀ i, weight (G i) = k
noncomputable def Expanding {I J : Type*} [Fintype I] [Fintype J]
    (G : Matrix I J Bit) (γ : ℝ) (k : ℕ) (t : ℝ) : Prop := by
  classical
  exact RowWeight G k ∧
    (if Fintype.card I = 0 then True else
      QuantumExpander.Decoder.IsLeftExpanding (fun i j => G i j ≠ 0) k
        (t / Fintype.card I) (1 - γ))
noncomputable def eventProb {Ω : Type*} [Fintype Ω] (P : PMF Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then (P ω).toReal else 0
noncomputable def uniformProb {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) : ℝ :=
  eventProb (PMF.uniformOfFintype Ω) E
noncomputable def bernoulliWord (m : ℕ) (p : ℝ) (v : Word m) : ℝ :=
  p ^ weight v * (1 - p) ^ (m - weight v)

end ExpandingCodes.PolynomialStretch
