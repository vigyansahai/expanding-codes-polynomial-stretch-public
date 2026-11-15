import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_PolynomialTest
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open scoped BigOperators
noncomputable def ambiguity {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (E : Finset I) : Submodule F (I → F) where
  carrier := {v | v ∈ C ∧ ∀ i, i ∉ E → v i = 0}
  zero_mem' := ⟨C.zero_mem, by simp⟩
  add_mem' := by
    intro v w hv hw
    exact ⟨C.add_mem hv.1 hw.1, fun i hi => by simp [hv.2 i hi, hw.2 i hi]⟩
  smul_mem' := by
    intro a v hv
    exact ⟨C.smul_mem a hv.1, fun i hi => by simp [hv.2 i hi]⟩
noncomputable def erasureExpectation {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (p : ℝ) : ℝ := by
  classical
  exact ∑ E : Finset I, p ^ E.card * (1 - p) ^ (Fintype.card I - E.card) *
    (Module.finrank F (ambiguity C E) : ℝ)
noncomputable def DoublyTransitiveCode {F : Type*} [Field F] (M : ℕ)
    (C : Submodule F (Fin M → F)) : Prop :=
  ∃ H : Subgroup (Equiv.Perm (Fin M)),
    (∀ σ ∈ H, ∀ c ∈ C, (fun i => c (σ i)) ∈ C) ∧
    ∀ a b a' b' : Fin M, a ≠ b → a' ≠ b' →
      ∃ σ ∈ H, σ a = a' ∧ σ b = b'
noncomputable def limitingRate (d : ℕ) : ℝ :=
  (MeasureTheory.volume {x : Fin d → ℝ |
    (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ ((d : ℝ) - 3) / 2}).toReal
noncomputable def auxiliaryCode {d n : ℕ} (g : Geometry d n) :=
  reedMuller g.F d (auxiliaryDegree (Fintype.card g.F) d)

end ExpandingCodes.PolynomialStretch
