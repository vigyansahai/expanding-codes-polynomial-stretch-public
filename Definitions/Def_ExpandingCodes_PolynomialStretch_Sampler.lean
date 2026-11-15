import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_Parameters
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open scoped BigOperators
abbrev Forms (F : Type*) (d k : ℕ) := Fin 2 → Fin k → F → Fin d → F
abbrev Hashes (F : Type*) (k b : ℕ) := Fin k → (F × F × F) → Fin b
noncomputable instance bucketNonempty (ε : ℝ) (n : ℕ) : Nonempty (Fin (buckets ε n)) :=
  ⟨⟨0, by unfold buckets; exact pow_pos (by decide) _⟩⟩
noncomputable def fixedForm {d n k : ℕ} (g : Geometry d n) (i : Fin k) (z : Fin d → g.F) : g.F :=
  ∑ j, alpha g i ^ j.val * z j
noncomputable def linearForm {F : Type*} [Field F] {d : ℕ} (a z : Fin d → F) : F :=
  ∑ j, a j * z j
noncomputable def address {d n k : ℕ} (g : Geometry d n) (s : Forms g.F d k)
    (i : Fin k) (z : Fin d → g.F) : g.F × g.F × g.F :=
  let a := fixedForm g i z
  (a, linearForm (s 0 i a) z, linearForm (s 1 i a) z)
noncomputable def preliminary {d n k : ℕ} (g : Geometry d n) (s : Forms g.F d k) :
    Matrix (Fin (rowCount d n)) (Fin k × (g.F × g.F × g.F)) Bit := by
  classical
  exact fun z c => if address g s c.1 (g.rowOrder z) = c.2 then 1 else 0
noncomputable def combined {d n k b : ℕ} (g : Geometry d n) (s : Forms g.F d k)
    (h : Hashes g.F k b) : Generator (rowCount d n) n := by
  classical
  exact fun z j => if ∃ i : Fin k, ∃ u : Fin b,
    j.val = i.val * b + u.val ∧ h i (address g s i (g.rowOrder z)) = u then 1 else 0
noncomputable def sampleLaw (ε : ℝ) (n : ℕ) (g : Geometry (dimension ε) n) :
    PMF (Generator (rowCount (dimension ε) n) n) :=
  (PMF.uniformOfFintype _ : PMF (Forms g.F (dimension ε) (arity ε) ×
    Hashes g.F (arity ε) (buckets ε n))).map fun s => combined g s.1 s.2
noncomputable def PreliminaryGood (ε : ℝ) (n : ℕ) (g : Geometry (dimension ε) n)
    (s : Forms g.F (dimension ε) (arity ε)) : Prop :=
  ∀ S : Finset (Fin (rowCount (dimension ε) n)),
    (S.card : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
    ((arity ε : ℝ) - dimension ε + 1) * S.card ≤ ((neighbors (preliminary g s) S).card : ℝ)

end ExpandingCodes.PolynomialStretch
