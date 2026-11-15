import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryModel
set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

noncomputable def dimension (ε : ℝ) : ℕ := 2 * ⌈512 * ε⁻¹ ^ 2⌉₊
noncomputable def arity (ε : ℝ) : ℕ := ⌈4 * (dimension ε : ℝ) ^ 2 * ε⁻¹ ^ 2⌉₊
def fieldExponent (d n : ℕ) : ℕ := max 1 (Nat.clog 2 (n ^ (2 * d)))
def fieldSize (d n : ℕ) : ℕ := 2 ^ fieldExponent d n
def rowCount (d n : ℕ) : ℕ := fieldSize d n ^ d
noncomputable def buckets (ε : ℝ) (n : ℕ) : ℕ := 2 ^ Nat.log 2 (n / arity ε)
/-- Finite field and public index choices; no algorithmic or expansion guarantee is a field. -/
structure Geometry (d n : ℕ) where
  F : Type
  field : Field F
  finite : Fintype F
  charTwo : CharP F 2
  elements : Fin (fieldSize d n) ≃ F
  rowOrder : Fin (rowCount d n) ≃ (Fin d → F)
attribute [instance] Geometry.field Geometry.finite Geometry.charTwo
noncomputable def alpha {d n : ℕ} (g : Geometry d n) {k : ℕ} (i : Fin k) : g.F :=
  if h : i.val < fieldSize d n then g.elements ⟨i.val, h⟩ else 0

end ExpandingCodes.PolynomialStretch
