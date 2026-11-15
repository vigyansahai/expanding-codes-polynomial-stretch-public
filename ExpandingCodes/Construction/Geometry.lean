import Definitions.Def_ExpandingCodes_PolynomialStretch_Parameters
import Mathlib.FieldTheory.Finite.GaloisField

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

theorem fieldExponent_pos (d n : ℕ) : 0 < fieldExponent d n := by
  unfold fieldExponent
  omega

theorem fieldSize_pos (d n : ℕ) : 0 < fieldSize d n := by
  exact pow_pos (by decide) _

theorem fieldSize_ge_two (d n : ℕ) : 2 ≤ fieldSize d n := by
  unfold fieldSize
  have h := fieldExponent_pos d n
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ fieldExponent d n := Nat.pow_le_pow_right (by decide) h

theorem geometry_card {d n : ℕ} (g : Geometry d n) :
    Fintype.card g.F = fieldSize d n := by
  simpa using Fintype.card_congr g.elements.symm

/-- Honest finite characteristic-two fields and public enumerations exist.
No algorithmic, rank, or expansion assertion is inserted into this data. -/
noncomputable def standardGeometry (d n : ℕ) : Geometry d n := by
  let F := GaloisField 2 (fieldExponent d n)
  letI : Fintype F := Fintype.ofFinite F
  have he : fieldExponent d n ≠ 0 := (fieldExponent_pos d n).ne'
  have hcard : Fintype.card F = fieldSize d n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (fieldExponent d n) he
  exact {
    F := F
    field := inferInstance
    finite := inferInstance
    charTwo := inferInstance
    elements := Fintype.equivOfCardEq (by simpa using hcard.symm)
    rowOrder := Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin, Fintype.card_fun, hcard]
      rfl) }

theorem geometry_exists (d n : ℕ) : Nonempty (Geometry d n) :=
  ⟨standardGeometry d n⟩

end ExpandingCodes.PolynomialStretch
