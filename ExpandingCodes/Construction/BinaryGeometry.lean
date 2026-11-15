import ExpandingCodes.Computation.BinaryField
import ExpandingCodes.Construction.Geometry

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

/-- Finite-field geometry using the least successful explicit binary modulus.
Rows are enumerated by base-`q` digits, each interpreted by its binary
coefficient vector. No cardinality-choice enumeration enters either map. -/
noncomputable def binaryGeometry (d n : ℕ) : Geometry d n where
  F := BinaryField.Carrier (fieldExponent d n) (fieldExponent_pos d n)
  field := inferInstance
  finite := inferInstance
  charTwo := inferInstance
  elements := BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n)
  rowOrder := finFunctionFinEquiv.symm.trans
    (Equiv.piCongrRight fun _ => BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n))

theorem binaryGeometry_elements (d n : ℕ) (i : Fin (fieldSize d n)) :
    (binaryGeometry d n).elements i = BinaryField.decode (fieldExponent d n)
      (fieldExponent_pos d n) (BinaryPolynomial.indexEquiv (fieldExponent d n) i) := rfl

theorem binaryGeometry_rowOrder (d n : ℕ) (i : Fin (rowCount d n)) (j : Fin d) :
    (binaryGeometry d n).rowOrder i j = BinaryField.elements (fieldExponent d n)
      (fieldExponent_pos d n) (finFunctionFinEquiv.symm i j) := rfl

end ExpandingCodes.PolynomialStretch
