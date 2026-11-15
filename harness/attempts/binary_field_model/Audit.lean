import ExpandingCodes.Computation.BinaryField
import ExpandingCodes.Construction.BinaryGeometry

set_option autoImplicit false

open ExpandingCodes.PolynomialStretch

#print axioms BinaryPolynomial.factorFree_iff_irreducible
#print axioms BinaryPolynomial.modulus_irreducible
#print axioms BinaryField.decode_encode
#print axioms BinaryField.encode_decode
#print axioms BinaryField.multiply_remainder
#print axioms BinaryField.decode_multiply
#print axioms BinaryField.decode_inverse
#print axioms BinaryField.elements_multiplyIndex
#print axioms BinaryField.multiplicationCoefficientBudget_le
#print axioms BinaryField.inverseCoefficientBudget_le
#print axioms binaryGeometry

#eval (BinaryPolynomial.selectedIndex 1 (by decide)).val
#eval (BinaryPolynomial.selectedIndex 2 (by decide)).val
#eval (BinaryPolynomial.selectedIndex 3 (by decide)).val
#eval (BinaryPolynomial.selectedIndex 4 (by decide)).val

#eval (BinaryField.multiplyIndex 3 (by decide)
  (BinaryPolynomial.selectedIndex 3 (by decide))
  (BinaryPolynomial.indexEquiv 3 ⟨2, by decide⟩)
  (BinaryPolynomial.indexEquiv 3 ⟨4, by decide⟩)).val

#eval (BinaryField.inverseIndex 3 (by decide) ⟨2, by decide⟩).val
