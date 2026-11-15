import ExpandingCodes.Algebra.FullEvaluation

set_option autoImplicit false

open ExpandingCodes.Computation

#print axioms Gaussian.rank_correct
#print axioms Gaussian.run_correct
#print axioms Gaussian.run_work_le
#print axioms Gaussian.run_field_operations_le
#print axioms Gaussian.run_array_operations_le
#print axioms ExpandingCodes.PolynomialStretch.fullTestMatrix_rank
#print axioms ExpandingCodes.PolynomialStretch.fullTestTable_rank
#print axioms ExpandingCodes.PolynomialStretch.rationalRankTest_eq

-- Concrete evaluation confirms this is executable data over a decidable field.
-- This matrix requires selecting a pivot away from the initial entry and has
-- rank two (its third row is the sum of the first two).
def sample : Gaussian.Table (ZMod 2) 3 3 :=
  Gaussian.ofMatrix ![![0,1,0], ![1,0,0], ![1,1,0]]

#eval Gaussian.run sample

example : (Gaussian.run sample).1 = 2 := by decide
