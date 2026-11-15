import ExpandingCodes.Probability.AuxiliaryErasure
set_option autoImplicit false

#print axioms ExpandingCodes.PolynomialStretch.pow_reducedPower
#print axioms ExpandingCodes.PolynomialStretch.eval_mem_reedMuller
#print axioms ExpandingCodes.PolynomialStretch.reedMuller_comp_affine_mem
#print axioms ExpandingCodes.PolynomialStretch.erasureExpectation_codeReindex
#print axioms ExpandingCodes.PolynomialStretch.codeReindex_doublyTransitive
#print axioms ExpandingCodes.PolynomialStretch.reedMuller_pair_transitive
#print axioms ExpandingCodes.PolynomialStretch.doublyTransitive_reindexed_auxiliaryCode
#print axioms ExpandingCodes.PolynomialStretch.tendsto_auxiliaryCode_halfErasure

open Filter ExpandingCodes.PolynomialStretch
example (d : ℕ) (hd : 4 ≤ d) (g : ∀ n, Geometry d n)
    (hρ : 0 < limitingRate d ∧ limitingRate d < 1 / 2) :
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount d n) atTop (nhds 0) :=
  tendsto_auxiliaryCode_halfErasure d hd hρ g
