import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily

/-! Exact platform definitions are mirrored verbatim under `Definitions/`.
Their source identifiers and SHA-256 hashes are frozen in
`harness/platform/definition-manifest.json`. -/

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

@[simp] theorem neighbors_empty {I J : Type*} [Fintype I] [Fintype J]
    (G : Matrix I J Bit) : neighbors G ∅ = ∅ := by
  classical
  simp [neighbors, QuantumExpander.Decoder.nbhdA]

@[simp] theorem weight_zero {I K : Type*} [Fintype I] [Zero K] :
    weight (0 : I → K) = 0 := by
  classical
  simp [weight]

end ExpandingCodes.PolynomialStretch
