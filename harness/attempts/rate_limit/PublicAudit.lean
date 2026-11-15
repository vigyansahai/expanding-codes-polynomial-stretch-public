import ExpandingCodes.Probability.RateLimit

set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter
open ExpandingCodes.PolynomialStretch

example (d : ℕ) (hd : 4 ≤ d) :
    Tendsto (fun q : ℕ =>
      (Fintype.card {a : Fin d → Fin q // ∑ i, (a i).val ≤ auxiliaryDegree q d} : ℝ) /
        (q : ℝ) ^ d) atTop (𝓝 (limitingRate d)) :=
  tendsto_auxiliary_monomialCount_div d hd

example (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (g : ∀ n, Geometry (dimension ε) n) :
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount (dimension ε) n) atTop (nhds (limitingRate (dimension ε))) :=
  tendsto_auxiliaryCode_rate (dimension ε) (dimension_ge_four ε hε) g

#print axioms ExpandingCodes.PolynomialStretch.auxiliaryDegree_scaled_bounds
#print axioms ExpandingCodes.PolynomialStretch.tendsto_auxiliaryDegree_div
#print axioms ExpandingCodes.PolynomialStretch.volume_coordinateSum_eq_zero
#print axioms ExpandingCodes.PolynomialStretch.continuous_cubeHalfspace_volume
#print axioms ExpandingCodes.PolynomialStretch.volume_truncatedGrid
#print axioms ExpandingCodes.PolynomialStretch.cubeHalfspace_inter_halfOpenCube_subset_truncatedGrid
#print axioms ExpandingCodes.PolynomialStretch.tendsto_gridCount_div
#print axioms ExpandingCodes.PolynomialStretch.tendsto_auxiliary_monomialCount_div
#print axioms ExpandingCodes.PolynomialStretch.tendsto_reedMuller_rate
#print axioms ExpandingCodes.PolynomialStretch.tendsto_auxiliaryCode_rate

example : (∀ (d : ℕ), 4 ≤ d → Filter.Tendsto (fun q : ℕ => (Fintype.card {a : Fin d → Fin q // ∑ i, (a i).val ≤ ExpandingCodes.PolynomialStretch.auxiliaryDegree q d} : ℝ) / (q : ℝ) ^ d) Filter.atTop (nhds (ExpandingCodes.PolynomialStretch.limitingRate d))) := @ExpandingCodes.PolynomialStretch.tendsto_auxiliary_monomialCount_div

example : (∀ (d : ℕ), 4 ≤ d → ∀ (g : ∀ n : ℕ, ExpandingCodes.PolynomialStretch.Geometry d n), Filter.Tendsto (fun n : ℕ => (Module.finrank (g n).F (ExpandingCodes.PolynomialStretch.auxiliaryCode (g n)) : ℝ) / ExpandingCodes.PolynomialStretch.rowCount d n) Filter.atTop (nhds (ExpandingCodes.PolynomialStretch.limitingRate d))) := @ExpandingCodes.PolynomialStretch.tendsto_auxiliaryCode_rate
