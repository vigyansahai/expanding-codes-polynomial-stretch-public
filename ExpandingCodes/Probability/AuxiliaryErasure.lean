import ExpandingCodes.Algebra.ReedMullerAffine
import ExpandingCodes.Algebra.CodeReindex
import ExpandingCodes.Probability.RateLimit
import ExpandingCodes.Probability.ErasureCapacity

set_option autoImplicit false
open scoped Classical Topology
open Filter

namespace ExpandingCodes.PolynomialStretch

/-- Exact canonical Reed--Muller code, transported to the public row numbering,
has an honest doubly transitive group of code-preserving coordinate permutations. -/
theorem doublyTransitive_reindexed_auxiliaryCode {d n : ℕ} (g : Geometry d n) :
    DoublyTransitiveCode (rowCount d n) (codeReindex g.rowOrder (auxiliaryCode g)) := by
  apply codeReindex_doublyTransitive
  exact reedMuller_pair_transitive

/-- The deterministic row counts tend to infinity at each positive dimension. -/
theorem tendsto_rowCount_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (rowCount d) atTop atTop := by
  exact tendsto_atTop_mono (rowCount_lower d)
    (tendsto_pow_atTop (by have := pow_pos hd 2; omega))

/-- Half-erasure ambiguity is sublinear whenever the exact canonical limiting
rate lies strictly between zero and one half. -/
theorem tendsto_auxiliaryCode_halfErasure (d : ℕ) (hd : 4 ≤ d)
    (hρ : 0 < limitingRate d ∧ limitingRate d < 1 / 2) (g : ∀ n, Geometry d n) :
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount d n) atTop (nhds 0) := by
  let C := fun n => codeReindex (g n).rowOrder (auxiliaryCode (g n))
  have hrate : Tendsto (fun n => (Module.finrank (g n).F (C n) : ℝ) /
      rowCount d n) atTop (nhds (limitingRate d)) := by
    simpa only [C, finrank_codeReindex] using tendsto_auxiliaryCode_rate d hd g
  have hs := erasure_ambiguity (fun n => (g n).F) (rowCount d) C
    (limitingRate d) (1 / 2) ⟨hρ.1, by linarith [hρ.2]⟩
    ⟨by norm_num, by linarith [hρ.2]⟩
    (fun n => doublyTransitive_reindexed_auxiliaryCode (g n))
    (tendsto_rowCount_atTop d (by omega)) hrate
  simpa only [C, erasureExpectation_codeReindex] using hs

end ExpandingCodes.PolynomialStretch
