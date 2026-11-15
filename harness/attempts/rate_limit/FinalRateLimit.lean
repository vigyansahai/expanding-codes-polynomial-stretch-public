import ExpandingCodes.Probability.GridVolume
import ExpandingCodes.Algebra.ReedMullerDimension
import ExpandingCodes.Construction.Growth

set_option autoImplicit false

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch

/-- The volume of the mesh union is finite, as it is contained in the closed unit cube. -/
theorem volume_truncatedGrid_ne_top {q d R : ℕ} (hq : 0 < q) :
    volume (truncatedGrid q d R) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (b := 1) (by norm_num)
  calc
    volume (truncatedGrid q d R) ≤ volume (Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1)) :=
      measure_mono (truncatedGrid_subset_closedCube hq)
    _ = 1 := by simp [Real.volume_Icc_pi]

/-- Riemann counting with a moving threshold: whenever the scaled integer degree
converges to `t`, the normalized reduced-monomial count converges to the canonical
Lebesgue volume of the cube cut by `sum ≤ t`. -/
theorem tendsto_gridCount_div (d : ℕ) (hd : 0 < d) (R : ℕ → ℕ) (t : ℝ)
    (hR : Tendsto (fun q : ℕ => (R q : ℝ) / q) atTop (𝓝 t)) :
    Tendsto (fun q : ℕ => (Fintype.card (GridIndices q d (R q)) : ℝ) / (q : ℝ) ^ d)
      atTop (𝓝 ((volume (cubeHalfspace d t)).toReal)) := by
  have hz : Tendsto (fun q : ℕ => (d : ℝ) / q) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun q : ℕ => ((R q : ℝ) + d) / q) atTop (𝓝 t) := by
    simpa only [add_div, add_zero] using hR.add hz
  have hc := continuous_cubeHalfspace_volume d hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hc.continuousAt.tendsto.comp hR) (hc.continuousAt.tendsto.comp hupper)
  · filter_upwards [eventually_gt_atTop 0] with q hq
    rw [← volume_truncatedGrid hq]
    apply ENNReal.toReal_mono (volume_truncatedGrid_ne_top hq)
    rw [← measure_congr (cubeHalfspace_inter_halfOpenCube_ae d ((R q : ℝ) / q))]
    exact measure_mono (cubeHalfspace_inter_halfOpenCube_subset_truncatedGrid hq)
  · filter_upwards [eventually_gt_atTop 0] with q hq
    rw [← volume_truncatedGrid hq]
    exact ENNReal.toReal_mono (volume_cubeHalfspace_ne_top d _)
      (measure_mono (truncatedGrid_subset_cubeHalfspace hq))

/-- Exact natural-alphabet form of the limiting-rate assertion in paper Lemma 2.4. -/
theorem tendsto_auxiliary_monomialCount_div (d : ℕ) (hd : 4 ≤ d) :
    Tendsto (fun q : ℕ =>
      (Fintype.card {a : Fin d → Fin q // ∑ i, (a i).val ≤ auxiliaryDegree q d} : ℝ) /
        (q : ℝ) ^ d) atTop (𝓝 (limitingRate d)) := by
  exact tendsto_gridCount_div d (by omega) (fun q => auxiliaryDegree q d)
    (((d : ℝ) - 3) / 2) (tendsto_auxiliaryDegree_div d hd)

/-- The exact Reed--Muller dimension has the same limit for any family of finite
fields whose cardinalities tend to infinity. -/
theorem tendsto_reedMuller_rate {ι : Type*} {l : Filter ι} (d : ℕ) (hd : 4 ≤ d)
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (hF : Tendsto (fun i => Fintype.card (F i)) l atTop) :
    Tendsto (fun i =>
      (Module.finrank (F i) (reedMuller (F i) d (auxiliaryDegree (Fintype.card (F i)) d)) : ℝ) /
        (Fintype.card (F i) : ℝ) ^ d) l (𝓝 (limitingRate d)) := by
  convert (tendsto_auxiliary_monomialCount_div d hd).comp hF using 1
  funext i
  dsimp only [Function.comp_apply]
  rw [finrank_reedMuller]

/-- The mission's field size tends to infinity at every positive fixed dimension. -/
theorem tendsto_fieldSize_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n => fieldSize d n) atTop atTop := by
  exact tendsto_atTop_mono (fieldSize_lower d) (tendsto_pow_atTop (by omega))

/-- Exact limiting-rate convergence for the mission's arbitrary public geometries. -/
theorem tendsto_auxiliaryCode_rate (d : ℕ) (hd : 4 ≤ d) (g : ∀ n, Geometry d n) :
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount d n) atTop (𝓝 (limitingRate d)) := by
  have hF : Tendsto (fun n => Fintype.card (g n).F) atTop atTop := by
    simpa only [geometry_card] using tendsto_fieldSize_atTop d (by omega)
  convert (tendsto_auxiliary_monomialCount_div d hd).comp hF using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [auxiliaryCode, finrank_reedMuller, rowCount, ← geometry_card (g n), Nat.cast_pow]

end ExpandingCodes.PolynomialStretch
