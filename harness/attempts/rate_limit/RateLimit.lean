import Definitions.Def_ExpandingCodes_PolynomialStretch_ErasureModel
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.Indicator

set_option autoImplicit false

open scoped BigOperators Topology Pointwise
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch

/-- The exact integer-floor degree is within `d/q` of its limiting scaled degree. -/
theorem auxiliaryDegree_scaled_bounds (q d : ℕ) (hd : 4 ≤ d) (hq : 2 ≤ q) :
    ((d : ℝ) - 3) / 2 - d / q ≤ (auxiliaryDegree q d : ℝ) / q ∧
      (auxiliaryDegree q d : ℝ) / q ≤ ((d : ℝ) - 3) / 2 := by
  have hd' : (4 : ℤ) ≤ d := by exact_mod_cast hd
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hnum : 0 ≤ ((d : ℤ) - 3) * ((q : ℤ) - 1) - 1 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (d : ℤ) - 4 by omega)
      (show (0 : ℤ) ≤ (q : ℤ) - 2 by omega)]
  have hdiv : 0 ≤ (((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2 :=
    Int.ediv_nonneg hnum (by norm_num)
  have hcast : ((auxiliaryDegree q d : ℕ) : ℤ) =
      (((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2 :=
    Int.toNat_of_nonneg hdiv
  have hupper : 2 * (auxiliaryDegree q d : ℤ) ≤
      ((d : ℤ) - 3) * ((q : ℤ) - 1) - 1 := by rw [hcast]; omega
  have hlower : ((d : ℤ) - 3) * ((q : ℤ) - 1) - 1 <
      2 * (auxiliaryDegree q d : ℤ) + 2 := by rw [hcast]; omega
  have hupper' : 2 * (auxiliaryDegree q d : ℝ) ≤
      ((d : ℝ) - 3) * ((q : ℝ) - 1) - 1 := by exact_mod_cast hupper
  have hlower' : ((d : ℝ) - 3) * ((q : ℝ) - 1) - 1 <
      2 * (auxiliaryDegree q d : ℝ) + 2 := by exact_mod_cast hlower
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  constructor
  · apply (le_div_iff₀ hqR).2
    rw [sub_mul, div_mul_cancel₀ _ hqR.ne']
    nlinarith
  · apply (div_le_iff₀ hqR).2
    nlinarith

/-- The mission's exact integer-floor threshold, with no asymptotic replacement. -/
theorem tendsto_auxiliaryDegree_div (d : ℕ) (hd : 4 ≤ d) :
    Tendsto (fun q : ℕ => (auxiliaryDegree q d : ℝ) / q) atTop
      (𝓝 (((d : ℝ) - 3) / 2)) := by
  have hz : Tendsto (fun q : ℕ => (d : ℝ) / q) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hz) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with q hq
    exact (auxiliaryDegree_scaled_bounds q d hd hq).1
  · filter_upwards [eventually_ge_atTop 2] with q hq
    exact (auxiliaryDegree_scaled_bounds q d hd hq).2

/-- A closed unit cube intersected with a coordinate-sum halfspace. This is a local
analysis interface; at the canonical threshold its volume is exactly `limitingRate`. -/
def cubeHalfspace (d : ℕ) (t : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ t}

theorem cubeHalfspace_eq (d : ℕ) (t : ℝ) :
    cubeHalfspace d t = Icc (fun _ => 0) (fun _ => 1) ∩ {x | ∑ i, x i ≤ t} := by
  ext x
  simp only [cubeHalfspace, mem_ofPred_eq, mem_inter_iff, mem_Icc, Pi.le_def, forall_and]

theorem continuous_coordinateSum (d : ℕ) :
    Continuous (fun x : Fin d → ℝ => ∑ i, x i) := by fun_prop

theorem measurableSet_cubeHalfspace (d : ℕ) (t : ℝ) :
    MeasurableSet (cubeHalfspace d t) := by
  rw [cubeHalfspace_eq]
  exact measurableSet_Icc.inter (isClosed_le (continuous_coordinateSum d) continuous_const).measurableSet

theorem volume_cubeHalfspace_ne_top (d : ℕ) (t : ℝ) :
    volume (cubeHalfspace d t) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (b := 1) (by norm_num)
  calc
    volume (cubeHalfspace d t) ≤ volume (Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1)) :=
      measure_mono (by rw [cubeHalfspace_eq]; exact inter_subset_left)
    _ = 1 := by simp [Real.volume_Icc_pi]

/-- The coordinate-sum hyperplane has zero ambient Lebesgue volume in every positive dimension. -/
theorem volume_coordinateSum_eq_zero (d : ℕ) (hd : 0 < d) (t : ℝ) :
    volume {x : Fin d → ℝ | ∑ i, x i = t} = 0 := by
  let s : AffineSubspace ℝ (Fin d → ℝ) :=
    { carrier := {x | ∑ i, x i = t}
      smul_vsub_vadd_mem' := by
        intro c x y z hx hy hz
        change ∑ i, (c * (x i - y i) + z i) = t
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
        change ∑ i, x i = t at hx
        change ∑ i, y i = t at hy
        change ∑ i, z i = t at hz
        rw [hx, hy, hz]
        ring }
  change volume (s : Set (Fin d → ℝ)) = 0
  apply Measure.addHaar_affineSubspace volume s
  intro hs
  let i : Fin d := ⟨0, hd⟩
  have hx : (Pi.single i (t + 1) : Fin d → ℝ) ∈ s := by rw [hs]; trivial
  change ∑ j, (Pi.single i (t + 1) : Fin d → ℝ) j = t at hx
  simpa [Pi.single_apply] using hx

/-- Moving coordinate-sum halfspaces have continuous volume: the only possible
pointwise discontinuities lie on the zero-volume sum hyperplane. -/
theorem tendsto_volume_cubeHalfspace {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (d : ℕ) (hd : 0 < d) {u : ι → ℝ} {t : ℝ} (hu : Tendsto u l (𝓝 t)) :
    Tendsto (fun a => volume (cubeHalfspace d (u a))) l (𝓝 (volume (cubeHalfspace d t))) := by
  apply tendsto_measure_of_ae_tendsto_indicator l (measurableSet_cubeHalfspace d t)
    (fun a => measurableSet_cubeHalfspace d (u a)) measurableSet_Icc
    (show volume (Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1)) ≠ ⊤ by
      simp [Real.volume_Icc_pi])
    (Eventually.of_forall (fun a => by rw [cubeHalfspace_eq]; exact inter_subset_left))
  filter_upwards [compl_mem_ae_iff.mpr (volume_coordinateSum_eq_zero d hd t)] with x hx
  have hne : ∑ i, x i ≠ t := hx
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · filter_upwards [hu.eventually (lt_mem_nhds hlt)] with a ha
    simp only [cubeHalfspace, mem_ofPred_eq]
    exact and_congr_right (fun _ => iff_of_true ha.le hlt.le)
  · filter_upwards [hu.eventually (gt_mem_nhds hgt)] with a ha
    simp only [cubeHalfspace, mem_ofPred_eq]
    exact and_congr_right (fun _ => iff_of_false (not_le.mpr ha) (not_le.mpr hgt))

theorem continuous_cubeHalfspace_volume (d : ℕ) (hd : 0 < d) :
    Continuous (fun t : ℝ => (volume (cubeHalfspace d t)).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (ENNReal.tendsto_toReal (volume_cubeHalfspace_ne_top d t)).comp
    (tendsto_volume_cubeHalfspace d hd tendsto_id)

theorem limitingRate_eq_cubeHalfspace (d : ℕ) :
    limitingRate d = (volume (cubeHalfspace d (((d : ℝ) - 3) / 2))).toReal := rfl

end ExpandingCodes.PolynomialStretch
