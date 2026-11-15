import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_ErasureModel

set_option autoImplicit false

/-! Inlined whole module: ExpandingCodes.Construction.Geometry -/
section FlattenModule3



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch















theorem geometry_card {d n : ℕ} (g : Geometry d n) :
    Fintype.card g.F = fieldSize d n := by
  simpa using Fintype.card_congr g.elements.symm























end ExpandingCodes.PolynomialStretch

end FlattenModule3

/-! Inlined whole module: ExpandingCodes.Construction.ParameterBounds -/
section FlattenModule18


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

private theorem parameter_inv_ge_one (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 ≤ ε⁻¹ :=
  (one_le_inv₀ hε.1).2 (by linarith [hε.2])

theorem dimension_ge_four (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    4 ≤ dimension ε := by
  have hi := parameter_inv_ge_one ε hε
  have hs : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by nlinarith
  have hc : (2 : ℝ) ≤ (⌈512 * ε⁻¹ ^ 2⌉₊ : ℝ) :=
    (by nlinarith : (2 : ℝ) ≤ 512 * ε⁻¹ ^ 2).trans (Nat.le_ceil _)
  have hc' : 2 ≤ ⌈512 * ε⁻¹ ^ 2⌉₊ := by exact_mod_cast hc
  unfold dimension
  omega


















































end ExpandingCodes.PolynomialStretch

end FlattenModule18

/-! Inlined whole module: ExpandingCodes.Construction.Growth -/
section FlattenModule19



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

theorem fieldSize_lower (d n : ℕ) : n ^ (2 * d) ≤ fieldSize d n := by
  apply (Nat.le_pow_clog (by decide : 1 < 2) _).trans
  exact Nat.pow_le_pow_right (by decide) (le_max_right 1 _)












theorem rowCount_lower (d n : ℕ) : n ^ (2 * d ^ 2) ≤ rowCount d n := by
  have h := Nat.pow_le_pow_left (fieldSize_lower d n) d
  simpa only [rowCount, ← pow_mul, show 2 * d * d = 2 * d ^ 2 by ring] using h











































end ExpandingCodes.PolynomialStretch

end FlattenModule19

/-! Inlined whole module: ExpandingCodes.Probability.FiniteUniform -/
section FlattenModule20


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_eq_card_filter {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    uniformProb E = ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  classical
  simp [uniformProb, eventProb, ← Finset.sum_filter, div_eq_mul_inv]

theorem uniformProb_eq_card_subtype {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    uniformProb E = (Fintype.card {ω // E ω} : ℝ) / Fintype.card Ω := by
  classical
  rw [uniformProb_eq_card_filter]
  simp only [Fintype.card_subtype]

theorem uniformProb_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (e : Ω ≃ Ξ) (E : Ξ → Prop) :
    uniformProb (fun ω => E (e ω)) = uniformProb E := by
  classical
  rw [uniformProb_eq_card_subtype, uniformProb_eq_card_subtype]
  have ec : {ω // E (e ω)} ≃ {ξ // E ξ} :=
    { toFun := fun ω => ⟨e ω.val, ω.property⟩
      invFun := fun ξ => ⟨e.symm ξ.val, by simpa using ξ.property⟩
      left_inv := fun ω => by ext; simp
      right_inv := fun ξ => by ext; simp }
  rw [Fintype.card_congr ec, Fintype.card_congr e]

theorem uniformProb_congr {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {E D : Ω → Prop} (h : ∀ ω, E ω ↔ D ω) : uniformProb E = uniformProb D := by
  congr 1
  funext ω
  exact propext (h ω)

theorem uniformProb_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProb (fun _ : Ω => True) = 1 := by
  rw [uniformProb_eq_card_filter]
  simp [Fintype.card_ne_zero]

































































end ExpandingCodes.PolynomialStretch

end FlattenModule20

/-! Inlined whole module: ExpandingCodes.Probability.FiniteEvents -/
section FlattenModule27


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {E F : Ω → Prop} (h : ∀ x, E x → F x) : uniformProb E ≤ uniformProb F := by
  classical
  rw [uniformProb_eq_card_filter, uniformProb_eq_card_filter]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show (Finset.univ.filter E) ⊆ Finset.univ.filter F by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h x (Finset.mem_filter.mp hx).2⟩)

theorem uniformProb_exists_finset {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset ι) (E : ι → Ω → Prop) :
    uniformProb (fun x => ∃ i ∈ s, E i x) ≤ ∑ i ∈ s, uniformProb (E i) := by
  classical
  simp_rw [uniformProb_eq_card_filter]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc := Finset.card_biUnion_le (s := s)
    (t := fun i => Finset.univ.filter (E i))
  have hr : ((s.biUnion (fun i => Finset.univ.filter (E i))).card : ℝ) ≤
      ∑ i ∈ s, ((Finset.univ.filter (E i)).card : ℝ) := by exact_mod_cast hc
  convert hr using 1
  · rfl
  · apply congrArg (fun A : Finset Ω => (A.card : ℝ))
    ext x
    simp

end ExpandingCodes.PolynomialStretch

end FlattenModule27

/-! Inlined whole module: ExpandingCodes.Probability.HalfspaceVolume -/
section FlattenModule29





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




end ExpandingCodes.PolynomialStretch

end FlattenModule29

/-! Inlined whole module: ExpandingCodes.Probability.GridVolume -/
section FlattenModule30


set_option autoImplicit false

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch

/-- The exponent vectors being counted; this is `Monomials` with the alphabet
cardinality supplied directly. -/
abbrev GridIndices (q d R : ℕ) := {a : Fin d → Fin q // ∑ i, (a i).val ≤ R}

/-- The half-open mesh box whose lower corner is `a/q`. -/
def gridBox {q d : ℕ} (a : Fin d → Fin q) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico ((a i).val / (q : ℝ)) (((a i).val + 1) / (q : ℝ)))

/-- The union of mesh boxes indexed by the allowed exponent vectors. -/
def truncatedGrid (q d R : ℕ) : Set (Fin d → ℝ) :=
  ⋃ a : GridIndices q d R, gridBox a.val

/-- The half-open cube used to partition the canonical closed unit cube. -/
def halfOpenCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)

theorem measurableSet_gridBox {q d : ℕ} (a : Fin d → Fin q) :
    MeasurableSet (gridBox a) := MeasurableSet.univ_pi (fun _ => measurableSet_Ico)





theorem mem_gridBox_scaled {q d : ℕ} (hq : 0 < q) (a : Fin d → Fin q)
    (x : Fin d → ℝ) :
    x ∈ gridBox a ↔ ∀ i, ((a i).val : ℝ) ≤ q * x i ∧ q * x i < (a i).val + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [gridBox, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico]
  constructor
  · intro hx i
    have hi := hx i
    exact ⟨by nlinarith [(div_le_iff₀ hqR).mp hi.1],
      by nlinarith [(lt_div_iff₀ hqR).mp hi.2]⟩
  · intro hx i
    have hi := hx i
    exact ⟨(div_le_iff₀ hqR).mpr (by nlinarith),
      (lt_div_iff₀ hqR).mpr (by nlinarith)⟩

theorem pairwiseDisjoint_gridBox {q d : ℕ} (hq : 0 < q) :
    Pairwise (fun a b : Fin d → Fin q => Disjoint (gridBox a) (gridBox b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  apply hab
  funext i
  apply Fin.ext
  have ha := (mem_gridBox_scaled hq a x).mp hxa i
  have hb := (mem_gridBox_scaled hq b x).mp hxb i
  have hn : 0 ≤ (q : ℝ) * x i := (Nat.cast_nonneg (a i).val).trans ha.1
  exact ((Nat.floor_eq_iff hn).mpr ha).symm.trans ((Nat.floor_eq_iff hn).mpr hb)

theorem gridBox_subset_halfOpenCube {q d : ℕ} (hq : 0 < q) (a : Fin d → Fin q) :
    gridBox a ⊆ halfOpenCube d := by
  intro x hx
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hx' := (mem_gridBox_scaled hq a x).mp hx
  simp only [halfOpenCube, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico]
  intro i
  have hi := hx' i
  have hai : ((a i).val : ℝ) + 1 ≤ q := by exact_mod_cast (a i).isLt
  constructor
  · have hz : (0 : ℝ) ≤ (a i).val := Nat.cast_nonneg _
    nlinarith
  · nlinarith

theorem halfOpenCube_subset_closedCube (d : ℕ) :
    halfOpenCube d ⊆ Set.Icc (fun _ => 0) (fun _ => 1) := by
  intro x hx
  simp only [halfOpenCube, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico] at hx
  exact ⟨fun i => (hx i).1, fun i => (hx i).2.le⟩

theorem truncatedGrid_subset_closedCube {q d R : ℕ} (hq : 0 < q) :
    truncatedGrid q d R ⊆ Set.Icc (fun _ => 0) (fun _ => 1) := by
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  exact halfOpenCube_subset_closedCube d (gridBox_subset_halfOpenCube hq a.val ha)

theorem volume_gridBox {q d : ℕ} (a : Fin d → Fin q) :
    volume (gridBox a) = ENNReal.ofReal (1 / (q : ℝ)) ^ d := by
  simp only [gridBox, Real.volume_pi_Ico]
  have h : ∀ i : Fin d, (((a i).val : ℝ) + 1) / q - (a i).val / q = 1 / (q : ℝ) :=
    fun _ => by ring
  simp_rw [h]
  simp

/-- Exact finite count divided by mesh denominator, as actual Lebesgue volume. -/
theorem volume_truncatedGrid {q d R : ℕ} (hq : 0 < q) :
    (volume (truncatedGrid q d R)).toReal = (Fintype.card (GridIndices q d R) : ℝ) / q ^ d := by
  have hdisj : Pairwise (fun a b : GridIndices q d R => Disjoint (gridBox a.val) (gridBox b.val)) := by
    intro a b hab
    exact pairwiseDisjoint_gridBox hq (fun h => hab (Subtype.ext h))
  rw [truncatedGrid, measure_iUnion hdisj (fun a => measurableSet_gridBox a.val), tsum_fintype]
  simp only [volume_gridBox, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp [div_eq_mul_inv]

/-- Every selected mesh box lies below the threshold enlarged by one mesh per coordinate. -/
theorem truncatedGrid_subset_cubeHalfspace {q d R : ℕ} (hq : 0 < q) :
    truncatedGrid q d R ⊆ cubeHalfspace d (((R : ℝ) + d) / q) := by
  intro x hx
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  have hclosed := halfOpenCube_subset_closedCube d (gridBox_subset_halfOpenCube hq a.val ha)
  refine ⟨fun i => ⟨hclosed.1 i, hclosed.2 i⟩, (le_div_iff₀ hqR).mpr ?_⟩
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    ((mem_gridBox_scaled hq a.val x).mp ha i).2.le)
  have hR : (∑ i, ((a.val i).val : ℝ)) ≤ R := by exact_mod_cast a.property
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  nlinarith

/-- Floors supply the mesh box containing each point of the half-open cube. -/
theorem cubeHalfspace_inter_halfOpenCube_subset_truncatedGrid {q d R : ℕ} (hq : 0 < q) :
    cubeHalfspace d ((R : ℝ) / q) ∩ halfOpenCube d ⊆ truncatedGrid q d R := by
  intro x hx
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxC := hx.2
  simp only [halfOpenCube, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico] at hxC
  have hnonneg : ∀ i, 0 ≤ (q : ℝ) * x i := fun i => mul_nonneg hqR.le (hxC i).1
  let a : Fin d → Fin q := fun i => ⟨⌊(q : ℝ) * x i⌋₊,
    (Nat.floor_lt (hnonneg i)).mpr (by nlinarith [(hxC i).2])⟩
  have ha : ∑ i, (a i).val ≤ R := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      Nat.floor_le (hnonneg i))
    have hsum : (q : ℝ) * ∑ i, x i ≤ R := by
      have hh := (le_div_iff₀ hqR).mp hx.1.2
      nlinarith
    have ht : (∑ i, ((a i).val : ℝ)) ≤ R := by
      change (∑ i, (⌊(q : ℝ) * x i⌋₊ : ℝ)) ≤ R
      simpa only [← Finset.mul_sum] using hs.trans (by simpa only [Finset.mul_sum] using hsum)
    exact_mod_cast ht
  apply Set.mem_iUnion.mpr
  refine ⟨⟨a, ha⟩, (mem_gridBox_scaled hq a x).mpr (fun i => ?_)⟩
  exact ⟨Nat.floor_le (hnonneg i), Nat.lt_floor_add_one _⟩

/-- Removing the upper cube faces does not change any halfspace volume. -/
theorem cubeHalfspace_inter_halfOpenCube_ae (d : ℕ) (t : ℝ) :
    (cubeHalfspace d t ∩ halfOpenCube d : Set (Fin d → ℝ)) =ᵐ[volume] cubeHalfspace d t := by
  have hC : halfOpenCube d =ᵐ[volume] Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
    simpa only [halfOpenCube, volume_pi] using
      (Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
        (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ)))
  filter_upwards [hC] with x hx
  apply propext
  change (x ∈ cubeHalfspace d t ∧ x ∈ halfOpenCube d) ↔ x ∈ cubeHalfspace d t
  constructor
  · exact And.left
  · intro h
    exact ⟨h, (Iff.of_eq hx).mpr (by rw [cubeHalfspace_eq] at h; exact h.1)⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule30

/-! Inlined whole module: ExpandingCodes.Algebra.ReedMullerDimension -/
section FlattenModule31



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

universe u

/-- Finite-variable evaluation injectivity, including fields in arbitrary universes.
The lift only aligns the two universe parameters of Mathlib's finite-field theorem. -/
theorem eq_zero_of_eval_eq_zero_fin {F : Type u} [Field F] [Fintype F] {d : ℕ}
    (p : MvPolynomial (Fin d) F)
    (h : ∀ z : Fin d → F, MvPolynomial.eval z p = 0)
    (hp : p ∈ MvPolynomial.restrictDegree (Fin d) F (Fintype.card F - 1)) : p = 0 := by
  classical
  have hrename : MvPolynomial.rename (ULift.up : Fin d → ULift.{u} (Fin d)) p = 0 := by
    apply MvPolynomial.eq_zero_of_eval_eq_zero (ULift.{u} (Fin d)) F
    · intro z
      rw [MvPolynomial.eval_rename]
      exact h _
    · rw [MvPolynomial.mem_restrictDegree_iff_sup]
      intro i
      obtain ⟨i⟩ := i
      rw [← MvPolynomial.degreeOf_def,
        MvPolynomial.degreeOf_rename_of_injective ULift.up_injective]
      simpa only [MvPolynomial.degreeOf_def] using
        (MvPolynomial.mem_restrictDegree_iff_sup _ _ _).mp hp i
  apply MvPolynomial.rename_injective (ULift.up : Fin d → ULift.{u} (Fin d))
    ULift.up_injective
  simpa only [map_zero] using hrename

/-- The exponent vector of an exact canonical monomial, as a finitely supported function. -/
noncomputable def reducedMonomialExponent {F : Type*} [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a.val i).val)





theorem reducedMonomialExponent_injective {F : Type*} [Fintype F] {d R : ℕ} :
    Function.Injective (reducedMonomialExponent (F := F) (d := d) (R := R)) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun e : Fin d →₀ ℕ => e i) h

/-- A polynomial representative of each exact canonical monomial row. -/
noncomputable def reducedMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : MvPolynomial (Fin d) F :=
  MvPolynomial.monomial (reducedMonomialExponent a) 1

theorem eval_reducedMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (z : Fin d → F) :
    MvPolynomial.eval z (reducedMonomialPolynomial a) = monomialEval a z := by
  rw [reducedMonomialPolynomial, MvPolynomial.eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem reducedMonomialPolynomial_mem_restrictDegree {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (a : Monomials F d R) :
    reducedMonomialPolynomial a ∈
      MvPolynomial.restrictDegree (Fin d) F (Fintype.card F - 1) := by
  rw [MvPolynomial.mem_restrictDegree]
  intro b hb i
  have hba : b = reducedMonomialExponent a := by
    simpa [reducedMonomialPolynomial, MvPolynomial.support_monomial] using hb
  subst b
  exact Nat.le_sub_one_of_lt (a.val i).isLt

theorem linearIndependent_reducedMonomialPolynomial {F : Type*} [Field F] [Fintype F]
    (d R : ℕ) :
    LinearIndependent F (reducedMonomialPolynomial (F := F) (d := d) (R := R)) := by
  exact (MvPolynomial.basisMonomials (Fin d) F).linearIndependent.comp
    (reducedMonomialExponent (F := F) (d := d) (R := R))
    reducedMonomialExponent_injective

/-- Reduced monomials remain independent after evaluation on every point of the finite field. -/
theorem linearIndependent_monomialEval {F : Type*} [Field F] [Fintype F] (d R : ℕ) :
    LinearIndependent F (monomialEval (F := F) (d := d) (R := R)) := by
  have hspan : Submodule.span F
      (Set.range (reducedMonomialPolynomial (F := F) (d := d) (R := R))) ≤
      MvPolynomial.restrictDegree (Fin d) F (Fintype.card F - 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact reducedMonomialPolynomial_mem_restrictDegree a
  have hinj : Set.InjOn (MvPolynomial.evalₗ F (Fin d))
      (Submodule.span F
        (Set.range (reducedMonomialPolynomial (F := F) (d := d) (R := R)))) := by
    intro p hp q hq hpq
    apply sub_eq_zero.mp
    apply eq_zero_of_eval_eq_zero_fin (p - q)
    · intro z
      simpa only [map_sub, sub_eq_zero, MvPolynomial.evalₗ_apply] using congrFun hpq z
    · exact Submodule.sub_mem _ (hspan hp) (hspan hq)
  have h := (linearIndependent_reducedMonomialPolynomial (F := F) d R).map_injOn
    (MvPolynomial.evalₗ F (Fin d)) hinj
  have heval : (MvPolynomial.evalₗ F (Fin d)) ∘
      (reducedMonomialPolynomial (F := F) (d := d) (R := R)) =
      monomialEval (F := F) (d := d) (R := R) := by
    funext a z
    exact eval_reducedMonomialPolynomial a z
  rwa [heval] at h

/-- The exact Reed--Muller code dimension is the number of canonical reduced monomials. -/
theorem finrank_reedMuller {F : Type*} [Field F] [Fintype F] (d R : ℕ) :
    Module.finrank F (reedMuller F d R) = Fintype.card (Monomials F d R) := by
  exact finrank_span_eq_card (linearIndependent_monomialEval (F := F) d R)

end ExpandingCodes.PolynomialStretch

end FlattenModule31

/-! Inlined whole module: ExpandingCodes.Probability.RateLimit -/
section FlattenModule32




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

end FlattenModule32

/-! Inlined whole module: ExpandingCodes.Probability.BinomialAtom -/
section FlattenModule41




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

theorem centralBinom_sq_bound (s : ℕ) :
    Nat.centralBinom s ^ 2 * (2 * s + 1) ≤ 16 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hr := Nat.succ_mul_centralBinom_succ s
    have he : Nat.centralBinom (s + 1) ^ 2 * (s + 1) ^ 2 =
        4 * (2 * s + 1) ^ 2 * Nat.centralBinom s ^ 2 := by
      nlinarith [congrArg (fun x : ℕ => x ^ 2) hr]
    have hc : 4 * (2 * s + 1) * (2 * s + 3) ≤ 16 * (s + 1) ^ 2 := by
      nlinarith
    have hb := Nat.mul_le_mul_right (4 * (2 * s + 1) * (2 * s + 3)) ih
    have hb' := Nat.mul_le_mul_right (16 ^ s) hc
    have hh : (Nat.centralBinom (s + 1) ^ 2 * (2 * (s + 1) + 1)) * (s + 1) ^ 2 ≤
        (16 ^ (s + 1)) * (s + 1) ^ 2 := by
      calc
        _ = 4 * (2 * s + 1) * (2 * s + 3) *
            (Nat.centralBinom s ^ 2 * (2 * s + 1)) := by nlinarith [he]
        _ ≤ 4 * (2 * s + 1) * (2 * s + 3) * 16 ^ s := by nlinarith [hb]
        _ ≤ 16 * (s + 1) ^ 2 * 16 ^ s := hb'
        _ = _ := by rw [pow_succ]; ring
    exact (mul_le_mul_iff_left₀ (by positivity : 0 < (s + 1) ^ 2)).mp hh

theorem binomial_atom_le (s j : ℕ) :
    ((2 * s).choose j : ℝ) / 4 ^ s ≤ 1 / Real.sqrt (2 * s + 1) := by
  have hnat := centralBinom_sq_bound s
  have hsq : (Nat.centralBinom s : ℝ) ^ 2 * (2 * s + 1) ≤ (4 ^ s : ℝ) ^ 2 := by
    have h : (Nat.centralBinom s : ℝ) ^ 2 * (2 * s + 1) ≤ (16 : ℝ) ^ s := by
      exact_mod_cast hnat
    convert h using 1
    rw [← pow_mul, mul_comm s 2, pow_mul]
    norm_num
  have hroot : 0 < Real.sqrt (2 * (s : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hc : (Nat.centralBinom s : ℝ) * Real.sqrt (2 * s + 1) ≤ 4 ^ s := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * (s : ℝ) + 1 by positivity),
      show 0 ≤ (Nat.centralBinom s : ℝ) by positivity,
      show 0 < (4 : ℝ) ^ s by positivity]
  have hchoose : ((2 * s).choose j : ℝ) ≤ Nat.centralBinom s := by
    exact_mod_cast Nat.choose_le_centralBinom j s
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ s)).2
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ hroot).2
  calc
    ((2 * s).choose j : ℝ) * Real.sqrt (2 * s + 1) ≤
        (Nat.centralBinom s : ℝ) * Real.sqrt (2 * s + 1) := mul_le_mul_of_nonneg_right hchoose hroot.le
    _ ≤ 4 ^ s := hc

end ExpandingCodes.PolynomialStretch

end FlattenModule41

/-! Inlined whole module: ExpandingCodes.Probability.BinomialInterval -/
section FlattenModule42



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

noncomputable def trueSet {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i = true)

noncomputable def boolFinsetEquiv (d : ℕ) : (Fin d → Bool) ≃ Finset (Fin d) where
  toFun := trueSet
  invFun S i := decide (i ∈ S)
  left_inv x := by
    funext i
    simp [trueSet]
  right_inv S := by
    ext i
    simp [trueSet]

theorem card_trueSet_eq (d j : ℕ) [Fintype {x : Fin d → Bool // (trueSet x).card = j}] :
    Fintype.card {x : Fin d → Bool // (trueSet x).card = j} = d.choose j := by
  classical
  let e : {x : Fin d → Bool // (trueSet x).card = j} ≃
      {S : Finset (Fin d) // S.card = j} :=
    (boolFinsetEquiv d).subtypeEquiv (fun _ => Iff.rfl)
  have h := Fintype.card_congr e
  simpa only [Fintype.card_finset_len, Fintype.card_fin] using h

theorem uniformProb_trueSet_card_le (s j : ℕ) :
    uniformProb (fun x : Fin (2*s) → Bool => (trueSet x).card = j) ≤
      1 / Real.sqrt (2 * s + 1) := by
  rw [uniformProb_eq_card_subtype, card_trueSet_eq]
  have he : Fintype.card (Fin (2*s) → Bool) = 4 ^ s := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [pow_mul]
    rfl
  rw [he, Nat.cast_pow, Nat.cast_ofNat]
  exact binomial_atom_le s j

theorem uniformProb_trueSet_interval_le (s : ℕ) (a : ℝ) :
    uniformProb (fun x : Fin (2*s) → Bool =>
      a ≤ ((trueSet x).card : ℝ) ∧ ((trueSet x).card : ℝ) ≤ a + 3) ≤
        4 / Real.sqrt (2 * s + 1) := by
  classical
  let T := Finset.Icc ⌈a⌉₊ (⌈a⌉₊ + 3)
  have hin (x : Fin (2*s) → Bool)
      (hx : a ≤ ((trueSet x).card : ℝ) ∧ ((trueSet x).card : ℝ) ≤ a + 3) :
      (trueSet x).card ∈ T := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Nat.ceil_le).2 hx.1
    · have h : ((trueSet x).card : ℝ) ≤ (⌈a⌉₊ : ℝ) + 3 := by
        linarith [Nat.le_ceil a]
      exact_mod_cast h
  calc
    _ ≤ uniformProb (fun x : Fin (2*s) → Bool => ∃ j ∈ T, (trueSet x).card = j) :=
      uniformProb_mono (fun x hx => ⟨_, hin x hx, rfl⟩)
    _ ≤ ∑ j ∈ T, uniformProb (fun x : Fin (2*s) → Bool => (trueSet x).card = j) :=
      uniformProb_exists_finset T _
    _ ≤ ∑ _j ∈ T, 1 / Real.sqrt (2 * s + 1) :=
      Finset.sum_le_sum (fun j _ => uniformProb_trueSet_card_le s j)
    _ = _ := by
      have hc : T.card = 4 := by simp only [T, Nat.card_Icc]; omega
      simp [hc]
      ring

end ExpandingCodes.PolynomialStretch

end FlattenModule42

/-! Inlined whole module: ExpandingCodes.Probability.BoundedDifferences -/
section FlattenModule43



/-!
# Sharp finite bounded differences on the uniform Boolean cube

The probability in the final theorem is the mission's canonical `uniformProb`.
`uniformMean` and `HasUnitBoundedDifferences` are local helper interfaces. The
proof uses exact finite sums, splits coordinates by `Fin.consEquiv`, and proves
the centered MGF bound by induction. The two-point estimate is Mathlib's
`Real.cosh_le_exp_half_sq`; finite exponential Markov and optimization give the
sharp exponent `-2 * t^2 / m`. No measure-theoretic martingale is required.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace ExpandingCodes.PolynomialStretch

/-- Exact expectation under the uniform law on a nonempty finite space. -/
noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

section Mean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

@[simp] theorem uniformMean_const (c : ℝ) : uniformMean (fun _ : Ω => c) = c := by
  simp [uniformMean, Fintype.card_ne_zero]

theorem uniformMean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

omit [Nonempty Ω] in
theorem uniformMean_add (f g : Ω → ℝ) :
    uniformMean (fun x => f x + g x) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]


















/-- Bridge to the mission's canonical finite uniform probability. -/
theorem uniformProb_eq_uniformMean (E : Ω → Prop) :
    uniformProb E = uniformMean (fun x => if E x then 1 else 0) := by
  classical
  unfold uniformProb eventProb uniformMean
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

end Mean







































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule43

/-! Inlined whole module: ExpandingCodes.Probability.GridBand -/
section FlattenModule44



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_prod (α β : Type*) [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α × β → Prop) :
    uniformProb E = uniformMean (fun b => uniformProb (fun a => E (a, b))) := by
  classical
  simp_rw [uniformProb_eq_uniformMean]
  unfold uniformMean
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div]
  ring

noncomputable def gridBitEquiv (d q : ℕ) :
    ((Fin d → Bool) × (Fin d → Fin q)) ≃ (Fin d → Fin (2 * q)) :=
  (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => Bool) (fun _ => Fin q)).symm.trans
    (Equiv.piCongrRight (fun _ =>
      (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin q))).trans finProdFinEquiv))

theorem gridBitEquiv_sum (d q : ℕ) (x : Fin d → Bool) (z : Fin d → Fin q) :
    (∑ i, ((gridBitEquiv d q (x,z) i).val : ℝ)) =
      (q : ℝ) * (trueSet x).card + ∑ i, ((z i).val : ℝ) := by
  classical
  have he (i : Fin d) : ((gridBitEquiv d q (x,z) i).val : ℝ) =
      ((z i).val : ℝ) + (q : ℝ) * (if x i then 1 else 0) := by
    cases hx : x i <;> simp [gridBitEquiv, finProdFinEquiv, finTwoEquiv, hx]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc : (∑ i : Fin d, if x i then (1 : ℝ) else 0) = (trueSet x).card := by
    simp [trueSet, Finset.sum_boole]
  rw [hc]
  ring

theorem gridBand_prob_le (s q : ℕ) [NeZero q] (hq : 0 < q) (A D : ℝ) (hAD : D - A ≤ 3 * q) :
    uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      A ≤ ∑ i, ((v i).val : ℝ) ∧ (∑ i, ((v i).val : ℝ)) ≤ D) ≤
        4 / Real.sqrt (2 * s + 1) := by
  classical
  let E : (Fin (2*s) → Fin (2*q)) → Prop := fun v =>
    A ≤ ∑ i, ((v i).val : ℝ) ∧ (∑ i, ((v i).val : ℝ)) ≤ D
  change uniformProb E ≤ _
  rw [← uniformProb_equiv (gridBitEquiv (2*s) q) E,
    uniformProb_prod]
  apply (uniformMean_mono (fun z => ?_)).trans_eq (uniformMean_const _)
  let a := (A - ∑ i, ((z i).val : ℝ)) / (q : ℝ)
  calc
    uniformProb (fun x => E (gridBitEquiv (2*s) q (x,z))) ≤
        uniformProb (fun x : Fin (2*s) → Bool =>
          a ≤ ((trueSet x).card : ℝ) ∧ ((trueSet x).card : ℝ) ≤ a + 3) := by
      apply uniformProb_mono
      intro x hx
      change A ≤ ∑ i, ((gridBitEquiv (2*s) q (x,z) i).val : ℝ) ∧
        (∑ i, ((gridBitEquiv (2*s) q (x,z) i).val : ℝ)) ≤ D at hx
      rw [gridBitEquiv_sum] at hx
      have hqp : (0 : ℝ) < q := by exact_mod_cast hq
      constructor
      · apply (div_le_iff₀ hqp).2
        nlinarith
      · have hh : ((trueSet x).card : ℝ) - 3 ≤
            (A - ∑ i, ((z i).val : ℝ)) / (q : ℝ) := by
          apply (le_div_iff₀ hqp).2
          nlinarith
        dsimp [a]
        linarith
    _ ≤ _ := uniformProb_trueSet_interval_le s a

end ExpandingCodes.PolynomialStretch

end FlattenModule44

/-! Inlined whole module: ExpandingCodes.Algebra.PolynomialSum -/
section FlattenModule109





/-!
Finite-field polynomial summation used in the proof of paper Lemma 2.2.
These interfaces are local and provisional, not the unavailable mission preamble.
-/

set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] [DecidableEq σ]

































































end ExpandingCodes

end FlattenModule109

/-! Inlined whole module: ExpandingCodes.Algebra.FlatIndicator -/
section FlattenModule110



/-!
Polynomial indicators for finite families of affine equations, including the
three equations defining a preliminary generator column in paper Section 2.1.
These interfaces are local and provisional, not platform-canonical statements.
-/

set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ ι : Type*} [Field K]

/-- A polynomial representation of a scalar affine form. -/
noncomputable def affinePolynomial [Fintype σ] (coefficients : σ → K) (constant : K) :
    MvPolynomial σ K :=
  MvPolynomial.C constant + ∑ i, MvPolynomial.C (coefficients i) * MvPolynomial.X i

theorem eval_affinePolynomial [Fintype σ] (coefficients : σ → K) (constant : K)
    (x : σ → K) :
    MvPolynomial.eval x (affinePolynomial coefficients constant) =
      constant + ∑ i, coefficients i * x i := by
  simp [affinePolynomial]

theorem totalDegree_affinePolynomial_le [Fintype σ]
    (coefficients : σ → K) (constant : K) :
    (affinePolynomial coefficients constant).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

variable [Fintype K]










































































end ExpandingCodes

end FlattenModule110

/-! Inlined whole module: ExpandingCodes.Probability.RateDiscrete -/
section FlattenModule116



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_or_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E F : Ω → Prop) :
    uniformProb (fun x => E x ∨ F x) ≤ uniformProb E + uniformProb F := by
  classical
  rw [uniformProb_eq_uniformMean, uniformProb_eq_uniformMean,
    uniformProb_eq_uniformMean, ← uniformMean_add]
  apply uniformMean_mono
  intro x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf]

noncomputable def gridReflect (d q : ℕ) : Equiv.Perm (Fin d → Fin q) :=
  Equiv.piCongrRight (fun _ => Fin.revPerm)

theorem gridReflect_sum (d q : ℕ) (v : Fin d → Fin q) :
    (∑ i, (((gridReflect d q v) i).val : ℝ)) + (∑ i, ((v i).val : ℝ)) =
      (d : ℝ) * (q - 1 : ℕ) := by
  classical
  rw [← Finset.sum_add_distrib]
  have hc (i : Fin d) : (((gridReflect d q v) i).val : ℝ) + ((v i).val : ℝ) =
      (q - 1 : ℕ) := by
    have hv := (v i).isLt
    have hh : (Fin.rev (v i)).val + (v i).val = q - 1 := by
      rw [Fin.val_rev]
      omega
    exact_mod_cast hh
  simp_rw [hc]
  simp

theorem grid_median_prob_ge_half (s q : ℕ) [NeZero q] :
    1 / 2 ≤ uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      (∑ i, ((v i).val : ℝ)) ≤ (s * (2*q-1) : ℕ)) := by
  classical
  let D : ℝ := (s * (2*q-1) : ℕ)
  let E : (Fin (2*s) → Fin (2*q)) → Prop := fun v => (∑ i, ((v i).val : ℝ)) ≤ D
  let F : (Fin (2*s) → Fin (2*q)) → Prop := fun v => D ≤ ∑ i, ((v i).val : ℝ)
  have heq : uniformProb E = uniformProb F := by
    rw [← uniformProb_equiv (gridReflect (2*s) (2*q)) E]
    apply uniformProb_congr
    intro v
    have hh := gridReflect_sum (2*s) (2*q) v
    have hd : ((2*s : ℕ) : ℝ) * (2*q-1 : ℕ) = 2*D := by
      dsimp [D]
      push_cast
      ring
    rw [hd] at hh
    dsimp [E, F]
    constructor <;> intro h <;> linarith
  have hu : uniformProb (fun v => E v ∨ F v) = 1 := by
    have hh : (fun v => E v ∨ F v) = (fun _ => True) := by
      funext v
      apply propext
      exact iff_true_intro (le_total _ _)
    rw [hh, uniformProb_true]
  have hb := uniformProb_or_le E F
  rw [hu] at hb
  change 1 / 2 ≤ uniformProb E
  linarith

/-- For even dimension and alphabet, the exact floor leaves a band shorter
than three half-alphabet steps below the discrete median. -/
theorem auxiliaryDegree_even_band (s q : ℕ) (hs : 2 ≤ s) (hq : 1 ≤ q) :
    ((s * (2*q-1) : ℕ) : ℝ) - auxiliaryDegree (2*q) (2*s) ≤ 3 * (q : ℝ) := by
  have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hp : 0 ≤ ((2*(s : ℤ)-3) * q - s + 1) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ s-2 by omega)
      (show (0 : ℤ) ≤ q-1 by omega)]
  have he : auxiliaryDegree (2*q) (2*s) =
      ((2*(s : ℤ)-3) * q - s + 1).toNat := by
    unfold auxiliaryDegree
    push_cast
    congr 1
    have hh : ((2*(s : ℤ)-3) * (2*(q : ℤ)-1) - 1) =
        2 * ((2*(s : ℤ)-3) * q - s + 1) := by ring
    rw [hh, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
  have hc : (auxiliaryDegree (2*q) (2*s) : ℤ) =
      (2*(s : ℤ)-3) * q - s + 1 := by rw [he, Int.toNat_of_nonneg hp]
  have hsub : ((2*q-1 : ℕ) : ℤ) = 2*(q : ℤ)-1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hb : ((s*(2*q-1) : ℕ) : ℤ) - auxiliaryDegree (2*q) (2*s) ≤ 3*q := by
    rw [Nat.cast_mul, hsub, hc]
    nlinarith
  exact_mod_cast hb

theorem auxiliary_grid_rate_ge (s q : ℕ) [NeZero q] (hs : 2 ≤ s) :
    1 / 2 - 4 / Real.sqrt (2*s+1) ≤
      (Fintype.card (GridIndices (2*q) (2*s) (auxiliaryDegree (2*q) (2*s))) : ℝ) /
        ((2*q : ℕ) : ℝ) ^ (2*s) := by
  classical
  let R := auxiliaryDegree (2*q) (2*s)
  let D := s * (2*q-1)
  let E : (Fin (2*s) → Fin (2*q)) → Prop := fun v => (∑ i, (v i).val) ≤ R
  let F : (Fin (2*s) → Fin (2*q)) → Prop := fun v =>
    (R : ℝ) ≤ ∑ i, ((v i).val : ℝ) ∧ (∑ i, ((v i).val : ℝ)) ≤ D
  have hband : uniformProb F ≤ 4 / Real.sqrt (2*s+1) :=
    gridBand_prob_le s q (NeZero.pos q) R D
      (auxiliaryDegree_even_band s q hs (NeZero.pos q))
  have hmid : 1 / 2 ≤ uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      (∑ i, ((v i).val : ℝ)) ≤ (D : ℝ)) := grid_median_prob_ge_half s q
  have hsub : uniformProb (fun v : Fin (2*s) → Fin (2*q) =>
      (∑ i, ((v i).val : ℝ)) ≤ (D : ℝ)) ≤ uniformProb E + uniformProb F := by
    apply (uniformProb_mono (F := fun v => E v ∨ F v) ?_).trans (uniformProb_or_le E F)
    intro v hv
    by_cases he : E v
    · exact Or.inl he
    · right
      dsimp [E] at he
      have hh : (R : ℝ) ≤ ∑ i, ((v i).val : ℝ) := by
        have hn : R ≤ ∑ i, (v i).val := by omega
        exact_mod_cast hn
      exact ⟨hh, hv⟩
  have he : uniformProb E =
      (Fintype.card (GridIndices (2*q) (2*s) R) : ℝ) / ((2*q : ℕ) : ℝ) ^ (2*s) := by
    rw [uniformProb_eq_card_subtype]
    simp only [GridIndices, E, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    congr 1
    norm_cast
    congr 1
    exact Subsingleton.elim _ _
  rw [he] at hsub
  dsimp only [R] at hsub
  linarith

end ExpandingCodes.PolynomialStretch

end FlattenModule116

/-! Inlined whole module: ExpandingCodes.Probability.RateNumerical -/
section FlattenModule117



set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem limitingRate_lower_even (s : ℕ) (hs : 2 ≤ s) :
    1 / 2 - 4 / Real.sqrt (2*s+1) ≤ limitingRate (2*s) := by
  have hq : Tendsto (fun q : ℕ => 2*(q+1)) atTop atTop :=
    tendsto_atTop_mono (fun q => by change q ≤ 2*(q+1); omega) tendsto_id
  have hl : Tendsto (fun q : ℕ =>
      (Fintype.card (GridIndices (2*(q+1)) (2*s)
        (auxiliaryDegree (2*(q+1)) (2*s))) : ℝ) /
          ((2*(q+1) : ℕ) : ℝ) ^ (2*s)) atTop (𝓝 (limitingRate (2*s))) := by
    simpa only [Function.comp_def, GridIndices] using
      (tendsto_auxiliary_monomialCount_div (2*s) (by omega)).comp hq
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  apply Eventually.of_forall
  intro q
  exact auxiliary_grid_rate_ge s (q+1) hs

theorem dimension_lower_bound (ε : ℝ) :
    1024 * ε⁻¹ ^ 2 ≤ (dimension ε : ℝ) := by
  have hc : 512 * ε⁻¹ ^ 2 ≤ (⌈512 * ε⁻¹ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  unfold dimension
  push_cast
  linarith

theorem rate_atom_bound_parameter (ε : ℝ) (hε : 0 < ε) :
    4 / Real.sqrt ((dimension ε : ℝ)+1) ≤ ε / 8 := by
  have hd := dimension_lower_bound ε
  have ht : 0 < Real.sqrt ((dimension ε : ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ (dimension ε : ℝ)+1 by positivity)
  have hdiv : (32 / ε : ℝ) ^ 2 = 1024 * ε⁻¹ ^ 2 := by
    rw [div_eq_mul_inv, mul_pow]
    norm_num
  have hr : (32 : ℝ) / ε ≤ Real.sqrt ((dimension ε : ℝ)+1) := by
    have hp : (0 : ℝ) < 32 / ε := by positivity
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hr hε.le
  rw [div_mul_cancel₀ _ hε.ne'] at hm
  apply (div_le_iff₀ ht).2
  nlinarith

theorem limitingRate_lower_parameter (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) := by
  let s := ⌈512 * ε⁻¹ ^ 2⌉₊
  have hs : 2 ≤ s := by
    have hd := dimension_ge_four ε hε
    unfold dimension at hd
    dsimp [s]
    omega
  have hl := limitingRate_lower_even s hs
  have hb := rate_atom_bound_parameter ε hε.1
  have hl' : 1 / 2 - 4 / Real.sqrt ((dimension ε : ℝ)+1) ≤ limitingRate (dimension ε) := by
    simpa [dimension, s] using hl
  linarith

end ExpandingCodes.PolynomialStretch

end FlattenModule117

/-! Inlined whole module: ExpandingCodes.Probability.CubeSymmetry -/
section FlattenModule118


set_option autoImplicit false
open scoped Classical BigOperators Topology
open Set MeasureTheory

namespace ExpandingCodes.PolynomialStretch

theorem cubeHalfspace_midpoint (d : ℕ) (hd : 0 < d) :
    (volume (cubeHalfspace d ((d : ℝ)/2))).toReal = 1/2 := by
  let L := cubeHalfspace d ((d : ℝ)/2)
  let K : Set (Fin d → ℝ) := Icc (fun _ => 0) (fun _ => 1)
  let U : Set (Fin d → ℝ) := {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (d : ℝ)/2 ≤ ∑ i, x i}
  let T : (Fin d → ℝ) → (Fin d → ℝ) := fun x => (fun _ => 1) - x
  have hmp : MeasurePreserving T volume volume :=
    (volume : Measure (Fin d → ℝ)).measurePreserving_sub_left (fun _ => 1)
  have hpre : T ⁻¹' L = U := by
    ext x
    have hs : (∑ i, (1-x i)) = (d : ℝ) - ∑ i, x i := by
      simp [Finset.sum_sub_distrib]
    change ((∀ i, 0 ≤ 1-x i ∧ 1-x i ≤ 1) ∧ (∑ i, (1-x i)) ≤ (d : ℝ)/2) ↔
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (d : ℝ)/2 ≤ ∑ i, x i
    rw [hs]
    have hc : (∀ i, 0 ≤ 1-x i ∧ 1-x i ≤ 1) ↔ (∀ i, 0 ≤ x i ∧ x i ≤ 1) := by
      apply forall_congr'
      intro i
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hc]
    constructor <;> intro h <;> exact ⟨h.1, by linarith [h.2]⟩
  have hvolU : volume U = volume L := by
    rw [← hpre]
    exact hmp.measure_preimage (measurableSet_cubeHalfspace d _).nullMeasurableSet
  have hU : MeasurableSet U := by
    have he : U = K ∩ {x | (d : ℝ)/2 ≤ ∑ i, x i} := by
      ext x
      simp [U, K, mem_Icc, Pi.le_def, forall_and]
    rw [he]
    exact measurableSet_Icc.inter
      (isClosed_le continuous_const (continuous_coordinateSum d)).measurableSet
  have hunion : L ∪ U = K := by
    ext x
    change ((x ∈ L) ∨ x ∈ U) ↔ x ∈ K
    have ht := le_total (∑ i, x i) ((d : ℝ)/2)
    simp only [L, U, K, cubeHalfspace, mem_ofPred_eq, mem_Icc, Pi.le_def, forall_and]
    tauto
  have hinter : volume (L ∩ U) = 0 := by
    apply measure_mono_null (t := {x : Fin d → ℝ | ∑ i, x i = (d : ℝ)/2})
    · intro x hx
      exact le_antisymm hx.1.2 hx.2.2
    · exact volume_coordinateSum_eq_zero d hd _
  have hsum := measure_union_add_inter (μ := volume) L hU
  rw [hunion, hinter, add_zero, hvolU] at hsum
  have hK : volume K = 1 := by simp [K, Real.volume_Icc_pi]
  rw [hK] at hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (volume_cubeHalfspace_ne_top d _) (volume_cubeHalfspace_ne_top d _)] at hr
  norm_num at hr
  change (volume L).toReal = 1/2
  linarith

theorem limitingRate_lt_half (d : ℕ) (hd : 4 ≤ d) : limitingRate d < 1/2 := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  let t := ((d : ℝ)-3)/2
  let A := cubeHalfspace d t
  let L := cubeHalfspace d ((d : ℝ)/2)
  let O : Set (Fin d → ℝ) := ⋂ i, {x | 0 < x i ∧ x i < 1}
  let W : Set (Fin d → ℝ) := (O ∩ {x | t < ∑ i, x i}) ∩ {x | (∑ i, x i) < (d : ℝ)/2}
  have hO : IsOpen O := isOpen_iInter_of_finite (fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const))
  have hW : IsOpen W := (hO.inter (isOpen_lt continuous_const (continuous_coordinateSum d))).inter
    (isOpen_lt (continuous_coordinateSum d) continuous_const)
  have hWne : W.Nonempty := by
    let c : ℝ := 1/2 - 1/(d : ℝ)
    have hc : 0 < c ∧ c < 1 := by
      have hi : (1 : ℝ)/d ≤ 1/4 := (div_le_div_iff₀ hdpos (by norm_num)).2 (by linarith)
      have hip : (0 : ℝ) < 1/d := by positivity
      dsimp [c]
      constructor <;> linarith
    have he : (d : ℝ)*c = (d : ℝ)/2 - 1 := by
      dsimp [c]
      field_simp
    refine ⟨fun _ => c, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact mem_iInter.mpr (fun _ => hc)
    · change t < ∑ _i : Fin d, c
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [he]
      dsimp [t]
      linarith
    · change (∑ _i : Fin d, c) < (d : ℝ)/2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [he]
      linarith
  have hWsub : W ⊆ L := by
    intro x hx
    refine ⟨?_, hx.2.le⟩
    intro i
    have hi := mem_iInter.mp hx.1.1 i
    exact ⟨hi.1.le, hi.2.le⟩
  have hAsub : A ⊆ L := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by dsimp [t]; linarith)⟩
  have hdis : Disjoint A W := disjoint_left.mpr (by
    intro x ha hw
    exact (not_lt_of_ge ha.2) hw.1.2)
  have hineq : volume A + volume W ≤ volume L := by
    rw [← measure_union hdis hW.measurableSet]
    exact measure_mono (union_subset hAsub hWsub)
  have hWfinite : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cubeHalfspace_ne_top d _) (measure_mono hWsub)
  have hWpos : 0 < (volume W).toReal :=
    ENNReal.toReal_pos (hW.measure_pos volume hWne).ne' hWfinite
  have hr := ENNReal.toReal_mono (volume_cubeHalfspace_ne_top d _) hineq
  rw [ENNReal.toReal_add (volume_cubeHalfspace_ne_top d _) hWfinite,
    cubeHalfspace_midpoint d (by omega)] at hr
  change (volume A).toReal < 1/2
  linarith

end ExpandingCodes.PolynomialStretch

end FlattenModule118

/-! Inlined whole module: ExpandingCodes.Algebra.CodeReindex -/
section FlattenModule119


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

noncomputable def coordinateLinearEquiv {F I J : Type*} [Field F] (e : J ≃ I) :
    (I → F) ≃ₗ[F] (J → F) where
  toFun c := c ∘ e
  invFun c := c ∘ e.symm
  left_inv c := by funext i; simp
  right_inv c := by funext j; simp
  map_add' c c' := rfl
  map_smul' a c := rfl

noncomputable def codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) : Submodule F (J → F) :=
  C.map (coordinateLinearEquiv (F := F) e).toLinearMap

@[simp] theorem mem_codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) (c : J → F) :
    c ∈ codeReindex e C ↔ (fun i => c (e.symm i)) ∈ C := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [coordinateLinearEquiv] using hv
  · intro hc
    refine ⟨(fun i => c (e.symm i)), hc, ?_⟩
    funext j
    simp [coordinateLinearEquiv]

@[simp] theorem finrank_codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) :
    Module.finrank F (codeReindex e C) = Module.finrank F C :=
  (coordinateLinearEquiv (F := F) e).finrank_map_eq C

theorem ambiguity_codeReindex {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (e : J ≃ I) (C : Submodule F (I → F)) (E : Finset J) :
    ambiguity (codeReindex e C) E = codeReindex e (ambiguity C (E.map e.toEmbedding)) := by
  ext c
  simp only [ambiguity, Submodule.mem_mk, mem_codeReindex]
  constructor
  · rintro ⟨hc, hz⟩
    refine ⟨hc, fun i hi => hz _ ?_⟩
    simpa using hi
  · rintro ⟨hc, hz⟩
    refine ⟨hc, fun j hj => ?_⟩
    simpa using hz (e j) (by simpa using hj)

theorem erasureExpectation_codeReindex {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (e : J ≃ I) (C : Submodule F (I → F)) (p : ℝ) :
    erasureExpectation (codeReindex e C) p = erasureExpectation C p := by
  unfold erasureExpectation
  have hdim (E : Finset J) :
      Module.finrank F (ambiguity (codeReindex e C) E) =
        Module.finrank F (ambiguity C (E.map e.toEmbedding)) := by
    calc
      _ = Module.finrank F (codeReindex e (ambiguity C (E.map e.toEmbedding))) :=
        congrArg (fun S : Submodule F (J → F) => Module.finrank F S)
          (ambiguity_codeReindex e C E)
      _ = _ := finrank_codeReindex e _
  simp_rw [hdim]
  apply Fintype.sum_equiv e.finsetCongr
  intro E
  simp only [Equiv.finsetCongr_apply, Finset.card_map, Fintype.card_congr e]
  congr 2

/-- All coordinate permutations preserving a code in both directions. -/
noncomputable def codePreservingSubgroup {F I : Type*} [Field F]
    (C : Submodule F (I → F)) : Subgroup (Equiv.Perm I) where
  carrier := {σ | ∀ c, c ∈ C ↔ (fun i => c (σ i)) ∈ C}
  one_mem' := by intro c; rfl
  mul_mem' := by
    intro σ τ hσ hτ c
    exact (hσ c).trans (hτ (fun i => c (σ i)))
  inv_mem' := by
    intro σ hσ c
    have h := hσ (fun i => c (σ⁻¹ i))
    simpa using h.symm

/-- Transport an honest doubly transitive code symmetry action to numbered coordinates. -/
theorem codeReindex_doublyTransitive {F I : Type*} [Field F] {M : ℕ}
    (e : Fin M ≃ I) (C : Submodule F (I → F))
    (hpair : ∀ a b a' b' : I, a ≠ b → a' ≠ b' →
      ∃ σ ∈ codePreservingSubgroup C, σ a = a' ∧ σ b = b') :
    DoublyTransitiveCode M (codeReindex e C) := by
  refine ⟨codePreservingSubgroup (codeReindex e C), ?_, ?_⟩
  · intro σ hσ c hc
    exact (hσ c).mp hc
  · intro a b a' b' hab hab'
    obtain ⟨σ, hσ, ha, hb⟩ := hpair (e a) (e b) (e a') (e b')
      (e.injective.ne hab) (e.injective.ne hab')
    let τ : Equiv.Perm (Fin M) := (e.trans σ).trans e.symm
    refine ⟨τ, ?_, ?_, ?_⟩
    · intro c
      simp only [mem_codeReindex]
      have h := hσ (fun i => c (e.symm i))
      simpa only [τ, Equiv.trans_apply, Equiv.apply_symm_apply] using h
    · apply e.injective
      simpa [τ] using ha
    · apply e.injective
      simpa [τ] using hb

end ExpandingCodes.PolynomialStretch

end FlattenModule119

/-! Inlined whole module: ExpandingCodes.Algebra.ReedMullerAffine -/
section FlattenModule120




set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Degree of the unique reduced positive power, with zero preserved. -/
def reducedPower (q n : ℕ) : ℕ := if n = 0 then 0 else 1 + (n - 1) % (q - 1)

theorem reducedPower_lt {q : ℕ} (hq : 1 < q) (n : ℕ) : reducedPower q n < q := by
  unfold reducedPower
  split_ifs with hn
  · omega
  · have := Nat.mod_lt (n - 1) (by omega : 0 < q - 1)
    omega

theorem reducedPower_le (q n : ℕ) : reducedPower q n ≤ n := by
  unfold reducedPower
  split_ifs with hn
  · omega
  · have := Nat.mod_le (n - 1) (q - 1)
    omega

theorem pow_reducedPower {F : Type*} [Field F] [Fintype F] (x : F) (n : ℕ) :
    x ^ reducedPower (Fintype.card F) n = x ^ n := by
  by_cases hn : n = 0
  · simp [reducedPower, hn]
  by_cases hx : x = 0
  · simp [hx, reducedPower, hn]
  have hp := FiniteField.pow_card_sub_one_eq_one x hx
  have he : x ^ ((n - 1) % (Fintype.card F - 1)) = x ^ (n - 1) := by
    conv_rhs => rw [← Nat.mod_add_div (n - 1) (Fintype.card F - 1)]
    rw [pow_add, pow_mul, hp, one_pow, mul_one]
  rw [reducedPower, if_neg hn, pow_add, he, pow_one, ← pow_succ']
  congr 1
  omega

/-- Reduction of a support exponent never raises its total degree. -/
noncomputable def reducedExponentMonomial {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (e : Fin d →₀ ℕ) (he : e.sum (fun _ n => n) ≤ R) : Monomials F d R :=
  ⟨fun i => ⟨reducedPower (Fintype.card F) (e i),
    reducedPower_lt (Fintype.one_lt_card (α := F)) (e i)⟩, by
    calc
      (∑ i, reducedPower (Fintype.card F) (e i)) ≤ ∑ i, e i :=
        Finset.sum_le_sum (fun i _ => reducedPower_le _ _)
      _ = e.sum (fun _ n => n) := (Finsupp.sum_fintype e (fun _ n => n) (fun _ => rfl)).symm
      _ ≤ R := he⟩

theorem monomial_eval_mem_reedMuller {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (e : Fin d →₀ ℕ) (c : F) (he : e.sum (fun _ n => n) ≤ R) :
    (fun z => MvPolynomial.eval z (MvPolynomial.monomial e c)) ∈ reedMuller F d R := by
  let a := reducedExponentMonomial (F := F) e he
  have ha : monomialEval a ∈ reedMuller F d R := Submodule.subset_span ⟨a, rfl⟩
  have hfun : (fun z => MvPolynomial.eval z (MvPolynomial.monomial e c)) =
      c • monomialEval a := by
    funext z
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Pi.smul_apply, smul_eq_mul, monomialEval, a, reducedExponentMonomial]
    simp_rw [pow_reducedPower]
  rw [hfun]
  exact Submodule.smul_mem _ c ha

/-- Evaluation of every polynomial of bounded total degree lies in the canonical span.
Its unreduced individual degrees may exceed the field cardinality. -/
theorem eval_mem_reedMuller {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (p : MvPolynomial (Fin d) F) (hp : p.totalDegree ≤ R) :
    (fun z => MvPolynomial.eval z p) ∈ reedMuller F d R := by
  have heq : (fun z => MvPolynomial.eval z p) =
      ∑ e ∈ p.support, (fun z => MvPolynomial.eval z (MvPolynomial.monomial e (p.coeff e))) := by
    funext z
    simpa only [map_sum, Finset.sum_apply] using congrArg (MvPolynomial.eval z) p.as_sum
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  exact monomial_eval_mem_reedMuller e _ ((MvPolynomial.le_totalDegree he).trans hp)

/-- Every coordinatewise affine substitution preserves the Reed--Muller space;
invertibility is only needed later for the permutation group. -/
theorem reedMuller_comp_affine_mem {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (A : Fin d → Fin d → F) (b : Fin d → F) (c : (Fin d → F) → F)
    (hc : c ∈ reedMuller F d R) :
    (fun z => c (fun i => b i + ∑ j, A i j * z j)) ∈ reedMuller F d R := by
  induction hc using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    let p : MvPolynomial (Fin d) F :=
      ∏ i, ExpandingCodes.affinePolynomial (A i) (b i) ^ (a.val i).val
    have hp : p.totalDegree ≤ R := by
      calc
        p.totalDegree ≤ ∑ i, (ExpandingCodes.affinePolynomial (A i) (b i) ^ (a.val i).val).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ i, (a.val i).val := by
          apply Finset.sum_le_sum
          intro i _
          exact (MvPolynomial.totalDegree_pow _ _).trans
            (by simpa using (Nat.mul_le_mul_left ((a.val i).val)
              (ExpandingCodes.totalDegree_affinePolynomial_le (A i) (b i))))
        _ ≤ R := a.property
    have he : (fun z => monomialEval a (fun i => b i + ∑ j, A i j * z j)) =
        (fun z => MvPolynomial.eval z p) := by
      funext z
      simp [p, monomialEval, ExpandingCodes.eval_affinePolynomial]
    rw [he]
    exact eval_mem_reedMuller p hp
  | zero => exact (reedMuller F d R).zero_mem
  | add x y hx hy ihx ihy => exact (reedMuller F d R).add_mem ihx ihy
  | smul r x hx ih => exact (reedMuller F d R).smul_mem r ih

/-- A linear automorphism takes any nonzero vector to any other. -/
theorem exists_linearEquiv_apply_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ T : V ≃ₗ[F] V, T u = v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton F V u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton F V v hv
  let f := eu.symm.trans ev
  obtain ⟨T, hT⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨T, ?_⟩
  have h := hT (eu 1)
  have he : (f (eu 1) : V) = v := by simp [f, ev]
  have hu' : (eu 1 : V) = u := by simp [eu]
  rw [he, hu'] at h
  exact h.symm

/-- Every linear map on the coordinate space has a degree-one polynomial representation. -/
theorem reedMuller_comp_linear_add_mem {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (T : (Fin d → F) →ₗ[F] (Fin d → F)) (b : Fin d → F)
    (c : (Fin d → F) → F) (hc : c ∈ reedMuller F d R) :
    (fun z => c (T z + b)) ∈ reedMuller F d R := by
  let A : Fin d → Fin d → F := fun i j => T (fun k => if j = k then 1 else 0) i
  have hT : ∀ z, T z + b = (fun i => b i + ∑ j, A i j * z j) := by
    intro z
    funext i
    rw [LinearMap.pi_apply_eq_sum_univ T z]
    simp [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm, add_comm]
  simpa only [← hT] using reedMuller_comp_affine_mem A b c hc

/-- An affine permutation with prescribed linear and translation parts. -/
noncomputable def affineCoordinatePerm {F : Type*} [Field F] {d : ℕ}
    (T : (Fin d → F) ≃ₗ[F] (Fin d → F)) (a b : Fin d → F) :
    Equiv.Perm (Fin d → F) where
  toFun z := T (z - a) + b
  invFun z := T.symm (z - b) + a
  left_inv z := by simp
  right_inv z := by simp

theorem affineCoordinatePerm_mem_codePreservingSubgroup {F : Type*} [Field F] [Fintype F]
    {d R : ℕ} (T : (Fin d → F) ≃ₗ[F] (Fin d → F)) (a b : Fin d → F) :
    affineCoordinatePerm T a b ∈ codePreservingSubgroup (reedMuller F d R) := by
  intro c
  constructor
  · intro hc
    have h := reedMuller_comp_linear_add_mem T.toLinearMap (b - T a) c hc
    change (fun z => c (T z + (b - T a))) ∈ reedMuller F d R at h
    have he : (fun z => c (T z + (b - T a))) =
        (fun z => c (affineCoordinatePerm T a b z)) := by
      funext z
      congr 1
      change T z + (b - T a) = T (z - a) + b
      rw [map_sub]
      abel
    rwa [he] at h
  · intro hc
    have h := reedMuller_comp_linear_add_mem T.symm.toLinearMap (a - T.symm b)
      (fun z => c (affineCoordinatePerm T a b z)) hc
    have he : (fun z => c (affineCoordinatePerm T a b (T.symm z + (a - T.symm b)))) = c := by
      funext z
      congr 1
      simp [affineCoordinatePerm, map_add, map_sub]
      abel
    change (fun z => c (affineCoordinatePerm T a b (T.symm z + (a - T.symm b)))) ∈
      reedMuller F d R at h
    rwa [he] at h

/-- The code-preserving affine permutations act doubly transitively on points. -/
theorem reedMuller_pair_transitive {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a b a' b' : Fin d → F) (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ ∈ codePreservingSubgroup (reedMuller F d R), σ a = a' ∧ σ b = b' := by
  obtain ⟨T, hT⟩ := exists_linearEquiv_apply_eq (F := F) (b - a) (b' - a')
    (sub_ne_zero.mpr (Ne.symm hab)) (sub_ne_zero.mpr (Ne.symm hab'))
  refine ⟨affineCoordinatePerm T a a', affineCoordinatePerm_mem_codePreservingSubgroup T a a', ?_, ?_⟩
  · simp [affineCoordinatePerm]
  · change T (b - a) + a' = b'
    rw [hT]
    exact sub_add_cancel _ _

end ExpandingCodes.PolynomialStretch

end FlattenModule120

/-! Inlined whole module: ExpandingCodes.Probability.Erasure -/
section FlattenModule121









/-!
# Erasure ambiguity and the finite Boolean reduction

These interfaces are provisional local formulations of paper Lemma 2.3,
not definitions obtained from the Prove2 platform. The scalar field is arbitrary
and may vary with the sequence index. In particular, no fixed alphabet assumption
is used. The remaining Boolean sharp-threshold obligations are recorded in
`harness/tasks/erasure_capacity.json`.
-/

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.Erasure

open Module Filter Finset

variable {K I : Type*} [Field K]

/-- Words in `C` supported on the erased set `E`. -/
def ambiguity (C : Submodule K (I → K)) (E : Set I) : Submodule K (I → K) where
  carrier := {c | c ∈ C ∧ ∀ i ∉ E, c i = 0}
  zero_mem' := ⟨C.zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨C.add_mem hx.1 hy.1, fun i hi => by simp [hx.2 i hi, hy.2 i hi]⟩
  smul_mem' := by
    intro a x hx
    exact ⟨C.smul_mem a hx.1, fun i hi => by simp [hx.2 i hi]⟩







theorem ambiguity_mono (C : Submodule K (I → K)) {E F : Set I} (h : E ⊆ F) :
    ambiguity C E ≤ ambiguity C F := by
  intro c hc
  exact ⟨hc.1, fun i hi => hc.2 i (fun he => hi (h he))⟩









































/-- A coordinate is undetermined iff some compatible codeword is nonzero there.
For a linear code this is equivalent to ambiguity among compatible codewords. -/
def undetermined (C : Submodule K (I → K)) (E : Set I) : Set I :=
  {i | ∃ c ∈ ambiguity C E, c i ≠ 0}

theorem undetermined_subset (C : Submodule K (I → K)) (E : Set I) :
    undetermined C E ⊆ E := by
  intro i hi
  obtain ⟨c, hc, hci⟩ := hi
  by_contra hie
  exact hci (hc.2 i hie)

theorem undetermined_mono (C : Submodule K (I → K)) {E F : Set I} (h : E ⊆ F) :
    undetermined C E ⊆ undetermined C F := by
  rintro i ⟨c, hc, hci⟩
  exact ⟨c, ambiguity_mono C h hc, hci⟩

/-- Transport of the symbol-recovery event under an automorphism of the code.
Both preservation directions are explicit, as supplied by a subgroup and its
inverse elements in the canonical `DoublyTransitiveCode` definition. -/
theorem undetermined_permute (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) (E : Set I) (i : I) :
    σ i ∈ undetermined C (σ '' E) ↔ i ∈ undetermined C E := by
  constructor
  · rintro ⟨c, hc, hci⟩
    refine ⟨fun j => c (σ j), ⟨hσ c hc.1, ?_⟩, hci⟩
    intro j hj
    apply hc.2
    rintro ⟨k, hk, hkj⟩
    exact hj (σ.injective hkj ▸ hk)
  · rintro ⟨c, hc, hci⟩
    refine ⟨fun j => c (σ.symm j), ⟨hσinv c hc.1, ?_⟩, ?_⟩
    · intro j hj
      apply hc.2
      intro hmem
      apply hj
      exact ⟨σ.symm j, hmem, σ.apply_symm_apply j⟩
    · simpa only [σ.symm_apply_apply] using hci

theorem ambiguity_supported_on_undetermined (C : Submodule K (I → K))
    (E : Set I) {c : I → K} (hc : c ∈ ambiguity C E) :
    ∀ i ∉ undetermined C E, c i = 0 := by
  intro i hi
  by_contra hci
  exact hi ⟨c, hc, hci⟩

/-- Restriction to the undetermined coordinates loses no ambiguity vectors. -/
def ambiguityToUndetermined (C : Submodule K (I → K)) (E : Set I) :
    ambiguity C E →ₗ[K] (undetermined C E → K) where
  toFun c i := c.val i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem ambiguityToUndetermined_injective (C : Submodule K (I → K)) (E : Set I) :
    Function.Injective (ambiguityToUndetermined C E) := by
  intro x y h
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ undetermined C E
  · exact congrFun h ⟨i, hi⟩
  · rw [ambiguity_supported_on_undetermined C E x.property i hi,
      ambiguity_supported_on_undetermined C E y.property i hi]

variable [Fintype I]

/-- The elementary final inequality in paper Lemma 2.3. It is uniform over fields. -/
theorem finrank_ambiguity_le_undetermined (C : Submodule K (I → K)) (E : Set I) :
    finrank K (ambiguity C E) ≤ Nat.card (undetermined C E) := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    (LinearMap.finrank_le_finrank_of_injective
    (ambiguityToUndetermined_injective C E)).trans_eq (Module.finrank_pi K)
















/-- Observed coordinates whose values cannot be inferred from the other observed
coordinates. They are the essential coordinates of the restriction map. -/
def essential (C : Submodule K (I → K)) (E : Set I) : Set I :=
  {i | i ∉ E ∧ i ∈ undetermined C (insert i E)}

/-- A pointwise, purely linear-algebraic replacement for the one-sided EXIT area
bound: essential observed coordinates have linearly independent witnesses. -/
theorem card_essential_le_finrank (C : Submodule K (I → K)) (E : Set I) :
    Nat.card (essential C E) ≤ finrank K C := by
  classical
  have hw : ∀ i : essential C E, ∃ c : C,
      (∀ j ∉ insert i.val E, c.val j = 0) ∧ c.val i.val ≠ 0 := by
    intro i
    obtain ⟨c, hc, hci⟩ := i.property.2
    exact ⟨⟨c, hc.1⟩, hc.2, hci⟩
  choose w hw0 hwne using hw
  have hoff : ∀ i j : essential C E, j ≠ i → (w j).val i.val = 0 := by
    intro i j hji
    apply hw0 j
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨fun hij => hji (Subtype.ext hij.symm), i.property.1⟩
  have hli : LinearIndependent K w := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have hs := congrArg (fun c : C => c.val i.val) hg
    have hsum : (∑ j, g j * (w j).val i.val) = 0 := by
      simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] using hs
    rw [Finset.sum_eq_single i] at hsum
    · exact (mul_eq_zero.mp hsum).resolve_right (hwne i)
    · intro j _ hji
      rw [hoff i j hji, mul_zero]
    · simp
  simpa only [Nat.card_eq_fintype_card] using hli.fintype_card_le_finrank

/-- Probability of a particular independently erased coordinate set. -/
noncomputable def patternWeight (p : ℝ) (E : Finset I) : ℝ :=
  p ^ E.card * (1 - p) ^ (Fintype.card I - E.card)

theorem patternWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (E : Finset I) :
    0 ≤ patternWeight p E :=
  mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _)

theorem sum_patternWeight (p : ℝ) : ∑ E : Finset I, patternWeight p E = 1 := by
  classical
  simpa [patternWeight] using (Fintype.sum_pow_mul_eq_add_pow I p (1 - p))

/-- Finite Bernoulli expectation. The weights sum to one and are nonnegative
on `[0,1]`; no measurable-space or fixed-field convention is hidden here. -/
noncomputable def expectation (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  ∑ E : Finset I, patternWeight p E * f E

/-- The same independent erasure expectation on a specified finite coordinate set. -/
noncomputable def expectationOn (s : Finset I) (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  ∑ E ∈ s.powerset, p ^ E.card * (1 - p) ^ (s.card - E.card) * f E

theorem expectationOn_univ (p : ℝ) (f : Finset I → ℝ) :
    expectationOn Finset.univ p f = expectation p f := by
  classical
  simp [expectationOn, expectation, patternWeight]

theorem expectationOn_mono {s : Finset I} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {f g : Finset I → ℝ} (h : ∀ E ∈ s.powerset, f E ≤ g E) :
    expectationOn s p f ≤ expectationOn s p g := by
  classical
  apply Finset.sum_le_sum
  intro E hE
  exact mul_le_mul_of_nonneg_left (h E hE)
    (mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _))

@[simp] theorem expectationOn_const (s : Finset I) (p a : ℝ) :
    expectationOn s p (fun _ => a) = a := by
  classical
  unfold expectationOn
  rw [← Finset.sum_mul, Finset.sum_pow_mul_eq_add_pow]
  simp

/-- Reindex a finite erasure model by the subtype of coordinates actually used.
This connects `exit` to a Boolean function on exactly `length - 1` bits. -/
theorem expectationOn_eq_expectation_subtype (s : Finset I) (p : ℝ)
    (f : Finset I → ℝ) :
    expectationOn s p f = expectation (I := s) p
      (fun E => f (E.map (Function.Embedding.subtype (fun j => j ∈ s)))) := by
  classical
  unfold expectationOn expectation patternWeight
  symm
  refine Finset.sum_bij (fun E _ => E.map (Function.Embedding.subtype _)) ?_ ?_ ?_ ?_
  · intro E _
    apply Finset.mem_powerset.mpr
    intro j hj
    exact Finset.property_of_mem_map_subtype E hj
  · intro E _ E' _ h
    exact Finset.map_injective (Function.Embedding.subtype _) h
  · intro E hE
    refine ⟨E.subtype (fun j => j ∈ s), Finset.mem_univ _, ?_⟩
    exact Finset.subtype_map_of_mem (Finset.mem_powerset.mp hE)
  · intro E _
    simp only [Finset.card_map, Fintype.card_coe]

theorem expectationOn_permute [DecidableEq I] (σ : Equiv.Perm I) (s : Finset I)
    (p : ℝ) (f : Finset I → ℝ) :
    expectationOn (s.image σ) p f =
      expectationOn s p (fun E => f (E.image σ)) := by
  classical
  unfold expectationOn
  symm
  refine Finset.sum_bij (fun E _ => E.image σ) ?_ ?_ ?_ ?_
  · intro E hE
    exact Finset.mem_powerset.mpr (Finset.image_mono σ (Finset.mem_powerset.mp hE))
  · intro E _ E' _ h
    exact Finset.image_injective σ.injective h
  · intro E hE
    refine ⟨E.image σ.symm, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨l, hl, hlk⟩ := Finset.mem_image.mp (Finset.mem_powerset.mp hE hk)
      simpa only [← hlk, σ.symm_apply_apply] using hl
    · simp only [Finset.image_image, Function.comp_def, σ.apply_symm_apply,
        Finset.image_id']
  · intro E _
    simp only [Finset.card_image_of_injective _ σ.injective]

/-- Peel off one independent Bernoulli coordinate, keeping both conditional laws
explicit. This is independent of any coding-theoretic assumption. -/
theorem expectationOn_insert [DecidableEq I] {s : Finset I} {i : I} (hi : i ∉ s)
    (p : ℝ) (f : Finset I → ℝ) :
    expectationOn (insert i s) p f =
      (1 - p) * expectationOn s p f +
        p * expectationOn s p (fun E => f (insert i E)) := by
  unfold expectationOn
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro E hE
    have hcard : E.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hE)
    have hsub : s.card + 1 - E.card = s.card - E.card + 1 := by omega
    rw [Finset.card_insert_of_notMem hi, hsub, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro E hE
    have hiE : i ∉ E := fun h => hi (Finset.mem_powerset.mp hE h)
    rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hiE]
    simp only [Nat.add_sub_add_right, pow_succ]
    ring

/-- The extrinsic failure event tests recovery of coordinate `i` after erasing
the other coordinates in `E`. Its truth value ignores whether `i ∈ E`. -/
def extrinsicFailure (C : Submodule K (I → K)) (i : I) (E : Finset I) : Prop :=
  i ∈ undetermined C (insert i (E : Set I))

theorem extrinsicFailure_mono (C : Submodule K (I → K)) (i : I)
    {E E' : Finset I} (h : E ⊆ E') :
    extrinsicFailure C i E → extrinsicFailure C i E' := by
  intro hi
  exact undetermined_mono C
    (show insert i (E : Set I) ⊆ insert i (E' : Set I) from Set.insert_subset_insert h) hi

theorem extrinsicFailure_permute (C : Submodule K (I → K))
    (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) (i : I) (E : Finset I) :
    extrinsicFailure C (σ i) (E.image σ) ↔ extrinsicFailure C i E := by
  unfold extrinsicFailure
  simpa only [Set.image_insert_eq, Finset.coe_image] using
    undetermined_permute C σ hσ hσinv (insert i (E : Set I)) i

/-- The coordinate subtype used by the Boolean erasure cube. Freezing this
abbreviation avoids mismatched decidable-equality implementations in dependent
types when the ambient coordinates are later specialized to `Fin M`. -/
abbrev OtherCoordinates (i : I) := ↥(Finset.univ.erase i : Finset I)

theorem otherCoordinates_ne (i : I) (j : OtherCoordinates i) : j.val ≠ i :=
  (Finset.mem_erase.mp j.property).1

theorem card_otherCoordinates (i : I) :
    Fintype.card (OtherCoordinates i) = Fintype.card I - 1 := by
  simp only [OtherCoordinates, Fintype.card_coe,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- The Boolean event on the `length - 1` coordinates other than `i`. -/
def puncturedFailure (C : Submodule K (I → K)) (i : I)
    (E : Finset (OtherCoordinates i)) : Prop :=
  extrinsicFailure C i (E.map (Function.Embedding.subtype _))

/-- A coordinate permutation induces a bijection of the two punctured coordinate
sets. In the stabilizer case this is a permutation of one Boolean cube. -/
noncomputable def puncturedEquiv (σ : Equiv.Perm I) {i j : I} (hσ : σ i = j) :
    ↥(Finset.univ.erase i : Finset I) ≃ ↥(Finset.univ.erase j : Finset I) :=
  σ.subtypeEquiv (by
    intro k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hk hkj
      exact hk (σ.injective (hkj.trans hσ.symm))
    · intro hk hki
      exact hk (hki ▸ hσ))

theorem puncturedFailure_permute (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) {i j : I} (hij : σ i = j)
    (E : Finset ↥(Finset.univ.erase i : Finset I)) :
    puncturedFailure C j (E.image (puncturedEquiv σ hij)) ↔ puncturedFailure C i E := by
  classical
  have hm : (E.image (puncturedEquiv σ hij)).map (Function.Embedding.subtype _) =
      (E.map (Function.Embedding.subtype _)).image σ := by
    simp only [Finset.map_eq_image, Finset.image_image]
    rfl
  unfold puncturedFailure
  rw [hm, ← hij]
  exact extrinsicFailure_permute C σ hσ hσinv i _

/-- Embedding-map form of event transport, independent of any chosen
decidable-equality implementation on the punctured coordinate types. -/
theorem puncturedFailure_map (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) {i j : I} (hij : σ i = j)
    (E : Finset (OtherCoordinates i)) :
    puncturedFailure C j (E.map (puncturedEquiv σ hij).toEmbedding) ↔
      puncturedFailure C i E := by
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using
    puncturedFailure_permute C σ hσ hσinv hij E

theorem puncturedFailure_mono (C : Submodule K (I → K)) (i : I)
    {E E' : Finset ↥(Finset.univ.erase i : Finset I)} (h : E ⊆ E') :
    puncturedFailure C i E → puncturedFailure C i E' :=
  extrinsicFailure_mono C i (Finset.map_subset_map.mpr h)

noncomputable def exit (C : Submodule K (I → K)) (i : I) (p : ℝ) : ℝ := by
  classical
  exact expectationOn (Finset.univ.erase i) p
    (fun E => if extrinsicFailure C i E then 1 else 0)

theorem exit_eq_puncturedProbability (C : Submodule K (I → K)) (i : I) (p : ℝ) :
    exit C i p = expectation (I := ↥(Finset.univ.erase i : Finset I)) p
      (fun E => if puncturedFailure C i E then 1 else 0) := by
  exact expectationOn_eq_expectation_subtype _ _ _

theorem exit_permute (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) (i : I) (p : ℝ) :
    exit C (σ i) p = exit C i p := by
  classical
  have hs : (Finset.univ.erase i).image σ = Finset.univ.erase (σ i) := by
    rw [Finset.image_erase σ.injective, Finset.image_univ_equiv]
  unfold exit
  rw [← hs, expectationOn_permute]
  simp_rw [extrinsicFailure_permute C σ hσ hσinv]

theorem exit_nonneg (C : Submodule K (I → K)) (i : I) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ exit C i p := by
  classical
  unfold exit
  rw [← expectationOn_const (Finset.univ.erase i) p 0]
  exact expectationOn_mono hp hp' fun E _ => by split <;> norm_num

theorem exit_le_one (C : Submodule K (I → K)) (i : I) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : exit C i p ≤ 1 := by
  classical
  unfold exit
  rw [← expectationOn_const (Finset.univ.erase i) p 1]
  exact expectationOn_mono hp hp' fun E _ => by split <;> norm_num

theorem expectation_undetermined_indicator (C : Submodule K (I → K)) (i : I)
    (p : ℝ) :
    expectation p (fun E : Finset I => if i ∈ undetermined C (E : Set I) then 1 else 0) =
      p * exit C i p := by
  classical
  rw [← expectationOn_univ]
  have hu : (Finset.univ : Finset I) = insert i (Finset.univ.erase i) := by simp
  rw [hu, expectationOn_insert (Finset.notMem_erase i Finset.univ)]
  have hz : expectationOn (Finset.univ.erase i) p
      (fun E : Finset I => if i ∈ undetermined C (E : Set I) then 1 else 0) = 0 := by
    unfold expectationOn
    apply Finset.sum_eq_zero
    intro E hE
    have hiE : i ∉ E := fun h =>
      (Finset.notMem_erase i Finset.univ) (Finset.mem_powerset.mp hE h)
    have hnot : i ∉ undetermined C (E : Set I) := fun h =>
      hiE (undetermined_subset C (E : Set I) h)
    simp [hnot]
  rw [hz, mul_zero, zero_add]
  congr 1
  simp only [exit, extrinsicFailure, Finset.coe_insert]
  rfl

theorem expectation_essential_indicator (C : Submodule K (I → K)) (i : I)
    (p : ℝ) :
    expectation p (fun E : Finset I => if i ∈ essential C (E : Set I) then 1 else 0) =
      (1 - p) * exit C i p := by
  classical
  rw [← expectationOn_univ]
  have hu : (Finset.univ : Finset I) = insert i (Finset.univ.erase i) := by simp
  rw [hu, expectationOn_insert (Finset.notMem_erase i Finset.univ)]
  have hz : expectationOn (Finset.univ.erase i) p
      (fun E : Finset I => if i ∈ essential C ((insert i E : Finset I) : Set I)
        then 1 else 0) = 0 := by
    simp [expectationOn, essential]
  rw [hz, mul_zero, add_zero]
  congr 1
  unfold expectationOn exit
  apply Finset.sum_congr rfl
  intro E hE
  have hiE : i ∉ E := fun h =>
    (Finset.notMem_erase i Finset.univ) (Finset.mem_powerset.mp hE h)
  by_cases h : i ∈ undetermined C (insert i (E : Set I)) <;>
    simp [essential, hiE, extrinsicFailure, h]

theorem expectation_mono {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {f g : Finset I → ℝ} (h : ∀ E, f E ≤ g E) :
    expectation p f ≤ expectation p g := by
  classical
  exact Finset.sum_le_sum fun E _ =>
    mul_le_mul_of_nonneg_left (h E) (patternWeight_nonneg hp hp' E)

@[simp] theorem expectation_const (p a : ℝ) : expectation (I := I) p (fun _ => a) = a := by
  classical
  rw [expectation, ← Finset.sum_mul, sum_patternWeight, one_mul]

/-- Expected dimension of the erasure ambiguity subspace. -/
noncomputable def expectedAmbiguity (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectation p fun E : Finset I => (finrank K (ambiguity C (E : Set I)) : ℝ)

/-- Expected number of coordinates not determined by the unerased coordinates. -/
noncomputable def expectedUndetermined (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectation p fun E : Finset I => (Nat.card (undetermined C (E : Set I)) : ℝ)

theorem card_set_eq_sum_indicator (S : Set I) :
    (Nat.card S : ℝ) = ∑ i : I, if i ∈ S then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.natCast_card_filter _ _

theorem expectation_sum {J : Type*} [Fintype J] (p : ℝ)
    (f : J → Finset I → ℝ) :
    expectation p (fun E => ∑ j, f j E) = ∑ j, expectation p (f j) := by
  classical
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectedUndetermined_eq_sum_exit (C : Submodule K (I → K)) (p : ℝ) :
    expectedUndetermined C p = p * ∑ i : I, exit C i p := by
  classical
  unfold expectedUndetermined
  simp_rw [card_set_eq_sum_indicator]
  rw [expectation_sum]
  simp_rw [expectation_undetermined_indicator]
  rw [Finset.mul_sum]

/-- The one-sided EXIT area bound proved by independent witnesses, without
entropy or an integral identity. -/
theorem exit_area_bound (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1 - p) * ∑ i : I, exit C i p ≤ (finrank K C : ℝ) := by
  classical
  have h : expectation p (fun E : Finset I => (Nat.card (essential C (E : Set I)) : ℝ)) ≤
      expectation p (fun _ : Finset I => (finrank K C : ℝ)) := by
    apply expectation_mono hp hp'
    intro E
    exact_mod_cast card_essential_le_finrank C (E : Set I)
  rw [expectation_const] at h
  simp_rw [card_set_eq_sum_indicator] at h
  rw [expectation_sum] at h
  simp_rw [expectation_essential_indicator] at h
  rwa [← Finset.mul_sum] at h

noncomputable def meanExit (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  (∑ i : I, exit C i p) / Fintype.card I

noncomputable def rate (C : Submodule K (I → K)) : ℝ :=
  (finrank K C : ℝ) / Fintype.card I

theorem meanExit_nonneg (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ meanExit C p := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun i _ => exit_nonneg C i hp hp'

theorem meanExit_le_one (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : meanExit C p ≤ 1 := by
  by_cases hcard : Fintype.card I = 0
  · simp [meanExit, hcard]
  have hsum : (∑ i : I, exit C i p) ≤ (Fintype.card I : ℝ) := by
    calc
      _ ≤ ∑ _i : I, (1 : ℝ) := Finset.sum_le_sum fun i _ => exit_le_one C i hp hp'
      _ = _ := by simp
  exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hcard)).mpr hsum

theorem meanExit_area_bound (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : (1 - p) * meanExit C p ≤ rate C := by
  unfold meanExit rate
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (exit_area_bound C hp hp') (Nat.cast_nonneg _)

theorem expectedAmbiguity_nonneg (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ expectedAmbiguity C p := by
  classical
  unfold expectedAmbiguity expectation
  apply Finset.sum_nonneg
  intro E _
  exact mul_nonneg (patternWeight_nonneg hp hp' E) (Nat.cast_nonneg _)

theorem expectedAmbiguity_le_expectedUndetermined (C : Submodule K (I → K))
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    expectedAmbiguity C p ≤ expectedUndetermined C p := by
  unfold expectedAmbiguity expectedUndetermined
  apply expectation_mono hp hp'
  intro E
  exact_mod_cast finrank_ambiguity_le_undetermined C (E : Set I)

/-- Normalization of the expected ambiguity dimension by blocklength. -/
noncomputable def normalizedAmbiguity (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectedAmbiguity C p / Fintype.card I

/-- Normalization of the expected number of undetermined coordinates. -/
noncomputable def normalizedUndetermined (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectedUndetermined C p / Fintype.card I

theorem normalizedAmbiguity_nonneg (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ normalizedAmbiguity C p :=
  div_nonneg (expectedAmbiguity_nonneg C hp hp') (Nat.cast_nonneg _)

theorem normalizedAmbiguity_le_normalizedUndetermined (C : Submodule K (I → K))
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    normalizedAmbiguity C p ≤ normalizedUndetermined C p :=
  div_le_div_of_nonneg_right (expectedAmbiguity_le_expectedUndetermined C hp hp')
    (Nat.cast_nonneg _)

theorem normalizedAmbiguity_le_meanExit (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : normalizedAmbiguity C p ≤ meanExit C p := by
  calc
    normalizedAmbiguity C p ≤ normalizedUndetermined C p :=
      normalizedAmbiguity_le_normalizedUndetermined C hp hp'
    _ = p * meanExit C p := by
      unfold normalizedUndetermined meanExit
      rw [expectedUndetermined_eq_sum_exit, mul_div_assoc]
    _ ≤ meanExit C p := mul_le_of_le_one_left (meanExit_nonneg C hp hp') hp'

/-- Pure limit algebra locating a sharp transition from the one-sided area
bound. The sharpness hypothesis concerns two distinct probabilities and is
strictly independent of the rate/linear-algebra argument above. -/
theorem ambiguity_sublinear_of_exit_crossDecay
    {N : ℕ → ℕ} {F : ℕ → Type*} [∀ j, Field (F j)]
    (C : ∀ j, Submodule (F j) (Fin (N j) → F j)) {ρ p q : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hq : q < 1) (hqr : ρ < 1 - q)
    (hrate : Tendsto (fun j => rate (C j)) atTop (nhds ρ))
    (hcross : Tendsto (fun j => meanExit (C j) p * (1 - meanExit (C j) q))
      atTop (nhds 0)) :
    Tendsto (fun j => normalizedAmbiguity (C j) p) atTop (nhds 0) := by
  let δ : ℝ := (1 - q - ρ) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hq0 : 0 ≤ q := hp.trans hpq.le
  have hp1 : p ≤ 1 := hpq.le.trans hq.le
  have hrbound : ∀ᶠ j in atTop, rate (C j) < ρ + δ :=
    (tendsto_order.mp hrate).2 (ρ + δ) (by linarith)
  have hgap : ∀ᶠ j in atTop, δ ≤ 1 - meanExit (C j) q := by
    filter_upwards [hrbound] with j hj
    have ha := meanExit_area_bound (C j) hq0 hq.le
    have hb := meanExit_le_one (C j) hq0 hq.le
    have hc := mul_nonneg hq0 (sub_nonneg.mpr hb)
    dsimp [δ] at *
    nlinarith
  have hupper : ∀ᶠ j in atTop,
      normalizedAmbiguity (C j) p ≤
        (meanExit (C j) p * (1 - meanExit (C j) q)) / δ := by
    filter_upwards [hgap] with j hj
    apply (normalizedAmbiguity_le_meanExit (C j) hp hp1).trans
    apply (le_div_iff₀ hδ).mpr
    exact mul_le_mul_of_nonneg_left hj (meanExit_nonneg (C j) hp hp1)
  have hzero : Tendsto (fun j =>
      (meanExit (C j) p * (1 - meanExit (C j) q)) / δ) atTop (nhds 0) := by
    simpa using hcross.div_const δ
  exact squeeze_zero' (Filter.Eventually.of_forall fun j =>
    normalizedAmbiguity_nonneg (C j) hp hp1) hupper hzero












end ExpandingCodes.Erasure

end FlattenModule121

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.Basic -/
section FlattenModule122






/-!
# A qualitative Boolean sharp-threshold route

These are independent, provisional Boolean-analysis interfaces, not platform
axioms or a completed sharp-threshold proof. The remaining analytic obligations
are explicitly registered in `harness/tasks/sharp_threshold.json`.

The proposed route uses a fixed Fourier cutoff and only then takes the cutoff
to infinity. It does not require the quantitative logarithmic KKL inequality.
-/

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

noncomputable def indicator (Ω : Finset I → Prop) (E : Finset I) : ℝ := by
  classical
  exact if Ω E then 1 else 0

def Upward (Ω : Finset I → Prop) : Prop :=
  ∀ E F, E ⊆ F → Ω E → Ω F

noncomputable def probability (p : ℝ) (Ω : Finset I → Prop) : ℝ :=
  expectation p (indicator Ω)

noncomputable def variance (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  expectation p (fun E => f E ^ 2) - (expectation p f) ^ 2

noncomputable def gradient (i : I) (f : Finset I → ℝ) (E : Finset I) : ℝ := by
  classical
  exact f (insert i E) - f (E.erase i)

/-- For an upward event this is the usual nonnegative pivotal probability.
The definition also makes sense for general real-valued functions. -/
noncomputable def influence (p : ℝ) (Ω : Finset I → Prop) (i : I) : ℝ :=
  expectation p (gradient i (indicator Ω))

noncomputable def totalInfluence (p : ℝ) (Ω : Finset I → Prop) : ℝ :=
  ∑ i, influence p Ω i

/-- The centered, normalized biased coordinate. -/
noncomputable def coordinate (p : ℝ) (i : I) (E : Finset I) : ℝ := by
  classical
  exact ((if i ∈ E then 1 else 0) - p) / Real.sqrt (p * (1 - p))

noncomputable def character (p : ℝ) (S E : Finset I) : ℝ :=
  ∏ i ∈ S, coordinate p i E

noncomputable def fourier (p : ℝ) (f : Finset I → ℝ) (S : Finset I) : ℝ :=
  expectation p (fun E => f E * character p S E)

/-- Biased noise operator in the explicitly defined finite Fourier basis. -/
noncomputable def noise (p r : ℝ) (f : Finset I → ℝ) (E : Finset I) : ℝ :=
  ∑ S : Finset I, r ^ S.card * fourier p f S * character p S E

/-- The one-coordinate L^(4/3) to L² contraction, written without norms.
Its uniform compact-interval version is the only genuinely scalar analytic
inequality needed by the proposed route. -/
def TwoPointContraction (p r : ℝ) : Prop :=
  ∀ x y : ℝ,
    (1 - p) * (((1 - p) * x + p * y) + r * (x - ((1 - p) * x + p * y))) ^ 2 +
      p * (((1 - p) * x + p * y) + r * (y - ((1 - p) * x + p * y))) ^ 2 ≤
    ((1 - p) * |x| ^ (4 / 3 : ℝ) + p * |y| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ)

lemma indicator_nonneg (Ω : Finset I → Prop) (E : Finset I) :
    0 ≤ indicator Ω E := by
  classical
  unfold indicator
  split_ifs <;> norm_num

lemma indicator_le_one (Ω : Finset I → Prop) (E : Finset I) :
    indicator Ω E ≤ 1 := by
  classical
  unfold indicator
  split_ifs <;> norm_num

lemma probability_mem_Icc {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (Ω : Finset I → Prop) : probability p Ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · simpa [probability] using
      (expectation_mono hp hp' (fun E => indicator_nonneg Ω E))
  · simpa [probability] using
      (expectation_mono hp hp' (fun E => indicator_le_one Ω E))

lemma variance_indicator (p : ℝ) (Ω : Finset I → Prop) :
    variance p (indicator Ω) = probability p Ω * (1 - probability p Ω) := by
  have h : (fun E => indicator Ω E ^ 2) = indicator Ω := by
    funext E
    classical
    unfold indicator
    split_ifs <;> norm_num
  rw [variance, h]
  unfold probability
  ring

lemma gradient_indicator_nonneg (Ω : Finset I → Prop) (hΩ : Upward Ω)
    (i : I) (E : Finset I) : 0 ≤ gradient i (indicator Ω) E := by
  classical
  have hsub : E.erase i ⊆ insert i E :=
    (Finset.erase_subset i E).trans (Finset.subset_insert i E)
  have h := hΩ (E.erase i) (insert i E) hsub
  unfold gradient indicator
  split_ifs <;> simp_all

lemma influence_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (Ω : Finset I → Prop) (hΩ : Upward Ω) (i : I) : 0 ≤ influence p Ω i := by
  simpa [influence] using
    (expectation_mono hp hp' (fun E => gradient_indicator_nonneg Ω hΩ i E))

/-- A finite weighted tail bound. This is the elementary spectral-cutoff step:
no Boolean-analysis or sharp-threshold assertion is assumed. -/
theorem weighted_cutoff {A : Type*} [Fintype A] (a : A → ℝ) (d : A → ℕ)
    (ha : ∀ x, 0 ≤ a x) (k : ℕ) :
    (∑ x, a x) ≤ (∑ x, if d x ≤ k then a x else 0) +
      (∑ x, (d x : ℝ) * a x) / (k + 1 : ℝ) := by
  classical
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hpoint : ∀ x, a x ≤ (if d x ≤ k then a x else 0) +
      ((d x : ℝ) * a x) / (k + 1 : ℝ) := by
    intro x
    split_ifs with hx
    · have hn : 0 ≤ ((d x : ℝ) * a x) / (k + 1 : ℝ) :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha x)) hk.le
      linarith
    · simp only [zero_add]
      apply (le_div_iff₀ hk).mpr
      have hd : (k + 1 : ℝ) ≤ d x := by exact_mod_cast (by omega : k + 1 ≤ d x)
      nlinarith [ha x]
  simpa only [Finset.sum_add_distrib, ← Finset.sum_div] using
    (Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x))

/-- Low degrees are controlled by noisy-gradient energy. Together with
`weighted_cutoff`, this is the entire coefficient-estimate part of the proof. -/
theorem weighted_low_degree {A : Type*} [Fintype A] (a : A → ℝ) (d : A → ℕ)
    (ha : ∀ x, 0 ≤ a x) (hzero : ∀ x, d x = 0 → a x = 0)
    (k : ℕ) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    (∑ x, if d x ≤ k then a x else 0) ≤
      (∑ x, (d x : ℝ) * r ^ (2 * (d x - 1)) * a x) / r ^ (2 * k) := by
  classical
  have hp : 0 < r ^ (2 * k) := pow_pos hr _
  apply (le_div_iff₀ hp).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hz : d x = 0
  · simp [hzero x hz]
  by_cases hx : d x ≤ k
  · rw [if_pos hx]
    have hd : (1 : ℝ) ≤ d x := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
    have hrpow : r ^ (2 * k) ≤ r ^ (2 * (d x - 1)) :=
      pow_le_pow_of_le_one hr.le hr' (by omega)
    calc
      a x * r ^ (2 * k) ≤ a x * r ^ (2 * (d x - 1)) :=
        mul_le_mul_of_nonneg_left hrpow (ha x)
      _ ≤ (d x : ℝ) * r ^ (2 * (d x - 1)) * a x := by
        nlinarith [mul_nonneg (pow_nonneg hr.le (2 * (d x - 1))) (ha x)]
  · rw [if_neg hx, zero_mul]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.le _)) (ha x)

/-- Small individual influences control the nonlinear influence moment that
hypercontractivity contributes to the low-degree bound. -/
theorem influence_moment_bound (v : I → ℝ) {η B : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hη : ∀ i, v i ≤ η) (hB : (∑ i, v i) ≤ B) :
    (∑ i, v i * Real.sqrt (v i)) ≤ B * Real.sqrt η := by
  calc
    (∑ i, v i * Real.sqrt (v i)) ≤ ∑ i, v i * Real.sqrt η := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hη i)) (hv i)
    _ = (∑ i, v i) * Real.sqrt η := (Finset.sum_mul ..).symm
    _ ≤ B * Real.sqrt η := mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg η)

/-- Combines separately checkable Fourier inputs into the qualitative estimate.
The hard input is the low-degree estimate, not this arithmetic assembly. -/
theorem cutoff_variance_bound {A : Type*} [Fintype A]
    (a : A → ℝ) (d : A → ℕ) (v : I → ℝ) (k : ℕ) {V B L η : ℝ}
    (ha : ∀ x, 0 ≤ a x) (hV : V = ∑ x, a x)
    (henergy : (∑ x, (d x : ℝ) * a x) ≤ B)
    (hlow : (∑ x, if d x ≤ k then a x else 0) ≤
      L * (∑ i, v i * Real.sqrt (v i)))
    (hL : 0 ≤ L) (hv : ∀ i, 0 ≤ v i) (hη : ∀ i, v i ≤ η)
    (hB : (∑ i, v i) ≤ B) :
    V ≤ L * B * Real.sqrt η + B / (k + 1 : ℝ) := by
  rw [hV]
  apply (weighted_cutoff a d ha k).trans
  have hlow' := hlow.trans (mul_le_mul_of_nonneg_left
    (influence_moment_bound v hv hη hB) hL)
  have htail := div_le_div_of_nonneg_right henergy
    (show (0 : ℝ) ≤ k + 1 by positivity)
  nlinarith

/-- Symmetry turns a bound on total influence into a vanishing bound on each
individual influence. No group action or Boolean analysis is hidden here. -/
theorem equal_influences_bound (v : I → ℝ) {B : ℝ}
    (hcard : 0 < Fintype.card I) (heq : ∀ i j, v i = v j)
    (hB : (∑ i, v i) ≤ B) (i : I) : v i ≤ B / Fintype.card I := by
  have hs : (∑ j, v j) = (Fintype.card I : ℝ) * v i := by
    calc
      (∑ j, v j) = ∑ _j : I, v i := Finset.sum_congr rfl (fun j _ => heq j i)
      _ = (Fintype.card I : ℝ) * v i := by simp
  apply (le_div_iff₀ (by exact_mod_cast hcard : (0 : ℝ) < Fintype.card I)).mpr
  simpa only [hs, mul_comm] using hB

/-- Probability is a finite polynomial in the Bernoulli parameter. -/
theorem differentiable_probability (Ω : Finset I → Prop) :
    Differentiable ℝ (fun p => probability p Ω) := by
  unfold probability expectation patternWeight
  fun_prop

/-- A monotone Boolean discrete derivative is again a zero-one function. -/
lemma gradient_indicator_values (Ω : Finset I → Prop) (hΩ : Upward Ω)
    (i : I) (E : Finset I) :
    gradient i (indicator Ω) E = 0 ∨ gradient i (indicator Ω) E = 1 := by
  classical
  have h := hΩ (E.erase i) (insert i E)
    ((Finset.erase_subset i E).trans (Finset.subset_insert i E))
  unfold gradient indicator
  split_ifs <;> simp_all

end ExpandingCodes.SharpThreshold

end FlattenModule122

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.Scalar -/
section FlattenModule123

/-!
# Uniform scalar two-point contraction

The proof uses a polynomial strong-convexity bound for signed cubes, followed
by max-norm normalization. All statements remain the provisional Boolean
analysis interfaces defined in `Basic`; no code-capacity assertion is assumed.
-/

set_option autoImplicit false
namespace ExpandingCodes.SharpThreshold

/-- The tangent gap of the fourth power, parametrized by signed cubes.
Factoring out `(u-v)^2` reduces the bound to two quadratic inequalities. -/
lemma cube_tangent_bound (u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    (u ^ 3 - v ^ 3) ^ 2 / 18 ≤
      u ^ 4 - v ^ 4 - (4 / 3 : ℝ) * v * (u ^ 3 - v ^ 3) := by
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_abs u, mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ |u| + 1 by positivity)]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith [sq_abs v, mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ |v| + 1 by positivity)]
  have hQ0 : 0 ≤ u ^ 2 + u * v + v ^ 2 := by nlinarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]
  have hQ3 : u ^ 2 + u * v + v ^ 2 ≤ 3 := by nlinarith [sq_nonneg (u - v)]
  have hQ2 : (u ^ 2 + u * v + v ^ 2) ^ 2 ≤ 3 * (u ^ 2 + u * v + v ^ 2) := by
    nlinarith [mul_nonneg hQ0 (sub_nonneg.mpr hQ3)]
  have hH : (u ^ 2 + u * v + v ^ 2) / 6 ≤ u ^ 2 + (2 / 3 : ℝ) * u * v + v ^ 2 / 3 := by
    nlinarith [sq_nonneg (3 * u + v), sq_nonneg u, sq_nonneg v]
  have h := mul_nonneg (sq_nonneg (u - v)) (show 0 ≤
    u ^ 2 + (2 / 3 : ℝ) * u * v + v ^ 2 / 3 -
      (u ^ 2 + u * v + v ^ 2) ^ 2 / 18 by linarith)
  nlinarith only [h]
/-- Signed cube roots cover the unit interval and turn the fractional power
into an ordinary fourth power. -/
lemma exists_bounded_cube (x : ℝ) (hx : |x| ≤ 1) :
    ∃ u : ℝ, |u| ≤ 1 ∧ u ^ 3 = x ∧ u ^ 4 = |x| ^ (4 / 3 : ℝ) := by
  let t := |x| ^ (1 / 3 : ℝ)
  have ht0 : 0 ≤ t := Real.rpow_nonneg (abs_nonneg x) _
  have ht1 : t ≤ 1 := Real.rpow_le_one (abs_nonneg x) hx (by norm_num)
  have ht3 : t ^ 3 = |x| := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast (abs_nonneg x)]
    norm_num
  have ht4 : t ^ 4 = |x| ^ (4 / 3 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast (abs_nonneg x)]
    norm_num
  rcases le_total 0 x with h | h
  · exact ⟨t, by rwa [abs_of_nonneg ht0], by simpa [abs_of_nonneg h] using ht3, ht4⟩
  · refine ⟨-t, by simpa [abs_of_nonneg ht0] using ht1, ?_, ?_⟩
    · rw [abs_of_nonpos h] at ht3
      nlinarith only [ht3]
    · convert ht4 using 1; ring

/-- A uniform supporting quadratic for the `4/3` power on `[-1,1]`. -/
lemma bounded_rpow_tangent (y : ℝ) (hy : |y| ≤ 1) :
    ∃ d : ℝ, ∀ x : ℝ, |x| ≤ 1 →
      (x-y)^2 / 18 ≤ |x| ^ (4/3 : ℝ) - |y| ^ (4/3 : ℝ) - d*(x-y) := by
  obtain ⟨v, hv, hv3, hv4⟩ := exists_bounded_cube y hy
  refine ⟨(4/3:ℝ)*v, ?_⟩
  intro x hx
  obtain ⟨u, hu, hu3, hu4⟩ := exists_bounded_cube x hx
  simpa [hu3, hv3, hu4, hv4] using cube_tangent_bound u v hu hv

/-- The weighted Jensen gap controls the two-point variance. -/
lemma bounded_rpow_jensen (p x y : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |(1-p)*x+p*y| ^ (4/3 : ℝ) + p*(1-p)*(x-y)^2/18 ≤
      (1-p)*|x| ^ (4/3 : ℝ) + p*|y| ^ (4/3 : ℝ) := by
  have hm : |(1-p)*x+p*y| ≤ 1 := calc
    _ ≤ |(1-p)*x| + |p*y| := abs_add_le _ _
    _ = (1-p)*|x| + p*|y| := by rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp1), abs_of_nonneg hp]
    _ ≤ (1-p)*1+p*1 := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hp1)) (mul_le_mul_of_nonneg_left hy hp)
    _ = 1 := by ring
  obtain ⟨d, hd⟩ := bounded_rpow_tangent ((1-p)*x+p*y) hm
  have hdx := mul_le_mul_of_nonneg_left (hd x hx) (sub_nonneg.mpr hp1)
  have hdy := mul_le_mul_of_nonneg_left (hd y hy) hp
  nlinarith only [hdx, hdy]
lemma rpow_three_halves (t : ℝ) (ht : 0 ≤ t) :
    t ^ (3/2 : ℝ) = t * Real.sqrt t := by
  rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add' ht (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- A square-root factor transfers a gap through the `3/2` power. -/
lemma rpow_gap (A B δ : ℝ) (hB : 0 ≤ B) (hBA : B ≤ A) (hδ : δ ≤ A) :
    Real.sqrt δ * (A-B) ≤ A ^ (3/2:ℝ) - B ^ (3/2:ℝ) := by
  rw [rpow_three_halves A (hB.trans hBA), rpow_three_halves B hB]
  have h1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBA) hB
  have h2 := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hδ) (sub_nonneg.mpr hBA)
  nlinarith only [h1, h2]

/-- Bounded-input contraction from the Jensen gap and a lower moment bound. -/
lemma bounded_noise_contraction (p r δ x y : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hδ : δ ≤ (1-p)*|x| ^ (4/3:ℝ) + p*|y| ^ (4/3:ℝ))
    (hr : r^2 ≤ Real.sqrt δ / 18) :
    (1-p)*(((1-p)*x+p*y)+r*(x-((1-p)*x+p*y)))^2 +
      p*(((1-p)*x+p*y)+r*(y-((1-p)*x+p*y)))^2 ≤
      ((1-p)*|x| ^ (4/3:ℝ)+p*|y| ^ (4/3:ℝ)) ^ (3/2:ℝ) := by
  let m := (1-p)*x+p*y
  let A := (1-p)*|x| ^ (4/3:ℝ)+p*|y| ^ (4/3:ℝ)
  have hp0 : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hv : 0 ≤ p*(1-p)*(x-y)^2 := by positivity
  have hj := bounded_rpow_jensen p x y hp hp1 hx hy
  change |m| ^ (4/3:ℝ) + p*(1-p)*(x-y)^2/18 ≤ A at hj
  have hB : 0 ≤ |m| ^ (4/3:ℝ) := Real.rpow_nonneg (abs_nonneg m) _
  have hBA : |m| ^ (4/3:ℝ) ≤ A := by linarith
  have hg := rpow_gap A (|m| ^ (4/3:ℝ)) δ hB hBA hδ
  have hm : (|m| ^ (4/3:ℝ)) ^ (3/2:ℝ) = m^2 := by
    rw [← Real.rpow_mul (abs_nonneg m)]
    norm_num [sq_abs]
  rw [hm] at hg
  have hJ := mul_le_mul_of_nonneg_left hj (Real.sqrt_nonneg δ)
  have hR := mul_le_mul_of_nonneg_right hr hv
  have heq :
    (1-p)*(((1-p)*x+p*y)+r*(x-((1-p)*x+p*y)))^2 +
      p*(((1-p)*x+p*y)+r*(y-((1-p)*x+p*y)))^2 = m^2+r^2*(p*(1-p)*(x-y)^2) := by dsimp [m]; ring
  rw [heq]
  change m^2+r^2*(p*(1-p)*(x-y)^2) ≤ A ^ (3/2:ℝ)
  nlinarith only [hg, hJ, hR]
/-- Normalize by the maximum absolute value, apply bounded contraction, and
rescale. One normalized coordinate has absolute value one, so the moment is
at least either atom weight. -/
lemma two_point_of_sq_le (p r δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hδp : δ ≤ p) (hδq : δ ≤ 1-p) (hr : r^2 ≤ Real.sqrt δ / 18) :
    TwoPointContraction p r := by
  intro x y
  let M := max |x| |y|
  have hM0 : 0 ≤ M := (abs_nonneg x).trans (le_max_left _ _)
  by_cases hM : M = 0
  · have hxbound : |x| ≤ M := le_max_left _ _
    have hybound : |y| ≤ M := le_max_right _ _
    have hx : x = 0 := abs_eq_zero.mp (le_antisymm (hM ▸ hxbound) (abs_nonneg x))
    have hy : y = 0 := abs_eq_zero.mp (le_antisymm (hM ▸ hybound) (abs_nonneg y))
    subst x; subst y
    norm_num
  have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
  have hx : |x/M| ≤ 1 := by rw [abs_div, abs_of_pos hMpos]; exact (div_le_one hMpos).mpr (le_max_left _ _)
  have hy : |y/M| ≤ 1 := by rw [abs_div, abs_of_pos hMpos]; exact (div_le_one hMpos).mpr (le_max_right _ _)
  have hp0 : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hnorm : δ ≤ (1-p)*|x/M| ^ (4/3:ℝ)+p*|y/M| ^ (4/3:ℝ) := by
    rcases le_total |x| |y| with hxy | hyx
    · have heq : |y/M| = 1 := by
        rw [abs_div, abs_of_pos hMpos, show M = |y| from max_eq_right hxy]
        apply div_self
        simpa only [M, max_eq_right hxy] using hM
      rw [heq, Real.one_rpow, mul_one]
      exact hδp.trans (le_add_of_nonneg_left (by positivity))
    · have heq : |x/M| = 1 := by
        rw [abs_div, abs_of_pos hMpos, show M = |x| from max_eq_left hyx]
        apply div_self
        simpa only [M, max_eq_left hyx] using hM
      rw [heq, Real.one_rpow, mul_one]
      exact hδq.trans (le_add_of_nonneg_right (by positivity))
  have h := bounded_noise_contraction p r δ (x/M) (y/M) hp hp1 hx hy hnorm hr
  have hleft :
    (1-p)*(((1-p)*(x/M)+p*(y/M))+r*((x/M)-((1-p)*(x/M)+p*(y/M))))^2 +
      p*(((1-p)*(x/M)+p*(y/M))+r*((y/M)-((1-p)*(x/M)+p*(y/M))))^2 =
    ((1-p)*(((1-p)*x+p*y)+r*(x-((1-p)*x+p*y)))^2 +
      p*(((1-p)*x+p*y)+r*(y-((1-p)*x+p*y)))^2) / M^2 := by
    field_simp
  have hmoment : (1-p)*|x/M| ^ (4/3:ℝ)+p*|y/M| ^ (4/3:ℝ) =
      ((1-p)*|x| ^ (4/3:ℝ)+p*|y| ^ (4/3:ℝ)) / M ^ (4/3:ℝ) := by
    rw [abs_div, abs_div, abs_of_pos hMpos,
      Real.div_rpow (abs_nonneg x) hM0, Real.div_rpow (abs_nonneg y) hM0]
    ring
  have hmom0 : 0 ≤ (1-p)*|x| ^ (4/3:ℝ)+p*|y| ^ (4/3:ℝ) := by positivity
  rw [hleft, hmoment, Real.div_rpow hmom0 (Real.rpow_nonneg hM0 _),
    ← Real.rpow_mul hM0] at h
  norm_num at h
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hMpos)).mp h

/-- Uniform scalar contraction on a compact subinterval of `(0,1)`.
An explicit admissible choice is `r = sqrt (sqrt (min a (1-b)) / 18)`. -/
theorem two_point_uniform (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ p ∈ Set.Icc a b, TwoPointContraction p r := by
  let δ := min a (1-b)
  have hδ : 0 < δ := lt_min ha (by linarith)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by linarith)
  let r := Real.sqrt (Real.sqrt δ / 18)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r^2 = Real.sqrt δ / 18 := Real.sq_sqrt (by positivity)
  have hr1 : r < 1 := by
    have hs : Real.sqrt δ ≤ 1 := by simpa using Real.sqrt_le_sqrt hδ1
    nlinarith [hr2]
  refine ⟨r, hr0, hr1, ?_⟩
  intro p hp
  apply two_point_of_sq_le p r δ (by linarith [hp.1]) (by linarith [hp.2])
  · exact (min_le_left _ _).trans hp.1
  · exact (min_le_right _ _).trans (by linarith [hp.2])
  · exact hr2.le
end ExpandingCodes.SharpThreshold

end FlattenModule123

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.ProductNoise -/
section FlattenModule124



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]

/-- Finite product kernel form of biased noise. -/
noncomputable def productNoiseOn (s : Finset I) (p r : ℝ)
    (f : Finset I → ℝ) (E : Finset I) : ℝ :=
  expectationOn s p (fun F => f F * ∏ i ∈ s,
    (1 + r * coordinate p i E * coordinate p i F))

lemma noise_character_kernel (p r : ℝ) (E F : Finset I) :
    (∑ S : Finset I, r ^ S.card * character p S E * character p S F) =
      ∏ i : I, (1 + r * coordinate p i E * coordinate p i F) := by
  classical
  have hterm : ∀ S : Finset I,
      r ^ S.card * character p S E * character p S F =
      ∏ i ∈ S, (r * coordinate p i E * coordinate p i F) := by
    intro S
    simp only [character, Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hterm]
  symm
  simpa using (Finset.prod_one_add (f := fun i : I =>
    r * coordinate p i E * coordinate p i F) Finset.univ)

lemma noise_eq_productNoiseOn_univ (p r : ℝ) (f : Finset I → ℝ) (E : Finset I) :
    noise p r f E = productNoiseOn Finset.univ p r f E := by
  classical
  unfold noise fourier productNoiseOn
  rw [expectationOn_univ]
  unfold expectation
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F _
  rw [← noise_character_kernel]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

lemma rpow_three_halves_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = x := by
  rw [← Real.rpow_mul hx]
  norm_num

lemma rpow_two_thirds_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = x := by
  rw [← Real.rpow_mul hx]
  norm_num

/-- Weighted finite Minkowski at the mixed-norm exponent `2/(4/3)`. -/
lemma weighted_minkowski_three_halves {J : Type*} (s : Finset J)
    (w a b : J → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (ha : ∀ j ∈ s, 0 ≤ a j) (hb : ∀ j ∈ s, 0 ≤ b j) :
    (∑ j ∈ s, w j * (a j + b j) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      (∑ j ∈ s, w j * a j ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) +
      (∑ j ∈ s, w j * b j ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  have hpow : ∀ j ∈ s, ∀ x : ℝ, 0 ≤ x →
      (w j ^ (2 / 3 : ℝ) * x) ^ (3 / 2 : ℝ) = w j * x ^ (3 / 2 : ℝ) := by
    intro j hj x hx
    rw [Real.mul_rpow (Real.rpow_nonneg (hw j hj) _) hx,
      rpow_two_thirds_three_halves (hw j hj)]
  have h := Real.Lp_add_le_of_nonneg s
    (f := fun j => w j ^ (2 / 3 : ℝ) * a j)
    (g := fun j => w j ^ (2 / 3 : ℝ) * b j)
    (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    (fun j hj => mul_nonneg (Real.rpow_nonneg (hw j hj) _) (ha j hj))
    (fun j hj => mul_nonneg (Real.rpow_nonneg (hw j hj) _) (hb j hj))
  norm_num only [show (1 / (3 / 2) : ℝ) = 2 / 3 by norm_num] at h
  have hleft : (∑ j ∈ s, (w j ^ (2 / 3 : ℝ) * a j +
      w j ^ (2 / 3 : ℝ) * b j) ^ (3 / 2 : ℝ)) =
      ∑ j ∈ s, w j * (a j + b j) ^ (3 / 2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_add, hpow j hj (a j + b j) (add_nonneg (ha j hj) (hb j hj))]
  have ha' : (∑ j ∈ s, (w j ^ (2 / 3 : ℝ) * a j) ^ (3 / 2 : ℝ)) =
      ∑ j ∈ s, w j * a j ^ (3 / 2 : ℝ) :=
    Finset.sum_congr rfl (fun j hj => hpow j hj (a j) (ha j hj))
  have hb' : (∑ j ∈ s, (w j ^ (2 / 3 : ℝ) * b j) ^ (3 / 2 : ℝ)) =
      ∑ j ∈ s, w j * b j ^ (3 / 2 : ℝ) :=
    Finset.sum_congr rfl (fun j hj => hpow j hj (b j) (hb j hj))
  rwa [hleft, ha', hb'] at h

/-- The finite mixed-norm interchange used in a single tensorization step. -/
lemma weighted_mixed_norm {J : Type*} (s : Finset J) (w a b : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (ha : ∀ j ∈ s, 0 ≤ a j)
    (hb : ∀ j ∈ s, 0 ≤ b j) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (∑ j ∈ s, w j * (α * a j ^ (2 / 3 : ℝ) + β * b j ^ (2 / 3 : ℝ)) ^
      (3 / 2 : ℝ)) ≤
      (α * (∑ j ∈ s, w j * a j) ^ (2 / 3 : ℝ) +
        β * (∑ j ∈ s, w j * b j) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
  have hroot : ∀ (c : ℝ) (hc : 0 ≤ c) (v : J → ℝ)
      (hv : ∀ j ∈ s, 0 ≤ v j),
      (∑ j ∈ s, w j * (c * v j ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) = c * (∑ j ∈ s, w j * v j) ^ (2 / 3 : ℝ) := by
    intro c hc v hv
    have hsum : (∑ j ∈ s, w j * (c * v j ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) =
        c ^ (3 / 2 : ℝ) * ∑ j ∈ s, w j * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.mul_rpow hc (Real.rpow_nonneg (hv j hj) _),
        rpow_two_thirds_three_halves (hv j hj)]
      ring
    rw [hsum, Real.mul_rpow (Real.rpow_nonneg hc _)
      (Finset.sum_nonneg (fun j hj => mul_nonneg (hw j hj) (hv j hj))),
      rpow_three_halves_two_thirds hc]
  have h := weighted_minkowski_three_halves s w
    (fun j => α * a j ^ (2 / 3 : ℝ)) (fun j => β * b j ^ (2 / 3 : ℝ)) hw
    (fun j hj => mul_nonneg hα (Real.rpow_nonneg (ha j hj) _))
    (fun j hj => mul_nonneg hβ (Real.rpow_nonneg (hb j hj) _))
  rw [hroot α hα a ha, hroot β hβ b hb] at h
  have hleft : 0 ≤ ∑ j ∈ s, w j *
      (α * a j ^ (2 / 3 : ℝ) + β * b j ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hw j hj) (Real.rpow_nonneg
      (add_nonneg (mul_nonneg hα (Real.rpow_nonneg (ha j hj) _))
        (mul_nonneg hβ (Real.rpow_nonneg (hb j hj) _))) _)
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg hleft _) h
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  rwa [rpow_two_thirds_three_halves hleft] at h'

lemma abs_rpow_four_thirds (x : ℝ) :
    |x| ^ (4 / 3 : ℝ) = (x ^ 2) ^ (2 / 3 : ℝ) := by
  rw [← sq_abs x, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  norm_num

lemma expectationOn_congr (s : Finset I) (p : ℝ) {f g : Finset I → ℝ}
    (hfg : ∀ E ∈ s.powerset, f E = g E) : expectationOn s p f = expectationOn s p g := by
  unfold expectationOn
  apply Finset.sum_congr rfl
  intro E hE
  rw [hfg E hE]

lemma expectationOn_add (s : Finset I) (p : ℝ) (f g : Finset I → ℝ) :
    expectationOn s p (fun E => f E + g E) = expectationOn s p f + expectationOn s p g := by
  simp [expectationOn, mul_add, Finset.sum_add_distrib]

lemma expectationOn_mul_left (s : Finset I) (p a : ℝ) (f : Finset I → ℝ) :
    expectationOn s p (fun E => a * f E) = a * expectationOn s p f := by
  simp only [expectationOn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E _
  ring

lemma expectationOn_nonneg (s : Finset I) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {f : Finset I → ℝ} (hf : ∀ E ∈ s.powerset, 0 ≤ f E) :
    0 ≤ expectationOn s p f := by
  rw [← expectationOn_const s p 0]
  exact expectationOn_mono hp hp' hf

lemma coordinate_insert_of_ne (p : ℝ) {i j : I} (hji : j ≠ i) (E : Finset I) :
    coordinate p j (insert i E) = coordinate p j E := by
  classical
  simp [coordinate, hji]

lemma productNoiseOn_insert_coordinate (s : Finset I) (p r : ℝ)
    (f : Finset I → ℝ) {i : I} (hi : i ∉ s) (E : Finset I) :
    productNoiseOn s p r f (insert i E) = productNoiseOn s p r f E := by
  classical
  apply expectationOn_congr
  intro F _
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [coordinate_insert_of_ne p (show j ≠ i from fun hji => hi (hji ▸ hj))]

lemma productNoiseOn_insert (s : Finset I) (p r : ℝ)
    (f : Finset I → ℝ) {i : I} (hi : i ∉ s) (E : Finset I) :
    productNoiseOn (insert i s) p r f E =
      (1 - p) * (1 + r * coordinate p i E * coordinate p i ∅) *
        productNoiseOn s p r f E +
      p * (1 + r * coordinate p i E * coordinate p i {i}) *
        productNoiseOn s p r (fun F => f (insert i F)) E := by
  classical
  unfold productNoiseOn
  rw [expectationOn_insert hi]
  have hfirst : expectationOn s p
      (fun F => f F * ∏ j ∈ insert i s, (1 + r * coordinate p j E * coordinate p j F)) =
      (1 + r * coordinate p i E * coordinate p i ∅) * expectationOn s p
        (fun F => f F * ∏ j ∈ s, (1 + r * coordinate p j E * coordinate p j F)) := by
    rw [← expectationOn_mul_left]
    apply expectationOn_congr
    intro F hF
    have hiF : i ∉ F := fun h => hi (Finset.mem_powerset.mp hF h)
    rw [Finset.prod_insert hi]
    simp only [coordinate, hiF, Finset.notMem_empty, if_false]
    ring
  have hsecond : expectationOn s p
      (fun F => f (insert i F) * ∏ j ∈ insert i s,
        (1 + r * coordinate p j E * coordinate p j (insert i F))) =
      (1 + r * coordinate p i E * coordinate p i {i}) * expectationOn s p
        (fun F => f (insert i F) * ∏ j ∈ s,
          (1 + r * coordinate p j E * coordinate p j F)) := by
    rw [← expectationOn_mul_left]
    apply expectationOn_congr
    intro F _
    rw [Finset.prod_insert hi]
    have hprod : (∏ j ∈ s, (1 + r * coordinate p j E * coordinate p j (insert i F))) =
        ∏ j ∈ s, (1 + r * coordinate p j E * coordinate p j F) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [coordinate_insert_of_ne p (show j ≠ i from fun hji => hi (hji ▸ hj))]
    rw [hprod]
    simp only [coordinate, Finset.mem_insert_self, Finset.mem_singleton_self, if_true]
    ring
  rw [hfirst, hsecond]
  ring

lemma coordinate_mul_eq (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (i : I) (E F : Finset I) :
    coordinate p i E * coordinate p i F =
      (((if i ∈ E then 1 else 0) - p) * ((if i ∈ F then 1 else 0) - p)) /
        (p * (1 - p)) := by
  classical
  unfold coordinate
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp'.le))]

lemma kernel_two_point (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (h : TwoPointContraction p r) {i : I} (E : Finset I) (hiE : i ∉ E) (x y : ℝ) :
    (1 - p) * ((1 - p) * (1 + r * coordinate p i E * coordinate p i ∅) * x +
      p * (1 + r * coordinate p i E * coordinate p i {i}) * y) ^ 2 +
    p * ((1 - p) * (1 + r * coordinate p i (insert i E) * coordinate p i ∅) * x +
      p * (1 + r * coordinate p i (insert i E) * coordinate p i {i}) * y) ^ 2 ≤
      ((1 - p) * |x| ^ (4 / 3 : ℝ) + p * |y| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp1 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp')
  have h0 : (1 - p) * (1 + r * coordinate p i E * coordinate p i ∅) * x +
      p * (1 + r * coordinate p i E * coordinate p i {i}) * y =
      ((1 - p) * x + p * y) + r * (x - ((1 - p) * x + p * y)) := by
    simp only [mul_assoc r, coordinate_mul_eq p hp hp', hiE,
      Finset.notMem_empty, Finset.mem_singleton_self, if_false, if_true]
    field_simp [hp0, hp1]
    ring
  have h1 : (1 - p) * (1 + r * coordinate p i (insert i E) * coordinate p i ∅) * x +
      p * (1 + r * coordinate p i (insert i E) * coordinate p i {i}) * y =
      ((1 - p) * x + p * y) + r * (y - ((1 - p) * x + p * y)) := by
    simp only [mul_assoc r, coordinate_mul_eq p hp hp', Finset.mem_insert_self,
      Finset.notMem_empty, Finset.mem_singleton_self, if_false, if_true]
    field_simp [hp0, hp1]
    ring
  rw [h0, h1]
  exact h x y

lemma expectationOn_mixed_norm (s : Finset I) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (u v : Finset I → ℝ) :
    expectationOn s p (fun E =>
      ((1 - p) * |u E| ^ (4 / 3 : ℝ) + p * |v E| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ)) ≤
      ((1 - p) * (expectationOn s p (fun E => u E ^ 2)) ^ (2 / 3 : ℝ) +
        p * (expectationOn s p (fun E => v E ^ 2)) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
  simp_rw [abs_rpow_four_thirds]
  exact weighted_mixed_norm s.powerset
    (fun E => p ^ E.card * (1 - p) ^ (s.card - E.card))
    (fun E => u E ^ 2) (fun E => v E ^ 2)
    (fun E _ => mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _))
    (fun E _ => sq_nonneg _) (fun E _ => sq_nonneg _)
    (sub_nonneg.mpr hp') hp

/-- Tensorization of the scalar inequality for an arbitrary finite coordinate product. -/
theorem productNoiseOn_contract (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (h : TwoPointContraction p r) (s : Finset I) (f : Finset I → ℝ) :
    expectationOn s p (fun E => productNoiseOn s p r f E ^ 2) ≤
      (expectationOn s p (fun E => |f E| ^ (4 / 3 : ℝ))) ^ (3 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    simp only [productNoiseOn, expectationOn, Finset.powerset_empty,
      Finset.sum_singleton, Finset.card_empty, pow_zero, zero_tsub, mul_one, one_mul,
      Finset.prod_empty]
    rw [← Real.rpow_mul (abs_nonneg (f ∅))]
    norm_num [sq_abs]
  | @insert i s hi ih =>
    let u : Finset I → ℝ := productNoiseOn s p r f
    let v : Finset I → ℝ := productNoiseOn s p r (fun F => f (insert i F))
    have hnonneg : ∀ g : Finset I → ℝ,
        0 ≤ expectationOn s p (fun E => |g E| ^ (4 / 3 : ℝ)) := by
      intro g
      exact expectationOn_nonneg s hp.le hp'.le
        (fun E _ => Real.rpow_nonneg (abs_nonneg _) _)
    have hroot_u : (expectationOn s p (fun E => u E ^ 2)) ^ (2 / 3 : ℝ) ≤
        expectationOn s p (fun E => |f E| ^ (4 / 3 : ℝ)) := by
      have hroot := Real.rpow_le_rpow
        (expectationOn_nonneg s hp.le hp'.le (fun E _ => sq_nonneg (u E)))
        (ih f) (show (0 : ℝ) ≤ 2 / 3 by norm_num)
      rwa [rpow_three_halves_two_thirds (hnonneg f)] at hroot
    have hroot_v : (expectationOn s p (fun E => v E ^ 2)) ^ (2 / 3 : ℝ) ≤
        expectationOn s p (fun E => |f (insert i E)| ^ (4 / 3 : ℝ)) := by
      have hroot := Real.rpow_le_rpow
        (expectationOn_nonneg s hp.le hp'.le (fun E _ => sq_nonneg (v E)))
        (ih (fun F => f (insert i F))) (show (0 : ℝ) ≤ 2 / 3 by norm_num)
      rwa [rpow_three_halves_two_thirds (hnonneg (fun F => f (insert i F)))] at hroot
    calc
      expectationOn (insert i s) p (fun E => productNoiseOn (insert i s) p r f E ^ 2) =
          expectationOn s p (fun E =>
            (1 - p) * productNoiseOn (insert i s) p r f E ^ 2 +
              p * productNoiseOn (insert i s) p r f (insert i E) ^ 2) := by
        rw [expectationOn_insert hi, expectationOn_add,
          expectationOn_mul_left, expectationOn_mul_left]
      _ ≤ expectationOn s p (fun E =>
          ((1 - p) * |u E| ^ (4 / 3 : ℝ) + p * |v E| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ)) := by
        apply expectationOn_mono hp.le hp'.le
        intro E hE
        have hiE : i ∉ E := fun h => hi (Finset.mem_powerset.mp hE h)
        rw [productNoiseOn_insert s p r f hi E,
          productNoiseOn_insert s p r f hi (insert i E),
          productNoiseOn_insert_coordinate s p r f hi E,
          productNoiseOn_insert_coordinate s p r (fun F => f (insert i F)) hi E]
        exact kernel_two_point p r hp hp' h E hiE (u E) (v E)
      _ ≤ ((1 - p) * (expectationOn s p (fun E => u E ^ 2)) ^ (2 / 3 : ℝ) +
          p * (expectationOn s p (fun E => v E ^ 2)) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
        expectationOn_mixed_norm s hp.le hp'.le u v
      _ ≤ ((1 - p) * expectationOn s p (fun E => |f E| ^ (4 / 3 : ℝ)) +
          p * expectationOn s p (fun E => |f (insert i E)| ^ (4 / 3 : ℝ))) ^
            (3 / 2 : ℝ) := by
        apply Real.rpow_le_rpow
        · exact add_nonneg
            (mul_nonneg (sub_nonneg.mpr hp'.le) (Real.rpow_nonneg
              (expectationOn_nonneg s hp.le hp'.le (fun E _ => sq_nonneg _)) _))
            (mul_nonneg hp.le (Real.rpow_nonneg
              (expectationOn_nonneg s hp.le hp'.le (fun E _ => sq_nonneg _)) _))
        · exact add_le_add
            (mul_le_mul_of_nonneg_left hroot_u (sub_nonneg.mpr hp'.le))
            (mul_le_mul_of_nonneg_left hroot_v hp.le)
        · norm_num
      _ = (expectationOn (insert i s) p (fun E => |f E| ^ (4 / 3 : ℝ))) ^
          (3 / 2 : ℝ) := by rw [expectationOn_insert hi]

end ExpandingCodes.SharpThreshold

end FlattenModule124

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.Tensorization -/
section FlattenModule125


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Finite tensorization, conditional on the scalar inequality. -/
theorem tensorize_two_point (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (h : TwoPointContraction p r)
    (f : Finset I → ℝ) :
    expectation p (fun E => noise p r f E ^ 2) ≤
      (expectation p (fun E => |f E| ^ (4 / 3 : ℝ))) ^ (3 / 2 : ℝ) := by
  simpa only [expectationOn_univ, ← noise_eq_productNoiseOn_univ] using
    productNoiseOn_contract p r hp hp' h Finset.univ f

end ExpandingCodes.SharpThreshold

end FlattenModule125

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.FourierBasis -/
section FlattenModule126




/-! Finite biased Fourier analysis from an explicit tensor-product delta kernel. -/

set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]

/-- Bernoulli pattern weights factor into their one-coordinate weights. -/
lemma patternWeight_prod (p : ℝ) (E : Finset I) :
    patternWeight p E = ∏ i : I, if i ∈ E then p else 1-p := by
  classical
  simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter, patternWeight]
  congr 2
  have h : Finset.univ.filter (fun x => x ∉ E) = Eᶜ := by ext; simp
  rw [h, Finset.card_compl]

/-- Summing characters factors into independent one-coordinate kernels. -/
lemma character_kernel (p : ℝ) (E F : Finset I) :
    (∑ S : Finset I, character p S E * character p S F) =
      ∏ i : I, (1 + coordinate p i E * coordinate p i F) := by
  classical
  simp_rw [character, ← Finset.prod_mul_distrib]
  symm
  simpa using (Finset.prod_one_add (f := fun i => coordinate p i E * coordinate p i F) (Finset.univ : Finset I))

omit [Fintype I] in
/-- The weighted one-coordinate character kernel is the delta function. -/
lemma coordinate_kernel (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (i : I) (E F : Finset I) :
    (if i ∈ F then p else 1-p) *
      (1 + coordinate p i E * coordinate p i F) =
      if (i ∈ E ↔ i ∈ F) then 1 else 0 := by
  classical
  have h : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp')
  have hs : Real.sqrt (p * (1-p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
  have hsq := Real.sq_sqrt h.le
  unfold coordinate
  by_cases hiE : i ∈ E <;> by_cases hiF : i ∈ F <;>
    simp only [hiE, hiF, if_true, if_false, iff_true, iff_false, iff_self, not_true_eq_false, zero_sub] <;>
    field_simp [hs] <;> nlinarith [hsq, congrArg (fun t : ℝ => p * t) hsq]

/-- The weighted full character kernel is the delta function. -/
lemma weighted_character_kernel (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (E F : Finset I) :
    patternWeight p F * (∑ S : Finset I, character p S E * character p S F) =
      if E = F then 1 else 0 := by
  classical
  rw [character_kernel, patternWeight_prod, ← Finset.prod_mul_distrib]
  simp_rw [coordinate_kernel p hp hp']
  by_cases hEF : E = F
  · simp [hEF]
  · rw [if_neg hEF]
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => hEF (Finset.ext h))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Distinct biased characters are orthogonal and every character has norm one. -/
lemma character_orthogonality (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (S T : Finset I) :
    expectation p (fun E => character p S E * character p T E) =
      if S = T then 1 else 0 := by
  classical
  let M : Matrix (Finset I) (Finset I) ℝ := fun E S => character p S E
  let N : Matrix (Finset I) (Finset I) ℝ :=
    fun S E => patternWeight p E * character p S E
  have hMN : M * N = 1 := by
    ext E F
    change (∑ S : Finset I, character p S E *
      (patternWeight p F * character p S F)) = if E = F then 1 else 0
    rw [← weighted_character_kernel p hp hp' E F, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  have hNM : N * M = 1 := mul_eq_one_comm.mp hMN
  have h := congrArg (fun A : Matrix (Finset I) (Finset I) ℝ => A S T) hNM
  change (∑ E : Finset I, patternWeight p E * character p S E *
      character p T E) = if S = T then 1 else 0 at h
  simpa only [expectation, mul_assoc] using h

/-- Every Boolean function has its finite biased Fourier expansion. -/
lemma fourier_inversion (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (E : Finset I) :
    (∑ S : Finset I, fourier p f S * character p S E) = f E := by
  classical
  calc
    _ = ∑ F : Finset I, f F * (patternWeight p F *
        ∑ S : Finset I, character p S E * character p S F) := by
      unfold fourier expectation
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro F _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ∑ F : Finset I, if E = F then f F else 0 := by
      apply Finset.sum_congr rfl
      intro F _
      rw [weighted_character_kernel p hp hp']
      split_ifs <;> simp
    _ = f E := by simp

/-- Bilinear Parseval for the explicitly defined biased Fourier coefficients. -/
lemma fourier_inner_product (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f g : Finset I → ℝ) :
    expectation p (fun E => f E * g E) =
      ∑ S : Finset I, fourier p f S * fourier p g S := by
  classical
  symm
  calc
    _ = ∑ E : Finset I, patternWeight p E * f E *
        (∑ S : Finset I, fourier p g S * character p S E) := by
      change (∑ S : Finset I,
        (∑ E : Finset I, patternWeight p E * (f E * character p S E)) *
          fourier p g S) = _
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = expectation p (fun E => f E * g E) := by
      simp_rw [fourier_inversion p hp hp']
      unfold expectation
      apply Finset.sum_congr rfl
      intro E _
      ring

@[simp] lemma fourier_empty (p : ℝ) (f : Finset I → ℝ) :
    fourier p f ∅ = expectation p f := by
  simp [fourier, character]

end ExpandingCodes.SharpThreshold

end FlattenModule126

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.Parseval -/
section FlattenModule127


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- The variance is the sum of squares of all nonconstant Fourier coefficients. -/
theorem fourier_parseval (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) :
    variance p f = ∑ S : Finset I, if S.Nonempty then fourier p f S ^ 2 else 0 := by
  classical
  have hfull : expectation p (fun E => f E ^ 2) =
      ∑ S : Finset I, fourier p f S ^ 2 := by
    simpa only [pow_two] using fourier_inner_product p hp hp' f f
  have hsplit : (∑ S : Finset I, fourier p f S ^ 2) =
      (∑ S : Finset I, if S.Nonempty then fourier p f S ^ 2 else 0) +
        (expectation p f) ^ 2 := by
    rw [← fourier_empty p f]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset I))]
    congr 1
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext S
      simp [Finset.nonempty_iff_ne_empty]
    · intro S _
      rfl
  unfold variance
  rw [hfull, hsplit]
  ring
end ExpandingCodes.SharpThreshold

end FlattenModule127

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.GradientFourier -/
section FlattenModule128


/-! Finite coordinate-gradient and noise identities in the explicit biased Fourier basis. -/

set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma character_insert_of_not_mem (p : ℝ) {i : I} {S : Finset I} (hi : i ∉ S)
    (E : Finset I) : character p S (insert i E) = character p S E := by
  classical
  unfold character
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [coordinate, hji]

omit [Fintype I] in
lemma character_erase_of_not_mem (p : ℝ) {i : I} {S : Finset I} (hi : i ∉ S)
    (E : Finset I) : character p S (E.erase i) = character p S E := by
  classical
  unfold character
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [coordinate, hji]

omit [Fintype I] in
lemma gradient_character (p : ℝ) (i : I) (S E : Finset I) :
    gradient i (character p S) E =
      if i ∈ S then character p (S.erase i) E / Real.sqrt (p * (1-p)) else 0 := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hc (F : Finset I) : character p S F =
        coordinate p i F * character p (S.erase i) F :=
      (Finset.mul_prod_erase S (fun j => coordinate p j F) hi).symm
    simp only [gradient, hc, character_insert_of_not_mem p (Finset.notMem_erase i S),
      character_erase_of_not_mem p (Finset.notMem_erase i S)]
    simp only [coordinate, Finset.mem_insert_self, Finset.notMem_erase, if_true, if_false]
    ring
  · simp [hi, gradient, character_insert_of_not_mem p hi, character_erase_of_not_mem p hi]

lemma fourier_gradient_sum (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (i : I) (T : Finset I) :
    fourier p (gradient i f) T =
      ∑ S : Finset I, if i ∈ S ∧ S.erase i = T then
        fourier p f S / Real.sqrt (p * (1-p)) else 0 := by
  classical
  have hexpand (E : Finset I) : gradient i f E =
      ∑ S : Finset I, fourier p f S * gradient i (character p S) E := by
    unfold gradient
    rw [← fourier_inversion p hp hp' f (insert i E),
      ← fourier_inversion p hp hp' f (E.erase i), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    ring
  calc
    _ = ∑ S : Finset I, fourier p f S *
        expectation p (fun E => gradient i (character p S) E * character p T E) := by
      change expectation p (fun E => gradient i f E * character p T E) = _
      simp_rw [hexpand, Finset.sum_mul]
      rw [expectation_sum]
      unfold expectation
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hi : i ∈ S
      · simp only [gradient_character, if_pos hi]
        have hfactor : expectation p
            (fun E => character p (S.erase i) E / Real.sqrt (p * (1-p)) * character p T E) =
            expectation p (fun E => character p (S.erase i) E * character p T E) /
              Real.sqrt (p * (1-p)) := by
          unfold expectation
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro E _
          ring
        rw [hfactor, character_orthogonality p hp hp']
        by_cases hST : S.erase i = T <;> simp [hi, hST, div_eq_mul_inv]
      · simp [gradient_character, hi]

lemma fourier_gradient (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (i : I) (T : Finset I) :
    fourier p (gradient i f) T =
      if i ∈ T then 0 else fourier p f (insert i T) / Real.sqrt (p * (1-p)) := by
  classical
  rw [fourier_gradient_sum p hp hp']
  by_cases hi : i ∈ T
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro S _
    have hST : ¬ (i ∈ S ∧ S.erase i = T) := by
      rintro ⟨_, h⟩
      exact Finset.notMem_erase i S (h.symm ▸ hi)
    simp [hST]
  · rw [if_neg hi]
    rw [Finset.sum_eq_single (insert i T)]
    · simp [Finset.erase_insert hi]
    · intro S _ hS
      have hST : ¬ (i ∈ S ∧ S.erase i = T) := by
        rintro ⟨hiS, h⟩
        exact hS (by rw [← h, Finset.insert_erase hiS])
      simp [hST]
    · simp


/-- Fourier multipliers are diagonal in the finite character basis. -/
lemma fourier_noise (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (T : Finset I) :
    fourier p (noise p r f) T = r ^ T.card * fourier p f T := by
  classical
  calc
    _ = ∑ S : Finset I, (r ^ S.card * fourier p f S) *
        expectation p (fun E => character p S E * character p T E) := by
      change expectation p (fun E => noise p r f E * character p T E) = _
      simp only [noise, Finset.sum_mul]
      rw [expectation_sum]
      unfold expectation
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := by
      simp_rw [character_orthogonality p hp hp']
      simp

/-- Adding a missing coordinate bijects subsets missing it with subsets containing it. -/
lemma sum_insert_not_mem (i : I) (a : Finset I → ℝ) :
    (∑ T : Finset I, if i ∉ T then a (insert i T) else 0) =
      ∑ S : Finset I, if i ∈ S then a S else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun T _ => insert i T)
  · intro T _
    simp
  · intro T hT U hU h
    have hiT : i ∉ T := (Finset.mem_filter.mp hT).2
    have hiU : i ∉ U := (Finset.mem_filter.mp hU).2
    simpa [Finset.erase_insert hiT, Finset.erase_insert hiU] using
      congrArg (fun S : Finset I => S.erase i) h
  · intro S hS
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
    exact ⟨S.erase i, by simp, Finset.insert_erase hiS⟩
  · intro T _
    rfl

/-- Weighted Parseval of coordinate gradients, before summing incidences. -/
lemma fourier_gradient_weighted (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (w : ℕ → ℝ) (i : I) :
    p * (1-p) * (∑ T : Finset I, w T.card * fourier p (gradient i f) T ^ 2) =
      ∑ S : Finset I, if i ∈ S then w (S.card-1) * fourier p f S ^ 2 else 0 := by
  classical
  have hv : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp')
  calc
    _ = ∑ T : Finset I, if i ∉ T then
        w T.card * fourier p f (insert i T) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [fourier_gradient p hp hp']
      by_cases hi : i ∈ T
      · simp [hi]
      · simp only [hi, if_false, not_false_eq_true, if_true, div_pow,
          Real.sq_sqrt hv.le]
        field_simp [hp.ne', (sub_pos.mpr hp').ne']
    _ = ∑ T : Finset I, if i ∉ T then
        w ((insert i T).card-1) * fourier p f (insert i T) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hi : i ∈ T
      · simp [hi]
      · simp [hi, Finset.card_insert_of_notMem hi]
    _ = _ := sum_insert_not_mem i (fun S => w (S.card-1) * fourier p f S ^ 2)

/-- Each Fourier support contributes once for each of its coordinates. -/
lemma sum_fourier_gradient_weighted (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) (w : ℕ → ℝ) :
    p * (1-p) * (∑ i : I, ∑ T : Finset I, w T.card * fourier p (gradient i f) T ^ 2) =
      ∑ S : Finset I, (S.card : ℝ) * w (S.card-1) * fourier p f S ^ 2 := by
  classical
  rw [Finset.mul_sum]
  simp_rw [fourier_gradient_weighted p hp hp' f w]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.sum_filter]
  simp [mul_assoc]

end ExpandingCodes.SharpThreshold

end FlattenModule128

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.Energy -/
section FlattenModule129


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Exact discrete-gradient energy identity. -/
theorem fourier_gradient_energy (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) :
    p * (1 - p) * (∑ i : I, expectation p (fun E => gradient i f E ^ 2)) =
      ∑ S : Finset I, (S.card : ℝ) * fourier p f S ^ 2 := by
  classical
  have hparseval (i : I) : expectation p (fun E => gradient i f E ^ 2) =
      ∑ T : Finset I, fourier p (gradient i f) T ^ 2 := by
    simpa only [pow_two] using fourier_inner_product p hp hp' (gradient i f) (gradient i f)
  simp_rw [hparseval]
  simpa using sum_fourier_gradient_weighted p hp hp' f (fun _ => 1)

end ExpandingCodes.SharpThreshold

end FlattenModule129

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.NoisedEnergy -/
section FlattenModule130


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Exact noised-gradient energy identity. -/
theorem fourier_noise_gradient_energy (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) :
    p * (1 - p) * (∑ i : I, expectation p (fun E => noise p r (gradient i f) E ^ 2)) =
      ∑ S : Finset I, (S.card : ℝ) * r ^ (2 * (S.card - 1)) * fourier p f S ^ 2 := by
  classical
  have hparseval (g : Finset I → ℝ) :
      expectation p (fun E => noise p r g E ^ 2) =
        ∑ T : Finset I, r ^ (2 * T.card) * fourier p g T ^ 2 := by
    have h := fourier_inner_product p hp hp' (noise p r g) (noise p r g)
    simp only [← pow_two] at h
    rw [h]
    simp_rw [fourier_noise p r hp hp']
    simp [mul_pow, ← pow_mul, Nat.mul_comm]
  simp_rw [hparseval]
  exact sum_fourier_gradient_weighted p hp hp' f (fun n => r ^ (2*n))

end ExpandingCodes.SharpThreshold

end FlattenModule130

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.Russo -/
section FlattenModule131


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure
open scoped Classical

variable {I : Type*} [Fintype I]

private lemma expectationOn_gradient_insert
    {s : Finset I} {i : I} (hi : i ∉ s) (p : ℝ) (f : Finset I → ℝ) :
    expectationOn (insert i s) p (gradient i f) =
      expectationOn s p (fun E => f (insert i E)) - expectationOn s p f := by
  classical
  rw [expectationOn_insert hi]
  have hsame : (fun E => gradient i f (insert i E)) = gradient i f := by
    funext E
    simp [gradient]
  rw [hsame]
  have hgrad : expectationOn s p (gradient i f) =
      expectationOn s p (fun E => f (insert i E)) - expectationOn s p f := by
    unfold expectationOn
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    have hiE : i ∉ E := fun h => hi (Finset.mem_powerset.mp hE h)
    simp only [gradient, Finset.erase_eq_of_notMem hiE]
    ring
  rw [hgrad]
  ring

omit [Fintype I] in
private lemma gradient_insert_other (i j : I) (hij : i ≠ j)
    (f : Finset I → ℝ) (E : Finset I) :
    gradient j f (insert i E) = gradient j (fun E => f (insert i E)) E := by
  classical
  unfold gradient
  rw [Finset.erase_insert_of_ne hij, Finset.insert_comm j i E]

/-- Differentiating the finite product measure sums the coordinate gradients.
The identity holds on all of `ℝ`, since the expectations are polynomials. -/
theorem hasDerivAt_expectationOn (s : Finset I) (f : Finset I → ℝ) (p : ℝ) :
    HasDerivAt (fun q => expectationOn s q f)
      (∑ i ∈ s, expectationOn s p (gradient i f)) p := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      simpa [expectationOn] using hasDerivAt_const p (f ∅)
  | @insert i s hi ih =>
      have hd := (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).mul (ih f)).add
        ((hasDerivAt_id p).mul (ih (fun E => f (insert i E))))
      have hsum : (∑ j ∈ insert i s, expectationOn (insert i s) p (gradient j f)) =
          (expectationOn s p (fun E => f (insert i E)) - expectationOn s p f) +
            (1 - p) * (∑ j ∈ s, expectationOn s p (gradient j f)) +
            p * (∑ j ∈ s,
              expectationOn s p (gradient j (fun E => f (insert i E)))) := by
        rw [Finset.sum_insert hi, expectationOn_gradient_insert hi]
        rw [add_assoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [expectationOn_insert hi]
        have hfun : (fun E => gradient j f (insert i E)) =
            gradient j (fun E => f (insert i E)) := by
          funext E
          exact gradient_insert_other i j (ne_of_mem_of_not_mem hj hi).symm f E
        rw [hfun]
      rw [hsum]
      convert! hd.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun q => expectationOn_insert hi q f)) using 1
      dsimp
      ring

/-- Finite polynomial differentiation identity (no monotonicity assumed). -/
theorem russo (Ω : Finset I → Prop) (p : ℝ) :
    HasDerivAt (fun q => probability q Ω) (totalInfluence p Ω) p := by
  simpa only [expectationOn_univ, probability, totalInfluence, influence] using
    hasDerivAt_expectationOn (Finset.univ : Finset I) (indicator Ω) p

end ExpandingCodes.SharpThreshold

end FlattenModule131

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold -/
section FlattenModule132







/-!
# Qualitative Boolean sharpness: checked reduction

The finite bound and convergence proof below reduce to six registered analytic
leaves in separate files. They are not completed proofs: their transitive
axioms include `sorryAx` until those leaves are proved. The independent
coefficient and Bernoulli helpers in `SharpThreshold.Basic` are hole-free.
-/

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Checked application of the registered tensorization leaf to a monotone
Boolean derivative. Its transitive axiom dependencies still include `sorryAx`
until `tensorize_two_point` is proved. -/
theorem noisy_gradient_bound (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (h : TwoPointContraction p r)
    (Ω : Finset I → Prop) (hΩ : Upward Ω) (i : I) :
    expectation p (fun E => noise p r (gradient i (indicator Ω)) E ^ 2) ≤
      influence p Ω i * Real.sqrt (influence p Ω i) := by
  have hpow : (fun E => |gradient i (indicator Ω) E| ^ (4 / 3 : ℝ)) =
      gradient i (indicator Ω) := by
    funext E
    rcases gradient_indicator_values Ω hΩ i E with hv | hv <;> simp [hv]
  have hh := tensorize_two_point p r hp hp' hr hr' h (gradient i (indicator Ω))
  rw [hpow] at hh
  change _ ≤ (influence p Ω i) ^ (3 / 2 : ℝ) at hh
  have he : (influence p Ω i) ^ (3 / 2 : ℝ) =
      influence p Ω i * Real.sqrt (influence p Ω i) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg (influence_nonneg hp.le hp'.le Ω hΩ i)
        (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  exact hh.trans_eq he

/-- Checked monotonicity reduction to Russo and nonnegative pivotal events. -/
theorem probability_monotone (Ω : Finset I → Prop) (hΩ : Upward Ω) :
    MonotoneOn (fun p => probability p Ω) (Set.Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    (differentiable_probability Ω).continuous.continuousOn
    (fun p _ => (russo Ω p).hasDerivWithinAt)
  intro p hp
  have hp' := interior_subset hp
  exact Finset.sum_nonneg fun i _ => influence_nonneg hp'.1 hp'.2 Ω hΩ i

/-- A mean-value point with bounded total influence, avoiding threshold inverse
functions and logistic differential inequalities. -/
theorem exists_small_totalInfluence (Ω : Finset I → Prop) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, totalInfluence t Ω ≤ 1 / (b - a) := by
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope
    (fun p => probability p Ω) (fun p => totalInfluence p Ω) hab
    (differentiable_probability Ω).continuous.continuousOn (fun p _ => russo Ω p)
  refine ⟨t, ht, ?_⟩
  rw [heq]
  have hpa := probability_mem_Icc ha (hab.le.trans hb) Ω
  have hpb := probability_mem_Icc (ha.trans hab.le) hb Ω
  exact div_le_div_of_nonneg_right (by linarith [hpa.1, hpb.2] : probability b Ω - probability a Ω ≤ 1)
    (sub_nonneg.mpr hab.le)

/-- The product needed by erasure capacity is bounded by the variance at any
intermediate parameter. This uses only monotonicity and zero-one bounds. -/
theorem cross_probability_le_variance (Ω : Finset I → Prop) (hΩ : Upward Ω)
    {a t b : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1) :
    probability a Ω * (1 - probability b Ω) ≤ variance t (indicator Ω) := by
  rw [variance_indicator]
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.trans hat, htb.trans hb⟩
  have hmono := probability_monotone Ω hΩ
  have h₁ := hmono ⟨ha, (hat.trans htb).trans hb⟩ ht hat
  have h₂ := hmono ht ⟨ha.trans (hat.trans htb), hb⟩ htb
  have hpt := probability_mem_Icc ht.1 ht.2 Ω
  have hpb := probability_mem_Icc (ha.trans (hat.trans htb)) hb Ω
  exact mul_le_mul h₁ (by linarith : 1 - probability b Ω ≤ 1 - probability t Ω)
    (by linarith [hpb.2] : 0 ≤ 1 - probability b Ω) hpt.1

/-- The finite qualitative estimate, reduced to explicitly registered Fourier
and tensorization leaves. No asymptotic or code-specific fact is assumed. -/
theorem variance_le_cutoff (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hr : 0 < r) (hr' : r ≤ 1) (hc : TwoPointContraction p r)
    (Ω : Finset I → Prop) (hΩ : Upward Ω) (k : ℕ) {B : ℝ}
    (hcard : 0 < Fintype.card I)
    (heq : ∀ i j, influence p Ω i = influence p Ω j)
    (hB : totalInfluence p Ω ≤ B) :
    variance p (indicator Ω) ≤
      (r ^ (2 * k))⁻¹ * B * Real.sqrt (B / Fintype.card I) + B / (k + 1 : ℝ) := by
  classical
  let a : Finset I → ℝ := fun S => if S.Nonempty then fourier p (indicator Ω) S ^ 2 else 0
  let v : I → ℝ := influence p Ω
  have ha : ∀ S, 0 ≤ a S := by intro S; dsimp [a]; split_ifs <;> positivity
  have hz : ∀ S, S.card = 0 → a S = 0 := by
    intro S hS
    simp [a, Finset.card_eq_zero.mp hS]
  have hv : ∀ i, 0 ≤ v i := influence_nonneg hp.le hp'.le Ω hΩ
  have hT : 0 ≤ totalInfluence p Ω := Finset.sum_nonneg (fun i _ => hv i)
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp.le (sub_nonneg.mpr hp'.le)
  have hpq' : p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg p]
  have henergy_eq : (∑ S, (S.card : ℝ) * a S) =
      p * (1 - p) * totalInfluence p Ω := by
    calc
      (∑ S, (S.card : ℝ) * a S) =
          ∑ S : Finset I, (S.card : ℝ) * fourier p (indicator Ω) S ^ 2 := by
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S.Nonempty
        · simp [a, hS]
        · simp [a, Finset.not_nonempty_iff_eq_empty.mp hS]
      _ = p * (1 - p) * (∑ i : I,
          expectation p (fun E => gradient i (indicator Ω) E ^ 2)) :=
        (fourier_gradient_energy p hp hp' (indicator Ω)).symm
      _ = p * (1 - p) * totalInfluence p Ω := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        unfold influence
        congr 1
        funext E
        rcases gradient_indicator_values Ω hΩ i E with h | h <;> simp [h]
  have henergy : (∑ S, (S.card : ℝ) * a S) ≤ B := by
    rw [henergy_eq]
    exact (mul_le_of_le_one_left hT hpq').trans hB
  have hn_eq : (∑ S, (S.card : ℝ) * r ^ (2 * (S.card - 1)) * a S) =
      p * (1 - p) * (∑ i : I,
        expectation p (fun E => noise p r (gradient i (indicator Ω)) E ^ 2)) := by
    rw [fourier_noise_gradient_energy p r hp hp' (indicator Ω)]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S.Nonempty
    · simp [a, hS]
    · simp [a, Finset.not_nonempty_iff_eq_empty.mp hS]
  have hmoment : 0 ≤ ∑ i, v i * Real.sqrt (v i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (Real.sqrt_nonneg _))
  have hn : (∑ S, (S.card : ℝ) * r ^ (2 * (S.card - 1)) * a S) ≤
      ∑ i, v i * Real.sqrt (v i) := by
    rw [hn_eq]
    have hh : (∑ i : I,
        expectation p (fun E => noise p r (gradient i (indicator Ω)) E ^ 2)) ≤
        ∑ i, v i * Real.sqrt (v i) :=
      Finset.sum_le_sum (fun i _ => noisy_gradient_bound p r hp hp' hr.le hr' hc Ω hΩ i)
    exact (mul_le_mul_of_nonneg_left hh hpq).trans
      (mul_le_of_le_one_left hmoment hpq')
  apply cutoff_variance_bound a Finset.card v k ha
    (fourier_parseval p hp hp' (indicator Ω)) henergy
  · have hlow := (weighted_low_degree a Finset.card ha hz k hr hr').trans
      (div_le_div_of_nonneg_right hn (pow_nonneg hr.le _))
    simpa only [div_eq_mul_inv, mul_comm] using hlow
  · positivity
  · exact hv
  · exact equal_influences_bound v hcard heq hB
  · exact hB

/-- A uniform finite bound that suffices for qualitative sharpness. The noise
radius is chosen before the coordinate type, event, or symmetry witnesses.
This is a checked reduction, not a completed theorem: the six registered
analytic leaves above remain open. -/
theorem uniform_cross_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ (J : Type) [Fintype J] (Ω : Finset J → Prop), Upward Ω →
        (∀ p ∈ Set.Icc a b, ∀ i j, influence p Ω i = influence p Ω j) →
        0 < Fintype.card J → ∀ k : ℕ,
        probability a Ω * (1 - probability b Ω) ≤
          (r ^ (2 * k))⁻¹ * (1 / (b - a)) *
            Real.sqrt ((1 / (b - a)) / Fintype.card J) +
          (1 / (b - a)) / (k + 1 : ℝ) := by
  obtain ⟨r, hr, hr', hc⟩ := two_point_uniform a b ha hab.le hb
  refine ⟨r, hr, hr', ?_⟩
  intro J inst Ω hΩ heq hcard k
  obtain ⟨t, ht, hT⟩ := exists_small_totalInfluence Ω ha.le hb.le hab
  have ht' : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact (cross_probability_le_variance Ω hΩ ha.le ht.1.le ht.2.le hb.le).trans
    (variance_le_cutoff t r (ha.trans ht.1) (ht.2.trans hb) hr hr'.le
      (hc t ht') Ω hΩ k hcard (heq t ht') hT)

/-- Qualitative sharpness, uniformly over varying finite coordinate types and
events. This theorem is a reduction to the six registered open leaves above;
its transitive axioms must still be audited as containing `sorryAx`. -/
theorem cross_tendsto_zero (J : ℕ → Type) [∀ n, Fintype (J n)]
    (Ω : ∀ n, Finset (J n) → Prop) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hΩ : ∀ n, Upward (Ω n))
    (hsym : ∀ n, ∀ p ∈ Set.Icc a b, ∀ i j,
      influence p (Ω n) i = influence p (Ω n) j)
    (hcard : Filter.Tendsto (fun n => Fintype.card (J n)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => probability a (Ω n) * (1 - probability b (Ω n)))
      Filter.atTop (nhds 0) := by
  obtain ⟨r, hr, hr', hbound⟩ := uniform_cross_bound a b ha hab hb
  let B : ℝ := 1 / (b - a)
  have hnonneg : ∀ n, 0 ≤ probability a (Ω n) * (1 - probability b (Ω n)) := by
    intro n
    exact mul_nonneg (probability_mem_Icc ha.le (hab.trans hb).le (Ω n)).1
      (sub_nonneg.mpr (probability_mem_Icc (ha.trans hab).le hb.le (Ω n)).2)
  have hcast : Filter.Tendsto (fun n => (Fintype.card (J n) : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp hcard
  have hdiv : Filter.Tendsto (fun n => B / (Fintype.card (J n) : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hcast) :
        Filter.Tendsto (fun n => B * (Fintype.card (J n) : ℝ)⁻¹)
          Filter.atTop (nhds (B * 0)))
  have hpos : ∀ᶠ n in Filter.atTop, 0 < Fintype.card (J n) :=
    hcard.eventually (Filter.eventually_gt_atTop 0)
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun n => hc.trans_le (hnonneg n)
  · intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * B / ε)
    have htail : B / (k + 1 : ℝ) < ε / 2 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
      have hk' : 2 * B < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
      nlinarith
    have hsmall : Filter.Tendsto
        (fun n => (r ^ (2 * k))⁻¹ * B * Real.sqrt (B / Fintype.card (J n)))
        Filter.atTop (nhds 0) := by
      have hs := (Real.continuous_sqrt.tendsto 0).comp hdiv
      simpa using (tendsto_const_nhds.mul hs :
        Filter.Tendsto (fun n => ((r ^ (2 * k))⁻¹ * B) *
          Real.sqrt (B / Fintype.card (J n))) Filter.atTop
          (nhds (((r ^ (2 * k))⁻¹ * B) * Real.sqrt 0)))
    have hev := (tendsto_order.1 hsmall).2 (ε / 2) (by positivity)
    filter_upwards [hev, hpos] with n hn hpn
    apply (hbound (J n) (Ω n) (hΩ n) (hsym n) hpn k).trans_lt
    change (r ^ (2 * k))⁻¹ * B * Real.sqrt (B / Fintype.card (J n)) +
      B / (k + 1 : ℝ) < ε
    linarith

end ExpandingCodes.SharpThreshold

end FlattenModule132

/-! Inlined whole module: ExpandingCodes.Probability.ErasureCapacity -/
section FlattenModule133




/-!
# Assembly at the canonical erasure interface

The definitions imported from `Definitions` are the exact platform definitions.
The lemmas here identify the reusable set-based helpers with that interface.
The canonical theorem `erasure_ambiguity` is not declared proved: its remaining
independent Boolean-analysis obligations are recorded in the task records.
-/

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter





theorem erasureExpectation_eq_expectedAmbiguity {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (p : ℝ) :
    erasureExpectation C p = Erasure.expectedAmbiguity C p := rfl

/-- A checked reduction at the exact platform expectation. Its extra hypothesis
is a purely Boolean two-probability decay statement, separated from the linear
algebra and rate argument, and is not asserted without proof. -/
theorem erasure_ambiguity_of_exit_crossDecay
    (F : ℕ → Type) [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    (M : ℕ → ℕ) (C : ∀ j, Submodule (F j) (Fin (M j) → F j))
    (ρ p q : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q < 1) (hqr : ρ < 1 - q)
    (hrate : Tendsto (fun j => (Module.finrank (F j) (C j) : ℝ) / M j)
      atTop (nhds ρ))
    (hcross : Tendsto (fun j => Erasure.meanExit (C j) p *
      (1 - Erasure.meanExit (C j) q)) atTop (nhds 0)) :
    Tendsto (fun j => erasureExpectation (C j) p / M j) atTop (nhds 0) := by
  simpa only [erasureExpectation_eq_expectedAmbiguity, Erasure.normalizedAmbiguity,
    Fintype.card_fin] using
    Erasure.ambiguity_sublinear_of_exit_crossDecay C hp hpq hq hqr
      (by simpa only [Erasure.rate, Fintype.card_fin] using hrate) hcross

/-- Code-preserving subgroups act by equality on the single-coordinate EXIT
functions. This matches the canonical convention `c ↦ c ∘ σ`. -/
theorem exit_eq_of_mem_preserving_subgroup {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (H : Subgroup (Equiv.Perm (Fin M)))
    (hH : ∀ σ ∈ H, ∀ c ∈ C, (fun i => c (σ i)) ∈ C)
    (σ : Equiv.Perm (Fin M)) (hσ : σ ∈ H) (i : Fin M) (p : ℝ) :
    Erasure.exit C (σ i) p = Erasure.exit C i p := by
  exact Erasure.exit_permute C σ (hH σ hσ) (hH σ⁻¹ (H.inv_mem hσ)) i p

theorem exit_eq_of_doublyTransitive {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (hsym : DoublyTransitiveCode M C) (hM : 2 ≤ M)
    (i j : Fin M) (p : ℝ) : Erasure.exit C i p = Erasure.exit C j p := by
  letI : Nontrivial (Fin M) := Fin.nontrivial_iff_two_le.mpr hM
  obtain ⟨i', hi'⟩ := exists_ne i
  obtain ⟨j', hj'⟩ := exists_ne j
  obtain ⟨H, hH, hpair⟩ := hsym
  obtain ⟨σ, hσ, hσi, _⟩ := hpair i i' j j' (Ne.symm hi') (Ne.symm hj')
  have he := exit_eq_of_mem_preserving_subgroup C H hH σ hσ i p
  rw [hσi] at he
  exact he.symm

theorem meanExit_eq_exit_of_doublyTransitive {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (hsym : DoublyTransitiveCode M C) (hM : 2 ≤ M)
    (i : Fin M) (p : ℝ) : Erasure.meanExit C p = Erasure.exit C i p := by
  have hc : ∀ j : Fin M, Erasure.exit C j p = Erasure.exit C i p :=
    fun j => exit_eq_of_doublyTransitive C hsym hM j i p
  unfold Erasure.meanExit
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (by omega : M ≠ 0))

theorem expectation_image_permutation {I : Type*} [Fintype I] (σ : Equiv.Perm I)
    (p : ℝ) (f : Finset I → ℝ) :
    Erasure.expectation p (fun E => f (E.image σ)) = Erasure.expectation p f := by
  simpa only [Finset.image_univ_equiv, Erasure.expectationOn_univ] using
    (Erasure.expectationOn_permute σ Finset.univ p f).symm

/-- Permutations preserving an event permute its pivotal probabilities. -/
theorem boolean_influence_permute {I : Type*} [Fintype I]
    (Ω : Finset I → Prop) (σ : Equiv.Perm I)
    (hΩ : ∀ E, Ω (E.map σ.toEmbedding) ↔ Ω E) (i : I) (p : ℝ) :
    SharpThreshold.influence p Ω (σ i) = SharpThreshold.influence p Ω i := by
  have hΩimage : ∀ E, Ω (E.image σ) ↔ Ω E := by
    intro E
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hΩ E
  have hg : ∀ E, SharpThreshold.gradient (σ i) (SharpThreshold.indicator Ω) (E.image σ) =
      SharpThreshold.gradient i (SharpThreshold.indicator Ω) E := by
    intro E
    unfold SharpThreshold.gradient
    rw [← Finset.image_insert, ← Finset.image_erase σ.injective]
    simp only [SharpThreshold.indicator, hΩimage]
  unfold SharpThreshold.influence
  rw [← expectation_image_permutation σ p
    (SharpThreshold.gradient (σ i) (SharpThreshold.indicator Ω))]
  simp_rw [hg]

theorem puncturedFailure_equal_influences {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (hsym : DoublyTransitiveCode M C)
    (i : Fin M) (p : ℝ) :
    ∀ a b : Erasure.OtherCoordinates i,
      SharpThreshold.influence p (Erasure.puncturedFailure C i) a =
        SharpThreshold.influence p (Erasure.puncturedFailure C i) b := by
  intro a b
  obtain ⟨H, hH, hpair⟩ := hsym
  have hai : i ≠ a.val := Ne.symm (Erasure.otherCoordinates_ne i a)
  have hbi : i ≠ b.val := Ne.symm (Erasure.otherCoordinates_ne i b)
  obtain ⟨σ, hσ, hfix, hab⟩ := hpair i a.val i b.val hai hbi
  let τ := Erasure.puncturedEquiv σ hfix
  have hτ : τ a = b := Subtype.ext hab
  have hΩ : ∀ E, Erasure.puncturedFailure C i (E.map τ.toEmbedding) ↔
      Erasure.puncturedFailure C i E := fun E =>
    Erasure.puncturedFailure_map C σ (hH σ hσ) (hH σ⁻¹ (H.inv_mem hσ)) hfix E
  have he := boolean_influence_permute (Erasure.puncturedFailure C i) τ hΩ a p
  rw [hτ] at he
  exact he.symm

theorem exit_monotone {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (i : I) :
    MonotoneOn (Erasure.exit C i) (Set.Icc 0 1) := by
  have hΩ : SharpThreshold.Upward (Erasure.puncturedFailure C i) := by
    intro E E' h
    exact Erasure.puncturedFailure_mono C i h
  intro p hp q hq hpq
  rw [Erasure.exit_eq_puncturedProbability, Erasure.exit_eq_puncturedProbability]
  exact SharpThreshold.probability_monotone _ hΩ hp hq hpq

theorem meanExit_monotone {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) : MonotoneOn (Erasure.meanExit C) (Set.Icc 0 1) := by
  intro p hp q hq hpq
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun i _ => exit_monotone C i hp hq hpq

/-- The code-specific assembly of the pure Boolean sharp-threshold reduction.
Only its imported, explicitly registered analytic leaves remain unproved. -/
theorem meanExit_cross_tendsto_zero
    (F : ℕ → Type) [∀ j, Field (F j)]
    (M : ℕ → ℕ) (C : ∀ j, Submodule (F j) (Fin (M j) → F j))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q < 1)
    (hsym : ∀ j, DoublyTransitiveCode (M j) (C j))
    (hlength : Tendsto M atTop atTop) :
    Tendsto (fun j => Erasure.meanExit (C j) p *
      (1 - Erasure.meanExit (C j) q)) atTop (nhds 0) := by
  let a : ℝ := (p + q) / 2
  have hpa : p < a := by dsimp [a]; linarith
  have haq : a < q := by dsimp [a]; linarith
  have ha : 0 < a := hp.trans_lt hpa
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    (hlength.eventually (Filter.eventually_ge_atTop 2))
  have hM : ∀ n, 2 ≤ M (n + k) := fun n => hk (n + k) (by omega)
  let coord : ∀ n, Fin (M (n + k)) := fun n => ⟨0, by have := hM n; omega⟩
  let J : ℕ → Type := fun n => Erasure.OtherCoordinates (coord n)
  let Ω : ∀ n, Finset (J n) → Prop := fun n => Erasure.puncturedFailure (C (n + k)) (coord n)
  have hΩ : ∀ n, SharpThreshold.Upward (Ω n) := by
    intro n E E' h
    exact Erasure.puncturedFailure_mono _ _ h
  have hinf : ∀ n, ∀ t ∈ Set.Icc a q, ∀ i j,
      SharpThreshold.influence t (Ω n) i = SharpThreshold.influence t (Ω n) j := by
    intro n t _ i j
    exact puncturedFailure_equal_influences _ (hsym (n + k)) (coord n) t i j
  have hcard : Tendsto (fun n => Fintype.card (J n)) atTop atTop := by
    have hn := (Filter.tendsto_sub_atTop_nat 1).comp
      (hlength.comp (Filter.tendsto_add_atTop_nat k))
    simpa only [J, Erasure.card_otherCoordinates, Fintype.card_fin, Function.comp_def] using hn
  have heq : ∀ n t, SharpThreshold.probability t (Ω n) = Erasure.meanExit (C (n + k)) t := by
    intro n t
    rw [meanExit_eq_exit_of_doublyTransitive _ (hsym (n + k)) (hM n) (coord n),
      Erasure.exit_eq_puncturedProbability]
    rfl
  have haCross := SharpThreshold.cross_tendsto_zero J Ω a q ha haq hq hΩ hinf hcard
  simp_rw [heq] at haCross
  have hpCross : Tendsto (fun n => Erasure.meanExit (C (n + k)) p *
      (1 - Erasure.meanExit (C (n + k)) q)) atTop (nhds 0) := by
    apply squeeze_zero _ _ haCross
    · intro n
      exact mul_nonneg (Erasure.meanExit_nonneg _ hp (hpq.trans hq).le)
        (sub_nonneg.mpr (Erasure.meanExit_le_one _ (hp.trans hpq.le) hq.le))
    · intro n
      exact mul_le_mul_of_nonneg_right
        (meanExit_monotone _ ⟨hp, (hpq.trans hq).le⟩ ⟨ha.le, (haq.trans hq).le⟩ hpa.le)
        (sub_nonneg.mpr (Erasure.meanExit_le_one _ (hp.trans hpq.le) hq.le))
  exact (Filter.tendsto_add_atTop_iff_nat k).mp hpCross

/-- Exact platform Lemma 2.3, reduced to six registered Boolean-analysis leaves.
This is a checked decomposition once compiled, not a completed proof until the
transitive `sorryAx` dependencies in `SharpThreshold` have been discharged. -/
theorem erasure_ambiguity
    (F : ℕ → Type) [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    (M : ℕ → ℕ) (C : ∀ j, Submodule (F j) (Fin (M j) → F j))
    (ρ p : ℝ) (hρ : 0 < ρ ∧ ρ < 1) (hp : 0 ≤ p ∧ p < 1 - ρ)
    (hsym : ∀ j, DoublyTransitiveCode (M j) (C j))
    (hlength : Tendsto M atTop atTop)
    (hrate : Tendsto (fun j => (Module.finrank (F j) (C j) : ℝ) / M j) atTop (nhds ρ)) :
    Tendsto (fun j => erasureExpectation (C j) p / M j) atTop (nhds 0) := by
  let q : ℝ := (p + (1 - ρ)) / 2
  have hpq : p < q := by dsimp [q]; linarith [hp.2]
  have hq : q < 1 := by dsimp [q]; linarith [hp.2, hρ.1]
  have hqr : ρ < 1 - q := by dsimp [q]; linarith [hp.2]
  exact erasure_ambiguity_of_exit_crossDecay F M C ρ p q hp.1 hpq hq hqr hrate
    (meanExit_cross_tendsto_zero F M C p q hp.1 hpq hq hsym hlength)

end ExpandingCodes.PolynomialStretch

end FlattenModule133

/-! Inlined whole module: ExpandingCodes.Probability.AuxiliaryErasure -/
section FlattenModule134





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

end FlattenModule134

/-! Inlined whole module: ExpandingCodes.Probability.AuxiliaryRate -/
section FlattenModule135




set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem auxiliary_rate (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) ∧
    limitingRate (dimension ε) < 1 / 2 ∧
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount (dimension ε) n) atTop (nhds (limitingRate (dimension ε))) ∧
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount (dimension ε) n) atTop (nhds 0) := by
  have hd := dimension_ge_four ε hε
  have hlo := limitingRate_lower_parameter ε hε
  have hhi := limitingRate_lt_half (dimension ε) hd
  have hρ : 0 < limitingRate (dimension ε) ∧ limitingRate (dimension ε) < 1/2 := by
    constructor
    · linarith [hε.2]
    · exact hhi
  exact ⟨hlo, hhi, tendsto_auxiliaryCode_rate (dimension ε) hd g,
    tendsto_auxiliaryCode_halfErasure (dimension ε) hd hρ g⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule135


open scoped Classical
open ExpandingCodes.PolynomialStretch Filter

theorem solution (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) ∧
    limitingRate (dimension ε) < 1 / 2 ∧
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount (dimension ε) n) atTop (nhds (limitingRate (dimension ε))) ∧
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount (dimension ε) n) atTop (nhds 0) := by
  exact auxiliary_rate ε hε g
