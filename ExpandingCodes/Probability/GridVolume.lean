import ExpandingCodes.Probability.HalfspaceVolume

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

theorem measurableSet_truncatedGrid (q d R : ℕ) :
    MeasurableSet (truncatedGrid q d R) :=
  MeasurableSet.iUnion (fun a => measurableSet_gridBox a.val)

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
