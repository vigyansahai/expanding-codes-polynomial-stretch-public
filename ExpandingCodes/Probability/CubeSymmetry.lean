import ExpandingCodes.Probability.HalfspaceVolume

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
