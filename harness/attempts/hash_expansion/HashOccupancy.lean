import ExpandingCodes.Probability.FiniteEvents

set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Uniform probability on a finite product is the average of the fiber probabilities. -/
theorem uniformProb_prod_fibers {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (E : A × B → Prop) :
    uniformProb E = (∑ a : A, uniformProb (fun b : B => E (a, b))) / Fintype.card A := by
  classical
  simp_rw [uniformProb_eq_card_filter]
  have hc : ((Finset.univ.filter E).card : ℝ) =
      ∑ a : A, ((Finset.univ.filter (fun b : B => E (a, b))).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    push_cast
    rfl
  rw [hc, Fintype.card_prod, Nat.cast_mul]
  simp_rw [← Finset.sum_div]
  ring

/-- A uniform upper bound on every fiber bounds the product event. -/
theorem uniformProb_prod_le_of_fibers {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (E : A × B → Prop) (C : ℝ)
    (h : ∀ a, uniformProb (fun b : B => E (a, b)) ≤ C) : uniformProb E ≤ C := by
  rw [uniformProb_prod_fibers]
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).2
  calc
    _ ≤ ∑ _a : A, C := Finset.sum_le_sum (fun a _ => h a)
    _ = _ := by simp [mul_comm]

/-- Every finite image has a subset of distinct representatives. -/
theorem exists_image_representatives {I V : Type*} [DecidableEq I] [DecidableEq V] (D : Finset I) (f : I → V) :
    ∃ R ⊆ D, R.card = (D.image f).card ∧ R.image f = D.image f := by
  classical
  obtain ⟨R, hR, hinj, him⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (D : Set I) (D.image f)
      (by simpa using (Set.surjOn_image f (D : Set I)))
  refine ⟨R, hR, ?_, him⟩
  rw [← him, Finset.card_image_of_injOn hinj]

/-- If an image has at least `r` fewer values, a set of `|D|-r` representatives covers it. -/
theorem exists_image_cover_of_loss {I V : Type*} [DecidableEq I] [DecidableEq V] (D : Finset I) (f : I → V) (r : ℕ)
    (hloss : (D.image f).card + r ≤ D.card) :
    ∃ R ∈ D.powersetCard (D.card - r), D.image f ⊆ R.image f := by
  classical
  obtain ⟨R, hRD, hc, hi⟩ := exists_image_representatives D f
  obtain ⟨T, hRT, hTD, hT⟩ := Finset.exists_subsuperset_card_eq hRD
    (by omega : R.card ≤ D.card - r) (Nat.sub_le _ _)
  exact ⟨T, Finset.mem_powersetCard.mpr ⟨hTD, hT⟩, hi ▸ Finset.image_subset_image hRT⟩

/-- Once representative hash values are fixed, all other prescribed inputs hit their image
with probability at most one factor `|R|/|V|` per input. -/
theorem uniformProb_image_covered_le {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    [Nonempty V] (D R : Finset I) (hRD : R ⊆ D) :
    uniformProb (fun f : I → V => D.image f ⊆ R.image f) ≤
      ((R.card : ℝ) / Fintype.card V) ^ (D.card - R.card) := by
  classical
  let J := {i : I // i ∉ R}
  let A : Finset J := (D \ R).attach.image
    (fun i => (⟨i.val, (Finset.mem_sdiff.mp i.property).2⟩ : J))
  have hAc : A.card = D.card - R.card := by
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_attach, Finset.card_sdiff_of_subset hRD]
    · intro i j h
      exact Subtype.ext (congrArg (fun x : J => x.val) h)
  let e := Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ R) (fun _ => V)
  rw [← uniformProb_equiv e.symm]
  apply uniformProb_prod_le_of_fibers
  intro a
  have hcov : ∀ c : J → V,
      D.image (e.symm (a, c)) ⊆ R.image (e.symm (a, c)) →
      ∀ i ∈ A, c i ∈ Finset.univ.image a := by
    intro c hc i hi
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
    have hjD : j.val ∈ D := (Finset.mem_sdiff.mp j.property).1
    have hx := hc (Finset.mem_image.mpr ⟨j.val, hjD, rfl⟩)
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, ?_⟩
    subst i
    simpa [e, Equiv.piEquivPiSubtypeProd, hw, (Finset.mem_sdiff.mp j.property).2]
      using hwe
  calc
    _ ≤ uniformProb (fun c : J → V => ∀ i ∈ A, c i ∈ Finset.univ.image a) :=
      uniformProb_mono hcov
    _ = ∏ _i ∈ A, uniformProb (fun v : V => v ∈ Finset.univ.image a) :=
      uniformProb_pi_finset A (fun _ v => v ∈ Finset.univ.image a)
    _ = (((Finset.univ.image a).card : ℝ) / Fintype.card V) ^ A.card := by
      have hp : uniformProb (fun v : V => v ∈ Finset.univ.image a) =
          ((Finset.univ.image a).card : ℝ) / Fintype.card V := by
        rw [uniformProb_eq_card_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp only [hp, Finset.prod_const]
    _ ≤ ((R.card : ℝ) / Fintype.card V) ^ (D.card - R.card) := by
      rw [hAc]
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_image_le (s := Finset.univ) (f := a)).trans_eq
        (by simp)

/-- Finite occupancy bound for independent values of a full uniformly sampled function.
The witness is a subset of representative inputs, so no adaptively exposed value is assumed
independent of its own past. -/
theorem uniformProb_image_loss_le {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    [Nonempty V] (D : Finset I) (r : ℕ) :
    uniformProb (fun f : I → V => (D.image f).card + r ≤ D.card) ≤
      (2 : ℝ) ^ D.card * ((D.card : ℝ) / Fintype.card V) ^ r := by
  classical
  by_cases hr : r ≤ D.card
  · have hcover : ∀ f : I → V, (D.image f).card + r ≤ D.card →
        ∃ R ∈ D.powersetCard (D.card - r), D.image f ⊆ R.image f :=
      fun f hf => exists_image_cover_of_loss D f r hf
    calc
      _ ≤ uniformProb (fun f : I → V =>
          ∃ R ∈ D.powersetCard (D.card - r), D.image f ⊆ R.image f) :=
        uniformProb_mono hcover
      _ ≤ ∑ R ∈ D.powersetCard (D.card - r),
          uniformProb (fun f : I → V => D.image f ⊆ R.image f) :=
        uniformProb_exists_finset _ _
      _ ≤ ∑ _R ∈ D.powersetCard (D.card - r),
          ((D.card : ℝ) / Fintype.card V) ^ r := by
        apply Finset.sum_le_sum
        intro R hR
        obtain ⟨hRD, hc⟩ := Finset.mem_powersetCard.mp hR
        have hexp : D.card - R.card = r := by omega
        calc
          _ ≤ ((R.card : ℝ) / Fintype.card V) ^ (D.card - R.card) :=
            uniformProb_image_covered_le D R hRD
          _ ≤ ((D.card : ℝ) / Fintype.card V) ^ r := by
            rw [hexp]
            apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_le_card hRD
      _ = ((D.powersetCard (D.card - r)).card : ℝ) *
          ((D.card : ℝ) / Fintype.card V) ^ r := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ D.card * ((D.card : ℝ) / Fintype.card V) ^ r := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_card
          (show D.powersetCard (D.card - r) ⊆ D.powerset from by
            intro R hR
            exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hR).1)).trans_eq
          (Finset.card_powerset D)
  · have hzero : uniformProb (fun f : I → V => (D.image f).card + r ≤ D.card) = 0 := by
      have he : uniformProb (fun f : I → V => (D.image f).card + r ≤ D.card) =
          uniformProb (fun _f : I → V => False) := by
        apply uniformProb_congr
        intro f
        constructor
        · intro h
          omega
        · exact False.elim
      rw [he, uniformProb_eq_card_filter]
      simp only [Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
    rw [hzero]
    positivity

end ExpandingCodes.PolynomialStretch
