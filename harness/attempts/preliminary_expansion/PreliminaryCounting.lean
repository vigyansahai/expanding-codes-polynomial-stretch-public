import ExpandingCodes.Construction.Peeling
import ExpandingCodes.Construction.Geometry
import ExpandingCodes.Probability.UniformLinear
import ExpandingCodes.Probability.FiniteEvents

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- A pair of sampled linear forms collides on some distinct pair of candidates. -/
noncomputable def candidateCollision {F : Type*} [Field F] {d : ℕ}
    (W : Finset (Fin d → F)) (a : Fin 2 → Fin d → F) : Prop :=
  ∃ z ∈ W, ∃ z' ∈ W, z ≠ z' ∧
    linearForm (a 0) z = linearForm (a 0) z' ∧
    linearForm (a 1) z = linearForm (a 1) z'

/-- All prescribed active pairs have distinct collision witnesses in deterministic `W_A`. -/
noncomputable def activeWitnessEvent {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (s : Forms g.F d k) : Prop :=
  ∀ p ∈ A, candidateCollision (activePointSet g A) (fun j => s j p.1 p.2)

/-- A union bound over ordered pairs of candidates. -/
theorem uniformProb_candidateCollision_le {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (W : Finset (Fin d → F)) :
    uniformProb (candidateCollision W) ≤ (W.card : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  classical
  let E := fun p : (Fin d → F) × (Fin d → F) =>
    fun a : Fin 2 → Fin d → F => p.1 ≠ p.2 ∧
      linearForm (a 0) p.1 = linearForm (a 0) p.2 ∧
      linearForm (a 1) p.1 = linearForm (a 1) p.2
  have hE : ∀ p, uniformProb (E p) ≤ 1 / (Fintype.card F : ℝ) ^ 2 := by
    intro p
    by_cases hne : p.1 ≠ p.2
    · have heq : uniformProb (E p) = uniformProb (fun a : Fin 2 → Fin d → F =>
          linearForm (a 0) p.1 = linearForm (a 0) p.2 ∧
          linearForm (a 1) p.1 = linearForm (a 1) p.2) := by
        apply uniformProb_congr
        intro a
        change (_ ∧ _) ↔ _
        exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩
      rw [heq, uniformProb_two_linearForm_collision _ _ hne]
    · have heq : uniformProb (E p) = 0 := by
        rw [uniformProb_eq_card_filter]
        simp [E, hne]
      rw [heq]
      positivity
  have heq : uniformProb (candidateCollision W) =
      uniformProb (fun a => ∃ p ∈ W.product W, E p a) := by
    apply uniformProb_congr
    intro a
    simp only [candidateCollision, Finset.mem_product, E]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ p ∈ W.product W, uniformProb (E p) := uniformProb_exists_finset _ _
    _ ≤ ∑ _p ∈ W.product W, 1 / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun p _ => hE p)
    _ = _ := by simp [pow_two, div_eq_mul_inv, mul_assoc]

/-- Finite witness counting, with independence even when witness pairs overlap. -/
theorem uniformProb_activeWitnessEvent_le {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (A : Finset (Fin k × g.F)) :
    uniformProb (activeWitnessEvent g A) ≤
      ((A.card : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ^ 2) ^ A.card := by
  classical
  rw [show activeWitnessEvent g A = (fun s : Forms g.F d k =>
    ∀ p ∈ A, candidateCollision (activePointSet g A) (fun j => s j p.1 p.2)) from rfl]
  rw [uniformProb_forms_events]
  have hc : ((activePointSet g A).card : ℝ) ≤ (A.card : ℝ) ^ d := by
    exact_mod_cast activePointSet_card_le g hk A
  have hq : Fintype.card g.F = fieldSize d n := geometry_card g
  calc
    _ ≤ ∏ _p ∈ A, ((A.card : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hp
        rw [uniformProb_eq_card_filter]
        positivity
      · intro p hp
        have hw := uniformProb_candidateCollision_le (activePointSet g A)
        rw [hq] at hw
        apply hw.trans
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          ((activePointSet g A).card : ℝ) ^ 2 ≤ ((A.card : ℝ) ^ d) ^ 2 := by
            gcongr
          _ = (A.card : ℝ) ^ (2 * d) := by rw [← pow_mul, Nat.mul_comm]
    _ = _ := by simp [div_pow]

/-- The canonical failure event is covered by nonempty active sets and their witnesses. -/
theorem preliminary_bad_implies_activeWitnessEvent (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (hd : 0 < dimension ε)
    (s : Forms g.F (dimension ε) (arity ε))
    (hbad : ¬ PreliminaryGood ε n g s) :
    ∃ A : Finset (Fin (arity ε) × g.F), A.Nonempty ∧
      (A.card : ℝ) ≤ (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) ∧ activeWitnessEvent g A s := by
  classical
  obtain ⟨S, hne, hsize, hcore⟩ := preliminary_bad_has_collision_core ε n g s hbad
  let A := preliminaryActivePairs g s S
  have hA : A.Nonempty := collision_core_activePairs_nonempty g hd s S hne hcore
  have hc : (A.card : ℝ) ≤ (arity ε : ℝ) * S.card := by
    have hi := preliminaryActivePairs_card_le g s S
    have hi' : 2 * (A.card : ℝ) ≤ (arity ε : ℝ) * S.card := by exact_mod_cast hi
    nlinarith [show 0 ≤ (A.card : ℝ) from Nat.cast_nonneg _]
  refine ⟨A, hA, hc.trans (mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg _)), ?_⟩
  intro p hp
  obtain ⟨z, hz, z', hz', hneq, hf, ha⟩ := (mem_preliminaryActivePairs g s S p).mp hp
  have hw := collision_core_rows_mem_activePointSet g s S hcore
  have hf' : fixedForm g p.1 (g.rowOrder z') = p.2 := by
    have hh : fixedForm g p.1 (g.rowOrder z) =
        fixedForm g p.1 (g.rowOrder z') := congrArg Prod.fst ha
    exact hh.symm.trans hf
  refine ⟨g.rowOrder z, hw z hz, g.rowOrder z', hw z' hz',
    fun he => hneq (g.rowOrder.injective he), ?_⟩
  change (fixedForm g p.1 (g.rowOrder z),
      linearForm (s 0 p.1 (fixedForm g p.1 (g.rowOrder z))) (g.rowOrder z),
      linearForm (s 1 p.1 (fixedForm g p.1 (g.rowOrder z))) (g.rowOrder z)) =
    (fixedForm g p.1 (g.rowOrder z'),
      linearForm (s 0 p.1 (fixedForm g p.1 (g.rowOrder z'))) (g.rowOrder z'),
      linearForm (s 1 p.1 (fixedForm g p.1 (g.rowOrder z'))) (g.rowOrder z')) at ha
  simp only [hf, hf', Prod.mk.injEq, true_and] at ha
  exact ha

/-- Union-bound active sets of one fixed cardinality, using the coarse count `(kq)^a`. -/
theorem uniformProb_exists_active_sets_le_pow {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (a : ℕ) (B : ℝ)
    (hbase : (k : ℝ) * (a : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ≤ B) :
    uniformProb (fun s : Forms g.F d k =>
      ∃ A ∈ (Finset.univ : Finset (Fin k × g.F)).powersetCard a,
        activeWitnessEvent g A s) ≤ B ^ a := by
  classical
  let C : ℝ := (a : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ^ 2
  have hC : 0 ≤ C := by positivity
  have hcount : (((Finset.univ : Finset (Fin k × g.F)).powersetCard a).card : ℝ) ≤
      ((k * fieldSize d n : ℕ) : ℝ) ^ a := by
    have hnat : ((Finset.univ : Finset (Fin k × g.F)).powersetCard a).card ≤
        (k * fieldSize d n) ^ a := by
      rw [Finset.card_powersetCard]
      simpa [Fintype.card_prod, geometry_card g] using
        Nat.choose_le_pow (k * fieldSize d n) a
    exact_mod_cast hnat
  calc
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin k × g.F)).powersetCard a,
        uniformProb (activeWitnessEvent g A) := uniformProb_exists_finset _ _
    _ ≤ ∑ _A ∈ (Finset.univ : Finset (Fin k × g.F)).powersetCard a, C ^ a := by
      apply Finset.sum_le_sum
      intro A hA
      have ha : A.card = a := (Finset.mem_powersetCard.mp hA).2
      simpa [C, ha] using uniformProb_activeWitnessEvent_le g hk A
    _ = (((Finset.univ : Finset (Fin k × g.F)).powersetCard a).card : ℝ) * C ^ a := by
      simp
    _ ≤ ((k * fieldSize d n : ℕ) : ℝ) ^ a * C ^ a :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hC a)
    _ = (((k * fieldSize d n : ℕ) : ℝ) * C) ^ a := (mul_pow _ _ _).symm
    _ ≤ B ^ a := by
      apply pow_le_pow_left₀ (by positivity)
      have hq : (fieldSize d n : ℝ) ≠ 0 := by exact_mod_cast (fieldSize_pos d n).ne'
      have he : (((k * fieldSize d n : ℕ) : ℝ) * C) =
          (k : ℝ) * (a : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) := by
        dsimp [C]
        push_cast
        field_simp
      rw [he]
      exact hbase

/-- Positive finite geometric sums are at most twice their first term when the ratio is at most `1/2`. -/
theorem sum_pow_succ_le_two_mul (B : ℝ) (hB : 0 ≤ B) (hhalf : B ≤ 1 / 2) (N : ℕ) :
    (∑ j ∈ Finset.range N, B ^ (j + 1)) ≤ 2 * B := by
  calc
    _ = B * ∑ j ∈ Finset.range N, B ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ, mul_comm]
    _ ≤ B * ∑ j ∈ Finset.range N, (1 / (2 : ℝ)) ^ j := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_left₀ hB hhalf j
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hB
    _ = _ := mul_comm _ _

/-- A finite, quantitative version of the exact canonical preliminary expansion estimate.
Only the parameter-dependent geometric ratio remains for the asymptotic step. -/
theorem preliminary_bad_prob_le_two_base (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (hd : 0 < dimension ε)
    (hk : arity ε ≤ fieldSize (dimension ε) n)
    (hhalf : (arity ε : ℝ) *
      ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ (2 * dimension ε) /
        (fieldSize (dimension ε) n : ℝ) ≤ 1 / 2) :
    uniformProb (fun s : Forms g.F (dimension ε) (arity ε) =>
      ¬ PreliminaryGood ε n g s) ≤
      2 * ((arity ε : ℝ) *
        ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ (2 * dimension ε) /
          (fieldSize (dimension ε) n : ℝ)) := by
  classical
  let t : ℝ := (arity ε : ℝ) * (n : ℝ) ^ (1 - ε)
  let N := ⌊t⌋₊
  let B : ℝ := (arity ε : ℝ) * t ^ (2 * dimension ε) /
    (fieldSize (dimension ε) n : ℝ)
  have ht : 0 ≤ t := by positivity
  have hB : 0 ≤ B := by positivity
  have hcover : ∀ s : Forms g.F (dimension ε) (arity ε),
      ¬ PreliminaryGood ε n g s →
      ∃ j ∈ Finset.range N,
        ∃ A ∈ (Finset.univ : Finset (Fin (arity ε) × g.F)).powersetCard (j + 1),
          activeWitnessEvent g A s := by
    intro s hs
    obtain ⟨A, hne, hsize, hevent⟩ := preliminary_bad_implies_activeWitnessEvent ε n g hd s hs
    have hpos : 0 < A.card := Finset.card_pos.mpr hne
    have hcard : A.card ≤ N := Nat.le_floor hsize
    refine ⟨A.card - 1, Finset.mem_range.mpr (by omega), A, ?_, hevent⟩
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ A, by omega⟩
  calc
    _ ≤ uniformProb (fun s : Forms g.F (dimension ε) (arity ε) =>
        ∃ j ∈ Finset.range N,
          ∃ A ∈ (Finset.univ : Finset (Fin (arity ε) × g.F)).powersetCard (j + 1),
            activeWitnessEvent g A s) := uniformProb_mono hcover
    _ ≤ ∑ j ∈ Finset.range N,
        uniformProb (fun s : Forms g.F (dimension ε) (arity ε) =>
          ∃ A ∈ (Finset.univ : Finset (Fin (arity ε) × g.F)).powersetCard (j + 1),
            activeWitnessEvent g A s) := uniformProb_exists_finset _ _
    _ ≤ ∑ j ∈ Finset.range N, B ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply uniformProb_exists_active_sets_le_pow g hk (j + 1) B
      have hjt : ((j + 1 : ℕ) : ℝ) ≤ t :=
        (Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans (Nat.floor_le ht)
      dsimp [B]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hjt _
    _ ≤ 2 * B := sum_pow_succ_le_two_mul B hB hhalf N
    _ = _ := rfl

end ExpandingCodes.PolynomialStretch
