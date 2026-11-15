import ExpandingCodes.Probability.HashOccupancy
import ExpandingCodes.Construction.HashNeighbors
import ExpandingCodes.Construction.HashParameters
import ExpandingCodes.Probability.PreliminaryCounting

set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

/-- A fixed row-set failure requires independent hash occupancy losses. -/
theorem uniformProb_combined_fixed_set_le (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hfit : arity ε * buckets ε n ≤ n) (hgood : PreliminaryGood ε n g s)
    (L : ℕ) (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (S : Finset (Fin (rowCount (dimension ε) n)))
    (hsize : (S.card : ℝ) ≤ (n : ℝ) ^ (1 - ε)) (C : ℝ)
    (_hC : 0 ≤ C) (hbase : (arity ε : ℝ) * S.card / (buckets ε n : ℝ) ≤ C) :
    uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
      ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) ≤
      ((2 : ℝ) ^ arity ε * C ^ L) ^ S.card := by
  classical
  let D := neighbors (preliminary g s) S
  have hD : D.card ≤ arity ε * S.card := preliminary_neighbors_card_le g s S
  have hocc := uniformProb_image_loss_le (V := Fin (buckets ε n)) D (L * S.card)
  have heq := uniformProb_equiv (hashesEquiv (F := g.F) (arity ε) (buckets ε n))
    (fun f : (Fin (arity ε) × (g.F × g.F × g.F)) → Fin (buckets ε n) =>
      (D.image f).card + L * S.card ≤ D.card)
  have hoccH := heq.le.trans hocc
  calc
    _ ≤ uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
        (D.image (fun p => h p.1 p.2)).card + L * S.card ≤ D.card) := by
      apply uniformProb_mono
      intro h hh
      exact combined_failure_implies_image_loss ε n g s h hfit hgood L hL S hsize hh
    _ ≤ (2 : ℝ) ^ D.card * ((D.card : ℝ) / (buckets ε n : ℝ)) ^ (L * S.card) := by
      simpa only [hashesEquiv, Equiv.coe_fn_mk, Fintype.card_fin] using hoccH
    _ ≤ (2 : ℝ) ^ (arity ε * S.card) * C ^ (L * S.card) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) hD
      · apply pow_le_pow_left₀ (by positivity)
        calc
          (D.card : ℝ) / (buckets ε n : ℝ) ≤
              (arity ε : ℝ) * S.card / (buckets ε n : ℝ) := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast hD
          _ ≤ C := hbase
      · positivity
      · positivity
    _ = _ := by simp only [mul_pow, pow_mul]

/-- Union over row subsets of a prescribed size, counted by the elementary bound `m^a`. -/
theorem uniformProb_exists_combined_sets_le_pow (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hfit : arity ε * buckets ε n ≤ n) (hgood : PreliminaryGood ε n g s)
    (L : ℕ) (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (a : ℕ) (hsize : (a : ℝ) ≤ (n : ℝ) ^ (1 - ε)) (C : ℝ)
    (hC : 0 ≤ C) (hbase : (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) /
      (buckets ε n : ℝ) ≤ C) :
    uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
      ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a,
        ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) ≤
      ((rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L) ^ a := by
  classical
  let Q : ℝ := (2 : ℝ) ^ arity ε * C ^ L
  have hQ : 0 ≤ Q := by positivity
  have hcount : (((Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a).card : ℝ) ≤
      (rowCount (dimension ε) n : ℝ) ^ a := by
    have hnat : ((Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a).card ≤
        rowCount (dimension ε) n ^ a := by
      simpa only [Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin] using Nat.choose_le_pow (rowCount (dimension ε) n) a
    exact_mod_cast hnat
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a,
        uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
          ((neighbors (combined g s h) S).card : ℝ) <
            (1 - ε) * arity ε * S.card) := uniformProb_exists_finset _ _
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a,
        Q ^ a := by
      apply Finset.sum_le_sum
      intro S hS
      have hc : S.card = a := (Finset.mem_powersetCard.mp hS).2
      have hb : (arity ε : ℝ) * S.card / (buckets ε n : ℝ) ≤ C := by
        apply le_trans _ hbase
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left (by simpa only [hc] using hsize) (Nat.cast_nonneg _)
      simpa only [Q, hc] using uniformProb_combined_fixed_set_le ε n g s hfit hgood
        L hL S (by simpa only [hc] using hsize) C hC hb
    _ = (((Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a).card : ℝ) *
        Q ^ a := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (rowCount (dimension ε) n : ℝ) ^ a * Q ^ a :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hQ a)
    _ = _ := by rw [← mul_pow]; congr 1; dsimp [Q]; ring

/-- A quantitative finite hash expansion estimate, uniform over all admissible forms. -/
theorem combined_bad_prob_le_two_base (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hfit : arity ε * buckets ε n ≤ n) (hgood : PreliminaryGood ε n g s)
    (L : ℕ) (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (C : ℝ) (hC : 0 ≤ C) (hbase : (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) /
      (buckets ε n : ℝ) ≤ C)
    (hhalf : (rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L ≤ 1 / 2) :
    uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
      ¬ Expanding (combined g s h) (1 - ε) (arity ε) ((n : ℝ) ^ (1 - ε))) ≤
      2 * ((rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L) := by
  classical
  let t := (n : ℝ) ^ (1 - ε)
  let N := ⌊t⌋₊
  let B : ℝ := (rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L
  have ht : 0 ≤ t := by positivity
  have hB : 0 ≤ B := by positivity
  have hcover : ∀ h : Hashes g.F (arity ε) (buckets ε n),
      ¬ Expanding (combined g s h) (1 - ε) (arity ε) t →
      ∃ j ∈ Finset.range N,
        ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard (j + 1),
          ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card := by
    intro h hh
    obtain ⟨S, hne, hsize, hbad⟩ := combined_not_expanding_witness g s h
      (sampler_buckets_pos ε n) hfit ε t hh
    have hpos : 0 < S.card := Finset.card_pos.mpr hne
    have hc : S.card ≤ N := Nat.le_floor hsize
    refine ⟨S.card - 1, Finset.mem_range.mpr (by omega), S, ?_, hbad⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by omega⟩
  calc
    _ ≤ uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
        ∃ j ∈ Finset.range N,
          ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard (j + 1),
            ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) :=
      uniformProb_mono hcover
    _ ≤ ∑ j ∈ Finset.range N,
        uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
          ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard (j + 1),
            ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) :=
      uniformProb_exists_finset _ _
    _ ≤ ∑ j ∈ Finset.range N, B ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjs : ((j + 1 : ℕ) : ℝ) ≤ t :=
        (Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans (Nat.floor_le ht)
      exact uniformProb_exists_combined_sets_le_pow ε n g s hfit hgood L hL
        (j + 1) hjs C hC hbase
    _ ≤ 2 * B := sum_pow_succ_le_two_mul B hB hhalf N

/-- The exact canonical hash-expansion envelope, uniform over arbitrary public geometry
and all preliminary-good sampled forms. -/
theorem hash_expansion_envelope (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧
      Tendsto (fun n => δ n * (n : ℝ) ^ (1 / ε)) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ s : Forms (g n).F (dimension ε) (arity ε),
        PreliminaryGood ε n (g n) s →
        uniformProb (fun h : Hashes (g n).F (arity ε) (buckets ε n) =>
          ¬ Expanding (combined (g n) s h) (1 - ε) (arity ε) ((n : ℝ) ^ (1 - ε))) ≤ δ n := by
  refine ⟨fun n => 2 * hashRatio ε n, fun n => mul_nonneg (by norm_num) (hashRatio_nonneg ε n), ?_, ?_⟩
  · have hh := (tendsto_hashRatio_scaled ε hε).const_mul 2
    simpa only [mul_assoc, mul_zero] using hh
  · filter_upwards [eventually_hash_parameters ε hε] with n hn
    intro s hs
    exact combined_bad_prob_le_two_base ε n (g n) s hn.2.1 hs (hashRepeatThreshold ε)
      (hashRepeatThreshold_le ε hε) (2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε))
      (by positivity) (hash_bucket_ratio_le ε n (hash_arity_pos ε hε) hn.1) hn.2.2

end ExpandingCodes.PolynomialStretch
