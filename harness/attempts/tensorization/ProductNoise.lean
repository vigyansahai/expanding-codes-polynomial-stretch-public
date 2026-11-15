import ExpandingCodes.Probability.SharpThreshold.Basic
import Mathlib.Analysis.MeanInequalities

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

/-- Finite tensorization, conditional on the scalar inequality. -/
theorem tensorize_two_point (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (h : TwoPointContraction p r)
    (f : Finset I → ℝ) :
    expectation p (fun E => noise p r f E ^ 2) ≤
      (expectation p (fun E => |f E| ^ (4 / 3 : ℝ))) ^ (3 / 2 : ℝ) := by
  simpa only [expectationOn_univ, ← noise_eq_productNoiseOn_univ] using
    productNoiseOn_contract p r hp hp' h Finset.univ f

#print axioms tensorize_two_point

end ExpandingCodes.SharpThreshold
