import ExpandingCodes.Probability.SharpThreshold.Basic
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
