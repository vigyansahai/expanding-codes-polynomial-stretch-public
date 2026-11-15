import ExpandingCodes.Probability.SharpThreshold.Basic

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
