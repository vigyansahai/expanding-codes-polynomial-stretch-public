import ExpandingCodes.Computation.EncodedSampler
import ExpandingCodes.Computation.PolynomialBounds
import ExpandingCodes.Computation.SourceBridge

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

/-- A concrete finite source program implementing the explicit indexed sampler
gives the entire canonical sampler clause. Its actual execution and numerical
step bound are hypotheses; random-tape length, exact law, compiler overhead,
and the sufficiently-large-size threshold are proved here. -/
theorem binary_sampler_of_source {R B L : ℕ} (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2)
    (P : TapeProgram R B L) (time : ℕ → ℕ) (N : ℕ)
    (htime : PolynomialBound time)
    (hsource : ∀ n ≥ N, ∀ ω : List Bool,
      ∃ t ≤ time n,
        P.halted (P.run ⟨sizeInput n, [], [], ω⟩ t) ∧
          (P.run ⟨sizeInput n, [], [], ω⟩ t).output =
            matrixBits (binarySamplerFromInput (dimension (θ : ℝ)) n (arity (θ : ℝ))
              (Nat.log 2 (n/arity (θ : ℝ))) ⟨sizeInput n, [], [], ω⟩)) :
    SamplerImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  let d := dimension (θ : ℝ)
  let k := arity (θ : ℝ)
  have hd : 0 < d := (by decide : 0 < 4).trans_le (dimension_ge_four (θ : ℝ) hθ)
  obtain ⟨C,a,hbound⟩ := common_polynomial_envelope htime (samplerEntropy_polynomial d k hd)
  let N' := max N (max 2 k)
  have hN' : 2 ≤ N' := (le_max_left 2 k).trans (le_max_right N (max 2 k))
  apply samplerImplementation_of_tape θ (fun n => binaryGeometry d n) P C a N' hN'
    (fun n ω => binarySamplerFromInput d n k (Nat.log 2 (n/k))
      ⟨sizeInput n, [], [], List.ofFn ω⟩)
  · intro n hn ω
    have hnN : N ≤ n := (le_max_left N (max 2 k)).trans hn
    have hn2 : 2 ≤ n := hN'.trans hn
    obtain ⟨t,ht,hh,hout⟩ := hsource n hnN (List.ofFn ω)
    exact ⟨t,ht.trans (hbound n hn2).1,hh,hout⟩
  · intro n hn G
    have hn2 : 2 ≤ n := hN'.trans hn
    have hkn : k ≤ n := (le_max_right 2 k).trans ((le_max_right N (max 2 k)).trans hn)
    have hkq : k ≤ fieldSize d n := hkn.trans ((show n ≤ n^(2*d) from by
      calc n = n^1 := by simp
           _ ≤ n^(2*d) := Nat.pow_le_pow_right (by omega) (by omega)).trans
        (fieldSize_lower d n))
    exact binarySamplerFromInput_law (θ : ℝ) n _ hkq (hbound n hn2).2 G

#print axioms binary_sampler_of_source
end ExpandingCodes.PolynomialStretch
