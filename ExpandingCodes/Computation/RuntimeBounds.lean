import ExpandingCodes.Computation.PolynomialBounds
import ExpandingCodes.Computation.ParameterPolynomial

set_option autoImplicit false

namespace ExpandingCodes.Computation

theorem ParameterPrograms.PolynomialMajorant.toPolynomialBound {f : ℕ → ℕ}
    (hf : ParameterPrograms.PolynomialMajorant f) : PolynomialBound f := by
  obtain ⟨C,a,hf⟩ := hf
  exact ⟨C,a,fun n _ => hf n⟩

/-- Finitely many excluded sizes only affect the numerical coefficient.
This arithmetic conversion asserts no source execution by itself. -/
theorem PolynomialBound.toMajorant {f : ℕ → ℕ} (hf : PolynomialBound f) :
    ParameterPrograms.PolynomialMajorant f := by
  obtain ⟨C,a,hf⟩ := hf
  let D := C+f 0+f 1
  refine ⟨D,a,?_⟩
  intro n
  by_cases hn : 2 ≤ n
  · exact (hf n hn).trans (Nat.mul_le_mul_right _ (by dsimp [D]; omega))
  · have hcases : n = 0 ∨ n = 1 := by omega
    have hp : 1 ≤ (n+1)^a := one_le_pow₀ (by omega)
    have hD : D ≤ D*(n+1)^a := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left D hp
    apply le_trans (b := D) ?_ hD
    rcases hcases with rfl | rfl <;> dsimp [D] <;> omega

theorem PolynomialBound.comp {f g : ℕ → ℕ} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f (g n)) :=
  (hf.toMajorant.comp hg.toMajorant).toPolynomialBound

end ExpandingCodes.Computation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

/-- A common shape for true source counter/head envelopes in the final
sampler. The fixed parameters and exponent are allowed in its coefficient. -/
theorem sampler_runtime_envelope_polynomial (d C a : ℕ) (hd : 0 < d) :
    PolynomialBound (fun n => C*(rowCount d n+n+1)^a) :=
  (PolynomialBound.const C).mul
    ((((rowCount_polynomial d hd).add PolynomialBound.identity).add (PolynomialBound.const 1)).pow a)

/-- Once the actual tester source is bounded in m+n, fixed scalar envelope
substitution and all finite sums/products/powers preserve that requirement. -/
theorem tester_runtime_envelope_polynomial (C a : ℕ) :
    PolynomialBound (fun x => C*(x+1)^a) :=
  (PolynomialBound.const C).mul ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow a)

#print axioms PolynomialBound.toMajorant
#print axioms sampler_runtime_envelope_polynomial
end ExpandingCodes.PolynomialStretch
