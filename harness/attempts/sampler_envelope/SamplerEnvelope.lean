import ExpandingCodes.Computation.RuntimeBounds

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

def samplerBucketCount (k n : ℕ) : ℕ := 2^Nat.log 2 (n/k)

theorem samplerBucketCount_le (k n : ℕ) : samplerBucketCount k n ≤ n+1 := by
  by_cases hz : n/k = 0
  · simp [samplerBucketCount,hz]
  · exact ((Nat.pow_log_le_self 2 hz).trans (Nat.div_le_self n k)).trans (Nat.le_succ n)

theorem samplerBucketCount_polynomial (k : ℕ) : PolynomialBound (samplerBucketCount k) :=
  (PolynomialBound.identity.add (PolynomialBound.const 1)).of_le (fun n _ => samplerBucketCount_le k n)

/-- One fixed polynomial envelope for actual sampler scalar values and table
heads. Every summand is a true size bound, not a machine instruction. -/
def samplerEnvelope (d k n : ℕ) : ℕ :=
  2 + ParameterPrograms.setupCounterBound d (n+1) + (2*k*d+d+k+1) +
    (fieldSize d n)^2 + (3*fieldExponent d n+1) + 2*fieldSize d n +
    (2*k*fieldSize d n*d*fieldSize d n+1) +
    (k*(fieldSize d n)^3*samplerBucketCount k n+1) + rowCount d n + n +
    rowCount d n*n + k*samplerBucketCount k n +
    SamplerTables.entropy d n k (Nat.log 2 (n/k))

structure SamplerEnvelopeCovers (d k n M : ℕ) : Prop where
  two : 2 ≤ M
  setup : ParameterPrograms.setupCounterBound d (n+1) ≤ M
  constants : 2*k*d+d+k+1 ≤ M
  square : (fieldSize d n)^2 ≤ M
  coefficients : 3*fieldExponent d n+1 ≤ M
  twiceField : 2*fieldSize d n ≤ M
  forms : 2*k*fieldSize d n*d*fieldSize d n+1 ≤ M
  hashes : k*(fieldSize d n)^3*samplerBucketCount k n+1 ≤ M
  rows : rowCount d n ≤ M
  input : n ≤ M
  output : rowCount d n*n ≤ M
  neighbors : k*samplerBucketCount k n ≤ M
  entropy : SamplerTables.entropy d n k (Nat.log 2 (n/k)) ≤ M

theorem samplerEnvelope_covers (d k n : ℕ) : SamplerEnvelopeCovers d k n (samplerEnvelope d k n) := by
  constructor <;> unfold samplerEnvelope <;> omega

theorem samplerEnvelope_polynomial (d k : ℕ) (hd : 0 < d) : PolynomialBound (samplerEnvelope d k) := by
  have hq := fieldSize_polynomial d hd
  have he := fieldExponent_polynomial d hd
  have hm := rowCount_polynomial d hd
  have hb := samplerBucketCount_polynomial k
  have hsetup := ((ParameterPrograms.setup_bounds_polynomial d).2.comp
    (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1))).toPolynomialBound
  have hforms := (((((PolynomialBound.const 2).mul (PolynomialBound.const k)).mul hq).mul
    (PolynomialBound.const d)).mul hq).add (PolynomialBound.const 1)
  have hhashes := (((PolynomialBound.const k).mul (hq.pow 3)).mul hb).add (PolynomialBound.const 1)
  exact ((((((((((((PolynomialBound.const 2).add hsetup).add
    (PolynomialBound.const (2*k*d+d+k+1))).add (hq.pow 2)).add
      (((PolynomialBound.const 3).mul he).add (PolynomialBound.const 1))).add
        ((PolynomialBound.const 2).mul hq)).add hforms).add hhashes).add hm).add
          PolynomialBound.identity).add (hm.mul PolynomialBound.identity)).add
            ((PolynomialBound.const k).mul hb)).add (samplerEntropy_polynomial d k hd)

#print axioms samplerEnvelope_covers
#print axioms samplerEnvelope_polynomial
end ExpandingCodes.PolynomialStretch
