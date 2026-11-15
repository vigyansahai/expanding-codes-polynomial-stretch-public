import ExpandingCodes.Computation.RuntimeBounds

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

theorem setupCounterBound_mono (d : ℕ) : Monotone (ParameterPrograms.setupCounterBound d) := by
  intro a b hab
  unfold ParameterPrograms.setupCounterBound ParameterPrograms.floorCounterBound
    ParameterPrograms.setupBound₃ ParameterPrograms.setupBound₂ ParameterPrograms.setupBound₁
    ParameterPrograms.powerCounterBound ParameterPrograms.ceilingCounterBound
  gcongr

/-- A fixed polynomial in the tester's input-plus-output dimension. It covers
physical table lengths, scalar values and the complete parameter setup. -/
def testerEnvelope (d x : ℕ) : ℕ :=
  2+ParameterPrograms.setupCounterBound d (x+1)+(d+1)*(x+1)^3+3*(x+1)+1

structure TesterEnvelopeCovers (d n M : ℕ) : Prop where
  two : 2 ≤ M
  setup : ParameterPrograms.setupCounterBound d (n+1) ≤ M
  rows : rowCount d n+1 ≤ M
  input : n+1 ≤ M
  square : (fieldSize d n)^2 ≤ M
  coefficients : 3*fieldExponent d n+1 ≤ M
  twiceField : 2*fieldSize d n ≤ M
  gram : 1+rowCount d n*rowCount d n*fieldSize d n ≤ M
  word : 1+rowCount d n*fieldSize d n ≤ M
  digitSum : d*(fieldSize d n-1) ≤ M
  cutoff : (d-3)*(fieldSize d n-1) ≤ M

theorem testerEnvelope_covers (d n : ℕ) (hd : 0 < d) :
    TesterEnvelopeCovers d n (testerEnvelope d (rowCount d n+n)) := by
  let x := rowCount d n+n
  have hm : rowCount d n ≤ x+1 := by omega
  have hn : n ≤ x := by omega
  have hqrow : fieldSize d n ≤ rowCount d n := Nat.le_self_pow hd.ne' _
  have hq : fieldSize d n ≤ x+1 := hqrow.trans hm
  have he : fieldExponent d n ≤ x+1 :=
    (Nat.lt_two_pow_self : fieldExponent d n < 2^fieldExponent d n).le.trans hq
  have hcube : x+1 ≤ (x+1)^3 := Nat.le_self_pow (by decide) _
  have hc : (x+1)^3 ≤ (d+1)*(x+1)^3 := Nat.le_mul_of_pos_left _ (by omega)
  have hprod : rowCount d n*rowCount d n*fieldSize d n ≤ (x+1)^3 := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul hm hm) hq
    nlinarith only [h]
  have hword : rowCount d n*fieldSize d n ≤ (x+1)^3 := by
    have h := Nat.mul_le_mul hm hq
    have hx : 1 ≤ x+1 := by omega
    nlinarith
  have hsq : (fieldSize d n)^2 ≤ (x+1)^3 := by
    have h := Nat.mul_le_mul hq hq
    have hx : 1 ≤ x+1 := by omega
    nlinarith
  have hsum : d*(fieldSize d n-1) ≤ (d+1)*(x+1)^3 :=
    Nat.mul_le_mul (Nat.le_succ d) ((Nat.sub_le _ _).trans (hq.trans hcube))
  have hcut : (d-3)*(fieldSize d n-1) ≤ d*(fieldSize d n-1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hsetup := setupCounterBound_mono d (show n+1 ≤ x+1 by omega)
  constructor <;> change _ ≤ testerEnvelope d x <;> unfold testerEnvelope <;> omega

theorem testerEnvelope_polynomial (d : ℕ) : PolynomialBound (testerEnvelope d) := by
  have hsetup := ((ParameterPrograms.setup_bounds_polynomial d).2.comp
    (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1))).toPolynomialBound
  exact (((((PolynomialBound.const 2).add hsetup).add
    ((PolynomialBound.const (d+1)).mul ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 3))).add
      ((PolynomialBound.const 3).mul (PolynomialBound.identity.add (PolynomialBound.const 1)))).add
        (PolynomialBound.const 1))

#print axioms testerEnvelope_covers
#print axioms testerEnvelope_polynomial
end ExpandingCodes.PolynomialStretch
