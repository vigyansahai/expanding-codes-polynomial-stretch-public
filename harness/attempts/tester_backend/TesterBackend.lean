import ExpandingCodes.Computation.GaussianDriverBounds
import ExpandingCodes.Computation.TesterSuffix
import ExpandingCodes.Computation.RuntimeBounds

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackend
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch

def suffixLayout : Fin 8 → Fin 64 := ![48,49,52,53,54,55,56,57]
theorem suffixLayout_injective : Function.Injective suffixLayout := by decide

/-- The entire actual Gaussian and acceptance suffix, on a fixed64-register
frame. The final tester lifts this into its larger Gram-construction frame. -/
def program (θ : ℚ) : TapeProgram 64 2 (4260+TesterSuffix.labels θ) :=
  TapeProgram.seq GaussianDriver.rankProgram (TesterSuffix.program θ suffixLayout)

def timeBound (θ : ℚ) (M : ℕ) : ℕ :=
  100000*(M+1)^9+1+TesterSuffix.timeBound θ M

theorem program_stops (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ) (inp : Inputs)
    (d : Store) (y : Word (rowCount degree n))
    (hc : GaussianDriver.Common (fieldExponent degree n) (fieldExponent_pos degree n)
      (rowCount degree n) M d)
    (B : Gaussian.Table (Fin (fieldSize degree n)) (rowCount degree n) (rowCount degree n))
    (ha : MatrixStored d 0 (binaryTestTable degree n y)) (hb : MatrixStored d 1 B) :
    ∃ t e, t ≤ timeBound θ M ∧ (program θ).Stops inp (d.toCfg (program θ).entry) t e ∧
      e.output = d.output ++ [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  obtain ⟨t,c,ht,hc,hcommon,hrank,_,_,hout⟩ := GaussianDriver.rankProgram_stops_canonical
    degree n M inp d y hc B ha hb
  have hr : c.store.reg (suffixLayout 0) = (EncodedGaussian.run
      (BinaryField.indexOperations (fieldExponent degree n) (fieldExponent_pos degree n))
      (binaryTestTable degree n y)).1 :=
    hrank.trans (binaryTestTable_rank degree n y).symm
  have hm : c.store.reg (suffixLayout 1) = rowCount degree n := hcommon.rows
  obtain ⟨s,e,hs,he,heo⟩ := TesterSuffix.program_canonical θ hθ suffixLayout suffixLayout_injective
    degree n y inp c.store M hcommon.state.bounded hr hm
  refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel 4260),?_,?_,?_⟩
  · unfold timeBound
    omega
  · convert hc.seq he using 1 <;> rfl
  · change e.output = _
    have ho : c.store.output = d.output := hout
    rw [heo,ho]

theorem timeBound_polynomial (θ : ℚ) : PolynomialBound (timeBound θ) :=
  ((((PolynomialBound.const 100000).mul
    ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 9)).add
      (PolynomialBound.const 1)).add (TesterSuffix.timeBound_polynomial θ))

#print axioms program_stops
#print axioms timeBound_polynomial
end ExpandingCodes.Computation.TesterBackend
