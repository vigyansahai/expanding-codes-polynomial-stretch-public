import ExpandingCodes.Computation.TesterProgram
import ExpandingCodes.Computation.ParameterPrograms
import ExpandingCodes.Computation.PolynomialBounds
import ExpandingCodes.Computation.TapeRename

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterSuffix
open NKtLB ParameterPrograms
variable {R B : ℕ}

def eta (θ : ℚ) : ℚ := 1/2-θ/2
def loadLabels (c : ℕ) : ℕ := 2+raiseLabels c
def labels (θ : ℚ) : ℕ := loadLabels (eta θ).den+loadLabels (eta θ).num.toNat+54

/-- Rational constants are fixed in the finite code before n. The suffix
loads both by actual increments, then executes the physical rank comparison. -/
def program (θ : ℚ) (r : Fin 8 → Fin R) : TapeProgram R B (labels θ) :=
  TapeProgram.seq (TapeProgram.seq (loadConstant (r 2) (eta θ).den)
    (loadConstant (r 3) (eta θ).num.toNat))
      (TapeProgram.renameStorage r id (TesterProgram.rankThreshold (B := B)))

def constantsStore (θ : ℚ) (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  (d.setReg (r 2) (eta θ).den).setReg (r 3) (eta θ).num.toNat

def envelope (θ : ℚ) (M : ℕ) : ℕ := max M (max (eta θ).den (eta θ).num.toNat)
def timeBound (θ : ℚ) (M : ℕ) : ℕ :=
  2*M+2*(eta θ).den+2*(eta θ).num.toNat+6+100*(envelope θ M+1)^2

theorem program_stops (θ : ℚ) (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ timeBound θ M ∧
      (program θ r).Stops inp (d.toCfg (program (B := B) θ r).entry) t e ∧
      e.output = d.output ++ [decide (d.reg (r 0)*(eta θ).den ≤ (eta θ).num.toNat*d.reg (r 1))] := by
  obtain ⟨c,hc,hcs⟩ := loadConstant_stops (r 2) (eta θ).den inp d
  obtain ⟨f,hf,hfs⟩ := loadConstant_stops (r 3) (eta θ).num.toNat inp c.store
  have hpost : f.store = constantsStore θ r d := by rw [hfs,hcs]; rfl
  have h3 : c.store.reg (r 3) = d.reg (r 3) := by
    rw [hcs]
    simp [TapeStore.setReg,hr.ne (by decide : (3 : Fin 8) ≠ 2)]
  have hbound : ∀ j, f.store.reg j ≤ envelope θ M := by
    rw [hpost]
    apply FieldPrograms.setReg_bound
    · apply FieldPrograms.setReg_bound
      · intro j
        exact (hd j).trans (le_max_left _ _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  let small := f.store.projectStorage r (id : Fin B → Fin B)
  have hb : ∀ i, small.reg i ≤ envelope θ M := fun i => hbound (r i)
  obtain ⟨u,e,hu,he,heo,_⟩ := TesterProgram.rankThreshold_stops inp small (envelope θ M) hb
  obtain ⟨z,hz,hproj,hzo⟩ := he.liftStorage r (id : Fin B → Fin B) hr Function.injective_id
    (f.store.toCfg (TesterProgram.rankThreshold (B := B)).entry) rfl
  have hbit : decide (small.reg 0*small.reg 2 ≤ small.reg 3*small.reg 1) =
      decide (d.reg (r 0)*(eta θ).den ≤ (eta θ).num.toNat*d.reg (r 1)) := by
    have hreg : f.reg = (constantsStore θ r d).reg := congrArg TapeStore.reg hpost
    simp [small,TapeStore.projectStorage,hreg,constantsStore,TapeStore.setReg,hr.eq_iff]
  have houtput : small.output = d.output := by rw [show small.output = f.store.output from rfl,hpost]; rfl
  have hall := (hc.seq hf).seq hz
  refine ⟨(d.reg (r 2)+2*(eta θ).den+2)+1+
    (c.store.reg (r 3)+2*(eta θ).num.toNat+2)+1+u,
    z.mapPC (TapeProgram.rightLabel (loadLabels (eta θ).den+loadLabels (eta θ).num.toNat)),?_,?_,?_⟩
  · rw [h3]
    have := hd (r 2)
    have := hd (r 3)
    unfold timeBound
    omega
  · convert hall using 1 <;> rfl
  · change z.output = _
    rw [hzo,heo,houtput,hbit]

theorem timeBound_polynomial (θ : ℚ) : PolynomialBound (timeBound θ) := by
  have he : PolynomialBound (envelope θ) := PolynomialBound.identity.max
    ((PolynomialBound.const (eta θ).den).max (PolynomialBound.const (eta θ).num.toNat))
  have hleft := (((PolynomialBound.const 2).mul PolynomialBound.identity).add
    (PolynomialBound.const (2*(eta θ).den))).add (PolynomialBound.const (2*(eta θ).num.toNat))
  exact (hleft.add (PolynomialBound.const 6)).add
    ((PolynomialBound.const 100).mul ((he.add (PolynomialBound.const 1)).pow 2))

theorem program_canonical (θ : ℚ) (hθ : θ ≤ 1) (r : Fin 8 → Fin R)
    (hr : Function.Injective r) (d n : ℕ)
    (y : PolynomialStretch.Word (PolynomialStretch.rowCount d n))
    (inp : Inputs) (s : TapeStore R B) (M : ℕ) (hM : ∀ j, s.reg j ≤ M)
    (hrank : s.reg (r 0) = (EncodedGaussian.run
      (PolynomialStretch.BinaryField.indexOperations
        (PolynomialStretch.fieldExponent d n) (PolynomialStretch.fieldExponent_pos d n))
      (PolynomialStretch.binaryTestTable d n y)).1)
    (hm : s.reg (r 1) = PolynomialStretch.rowCount d n) :
    ∃ t e, t ≤ timeBound θ M ∧
      (program θ r).Stops inp (s.toCfg (program (B := B) θ r).entry) t e ∧
      e.output = s.output ++ [PolynomialStretch.rankTest (θ : ℝ)
        (PolynomialStretch.binaryGeometry d n) y] := by
  obtain ⟨t,e,ht,he,heo⟩ := program_stops θ r hr inp s M hM
  have hb : decide (s.reg (r 0)*(eta θ).den ≤ (eta θ).num.toNat*s.reg (r 1)) =
      PolynomialStretch.rankTest (θ : ℝ) (PolynomialStretch.binaryGeometry d n) y := by
    calc
      _ = PolynomialStretch.binaryRankTest θ d n y := by
        simp only [hrank,hm,eta,PolynomialStretch.binaryRankTest]
      _ = _ := PolynomialStretch.binaryRankTest_eq θ hθ d n y
  exact ⟨t,e,ht,he,by simpa only [hb] using heo⟩

#print axioms program_stops
#print axioms timeBound_polynomial
#print axioms program_canonical
end ExpandingCodes.Computation.TesterSuffix
