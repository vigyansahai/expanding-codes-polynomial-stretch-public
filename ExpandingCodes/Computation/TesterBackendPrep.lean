import ExpandingCodes.Computation.TesterBackend
import ExpandingCodes.Computation.ZeroTables
import ExpandingCodes.Computation.TapeRename
import ExpandingCodes.Computation.SamplerEvaluation

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendPrep
open NKtLB UnaryArithmetic FieldPrograms TapeArrays GaussianProgram
open ExpandingCodes.PolynomialStretch

abbrev BigStore := TapeStore 80 3
abbrev Pair := Fin 80 × Fin 80

def copyLabels : List Pair → ℕ
  | [] => 1
  | _::ps => 11+copyLabels ps

def copies : (ps : List Pair) → TapeProgram 80 3 (copyLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (TapeMacros.copy p.1 p.2 79) (copies ps)

def copyResult : List Pair → BigStore → BigStore
  | [],d => d
  | p::ps,d => copyResult ps ((d.setReg p.2 (d.reg p.1)).setReg 79 0)

def Valid (ps : List Pair) : Prop :=
  ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ 79 ∧ p.2 ≠ 79

theorem copies_stops (ps : List Pair) (hp : Valid ps) (inp : Inputs)
    (d : BigStore) (M : ℕ) (hd : ∀ r,d.reg r ≤ M) :
    ∃ t e, t ≤ ps.length*(7*M+8) ∧
      (copies ps).Stops inp (d.toCfg (copies ps).entry) t e ∧
      e.store = copyResult ps d ∧ ∀ r,e.reg r ≤ M := by
  induction ps generalizing d with
  | nil => exact ⟨0,d.toCfg ⟨0,by decide⟩,by simp,TapeProgram.skip_stops inp d,rfl,hd⟩
  | cons p ps ih =>
    have hv := hp p (by simp)
    obtain ⟨t,c,ht,hc,hcs,hcb⟩ := SamplerEvaluation.copy_stops_bound
      p.1 p.2 79 hv.1 hv.2.1 hv.2.2 inp M d hd
    obtain ⟨s,e,hs,he,hes,heb⟩ := ih (by
      intro p hp'; exact hp p (by simp [hp'])) c.store hcb
    refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel 11),?_,?_,?_,heb⟩
    · rw [List.length_cons,Nat.succ_mul]
      omega
    · exact hc.seq he
    · change e.store = _
      rw [hes,hcs]
      rfl

theorem copyResult_data (ps : List Pair) (d : BigStore) :
    FieldConvolution.tapeData (copyResult ps d) = FieldConvolution.tapeData d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih => simpa [copyResult] using ih ((d.setReg p.2 (d.reg p.1)).setReg 79 0)

def metadataPairs : List Pair := [(23,0),(24,36),(19,37),(3,38),(70,40),(70,49)]
theorem metadataPairs_valid : Valid metadataPairs := by
  intro p hp
  simp [metadataPairs] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by decide,by decide,by decide⟩

def beforeZero (d : BigStore) : BigStore :=
  multiplyStore (multiplyStore (copyResult metadataPairs d) 70 70 51 52 53) 51 0 54 55 56

/-- Fixed finite metadata copies, two runtime unary multiplications, and the
physical spare-matrix zero fill. No matrix or runtime size is a code parameter. -/
def program : TapeProgram 80 3 118 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (copies metadataPairs)
    (multiply 70 70 51 52 53)) (multiply 51 0 54 55 56)) (ZeroTables.program 54 1)

def result (d : BigStore) : BigStore :=
  ZeroTables.result 54 1 (d.reg 70*d.reg 70*d.reg 23) (beforeZero d)

def registerResult (d : BigStore) : BigStore :=
  (((((((((((((d.setReg 0 (d.reg 23)).setReg 36 (d.reg 24)).setReg 37 (d.reg 19)).setReg 38 (d.reg 3)).setReg 40 (d.reg 70)).setReg 49 (d.reg 70)).setReg 79 0).setReg 51 (d.reg 70*d.reg 70)).setReg 52 0).setReg 53 0).setReg 54 (d.reg 70*d.reg 70*d.reg 23)).setReg 55 0).setReg 56 0)

theorem beforeZero_reg (d : BigStore) :
    (beforeZero d).reg = (registerResult d).reg := by
  simp only [beforeZero,metadataPairs,copyResult,multiplyStore,registerResult,TapeStore.setReg]
  funext r
  by_cases h79 : r = 79
  · subst r; simp
  · simp [Function.update,h79]


theorem beforeZero_data (d : BigStore) :
    FieldConvolution.tapeData (beforeZero d) = FieldConvolution.tapeData d := by
  simp only [beforeZero,multiplyStore,FieldConvolution.tapeData_setReg,copyResult_data]

theorem program_stops (inp : Inputs) (d : BigStore) (M : ℕ)
    (hd : ∀ r,d.reg r ≤ M) (hq : 0 < d.reg 23)
    (hn : d.reg 70*d.reg 70*d.reg 23 ≤ M) :
    ∃ t e, t ≤ 150*(M+1)^2 ∧ program.Stops inp (d.toCfg program.entry) t e ∧
      e.store = result d ∧ ∀ r,e.reg r ≤ M := by
  have hsq : d.reg 70*d.reg 70 ≤ M := by
    exact (Nat.le_mul_of_pos_right _ hq).trans hn
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copies_stops metadataPairs metadataPairs_valid inp d M hd
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂⟩ := multiply_stops_polynomial 70 70 51 52 53
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) inp c₁.store M
    (hb₁ _) (hb₁ _) (hb₁ _) (hb₁ _) (hb₁ _)
  have h70 : c₁.reg 70 = d.reg 70 := by
    change c₁.store.reg 70 = _
    rw [hs₁]
    simp [metadataPairs,copyResult,TapeStore.setReg]
  have hb₂ : ∀ r,c₂.reg r ≤ M := by
    change ∀ r,c₂.store.reg r ≤ M
    rw [hs₂]
    apply setReg_bound
    · apply setReg_bound
      · apply setReg_bound _ _ _ M hb₁
        simpa only [h70] using hsq
      · omega
    · omega
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃⟩ := multiply_stops_polynomial 51 0 54 55 56
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) inp c₂.store M
    (hb₂ _) (hb₂ _) (hb₂ _) (hb₂ _) (hb₂ _)
  have hpre : c₃.store = beforeZero d := by rw [hs₃,hs₂,hs₁]; rfl
  have hpreBound : ∀ r,(beforeZero d).reg r ≤ M := by
    rw [beforeZero_reg]
    unfold registerResult
    repeat apply setReg_bound
    all_goals first | exact hd | exact hd _ | exact hsq | exact hn | omega
  have h54 : c₃.reg 54 = d.reg 70*d.reg 70*d.reg 23 := by
    change c₃.store.reg 54 = _
    rw [hpre,beforeZero_reg]
    simp [registerResult,TapeStore.setReg]
  have h₄ := ZeroTables.program_stops 54 1 (d.reg 70*d.reg 70*d.reg 23) inp c₃.store h54
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨t₁+1+t₂+1+t₃+1+(2*(d.reg 70*d.reg 70*d.reg 23)+1),_,?_,hall,?_,?_⟩
  · have hh : metadataPairs.length = 6 := rfl
    rw [hh] at ht₁
    nlinarith
  · change ZeroTables.result 54 1 _ c₃.store = result d
    rw [hpre]
    rfl
  · change ∀ r,(ZeroTables.result 54 1 _ c₃.store).reg r ≤ M
    rw [hpre]
    exact ZeroTables.result_bound _ _ _ _ _ hpreBound

#print axioms program_stops
end ExpandingCodes.Computation.TesterBackendPrep
