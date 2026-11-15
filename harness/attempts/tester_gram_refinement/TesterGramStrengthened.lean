import ExpandingCodes.Computation.TesterEvaluation
import ExpandingCodes.Computation.TesterInput
import ExpandingCodes.Computation.SamplerOdometer
import ExpandingCodes.Computation.ParameterSetup
import ExpandingCodes.Computation.SourceFieldSetup

set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB

/-- Scalar source workspace occupies low registers. The three d-tuples and their
separate countdowns occupy exactly 6*d additional registers. -/
abbrev Registers (d : ℕ) := Fin (80+6*d)

def low (d : ℕ) (i : Fin 80) : Registers d := ⟨i.val,by omega⟩

def digit (d : ℕ) (group : Fin 6) (i : Fin d) : Registers d :=
  ⟨80+group.val*d+i.val,by
    have hg : group.val*d ≤ 5*d := Nat.mul_le_mul_right d (by omega)
    have hi := i.isLt
    omega⟩

def scalar (d : ℕ) (i : Fin 33) : Registers d := low d ⟨i.val,by omega⟩

def termWorkspace (d : ℕ) (i : Fin 31) : Registers d := low d ⟨i.val,by omega⟩

/-- Result64, canonical degree65, sum66 and flag67. -/
def evaluationCaller (d : ℕ) : Fin 4 → Registers d := ![low d 64,low d 65,low d 66,low d 67]

def aDigits (d : ℕ) := List.ofFn (fun i : Fin d => (digit d 0 i,digit d 1 i))
def bDigits (d : ℕ) := List.ofFn (fun i : Fin d => (digit d 2 i,digit d 3 i))
def zDigits (d : ℕ) := List.ofFn (fun i : Fin d => (digit d 4 i,digit d 5 i))

def aEvaluation (d : ℕ) := TesterEvaluation.evaluate (B := 3) (scalar d) (evaluationCaller d)
  (List.ofFn fun i : Fin d => (digit d 0 i,digit d 4 i))

def bEvaluation (d : ℕ) := TesterEvaluation.evaluate (B := 3) (scalar d) (evaluationCaller d)
  (List.ofFn fun i : Fin d => (digit d 2 i,digit d 4 i))

/-- Physical input table lookup: zIndex73 and q23 are preserved, bit78 is output;
all remaining used registers are disposable scalar scratch outside the modulus. -/
def inputLookup (d : ℕ) : Fin 8 → Registers d :=
  ![low d 73,low d 23,low d 0,low d 1,low d 2,low d 4,low d 78,low d 5]

/-- Two actual bounded monomials followed by their product and field addition
into the separately preserved Gram accumulator69. -/
def maskedTerm (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (aEvaluation d) (TapeMacros.copy (B := 3) (low d 64) (low d 68) (low d 2)))
    (bEvaluation d)) (TapeMacros.copy (low d 69) (low d 30) (low d 2)))
    (SamplerProgram.term (termWorkspace d) (low d 68) (low d 64)))
    (TapeMacros.copy (low d 30) (low d 69) (low d 2))

/-- One point: look up its stored input bit, conditionally accumulate the actual
masked term, then advance the physical point odometer and flat point index. -/
def pointBody (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (SamplerEvaluation.lookup (B := 3) (inputLookup d) (2 : Fin 3))
    (TapeProgram.branchZero (low d 78) TapeProgram.skip (maskedTerm d)))
    (SamplerOdometer.program (low d 23) (low d 2) (zDigits d)))
    (TapeMacros.increment (low d 73))

/-- One Gram entry is recomputed by an eager m-point loop. Values are written
sequentially to buffer0 using their real q-cell physical width. -/
def pairBody (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
      (TapeMacros.clear (B := 3) (low d 69))
      (SamplerOdometer.initDigits (low d 23) (low d 2) (zDigits d)))
      (TapeMacros.clear (low d 73)))
      (TapeMacros.copy (low d 70) (low d 76) (low d 2)))
      (TapeProgram.countedLoop (pointBody d) (low d 76)))
      (TapeMacros.copy (low d 23) (low d 79) (low d 2)))
      (TapeArrays.writeBlock (low d 69) (low d 79) (0 : Fin 3)))
      (TapeMacros.increment (low d 77)))
      (SamplerOdometer.program (low d 23) (low d 2) (bDigits d)))
      (TapeMacros.increment (low d 72))

/-- One exponent-row: reinitialize b and run the actual m-column loop. -/
def rowBody (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (B := 3) (low d 23) (low d 2) (bDigits d))
    (TapeMacros.clear (low d 72)))
    (TapeMacros.copy (low d 70) (low d 75) (low d 2)))
    (TapeProgram.countedLoop (pairBody d) (low d 75)))
    (SamplerOdometer.program (low d 23) (low d 2) (aDigits d)))
    (TapeMacros.increment (low d 71))

/-- The complete finite eager m-by-m Gram loop. Runtime m is in register70,
q in register23, cutoff in65; y is already stored in buffer2 and buffer0's
head is at1 after its marker. This definition contains only finite compositions
of permitted scalar/control/one-cell source instructions. -/
def program (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (B := 3) (low d 23) (low d 2) (aDigits d))
    (TapeMacros.clear (low d 71)))
    (TapeMacros.clear (low d 77)))
    (TapeMacros.copy (low d 70) (low d 74) (low d 2)))
    (TapeProgram.countedLoop (rowBody d) (low d 74))

/-- Physical input loader allocation preserves the field environment. -/
def inputLayout (d : ℕ) : Fin 5 → Registers d :=
  ![low d 23,low d 79,low d 78,low d 5,low d 76]

/-- Eager input storage and all three bottom-marker writes are actual source.
The size parser has already consumed n+1 RO0 symbols; m70 and field setup are
ready. The canonical degree source is composed separately before `program`. -/
def input (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeArrays.initializeBuffer (R := 80+6*d) (0 : Fin 3))
    (TapeArrays.initializeBuffer (1 : Fin 3))) (TapeArrays.initializeBuffer (2 : Fin 3)))
    (TapeMacros.copy (low d 70) (low d 76) (low d 2)))
    (TesterInput.load (inputLayout d) (2 : Fin 3))

/-- Reuse the low64 Gaussian interface only after all field evaluations finish.
The true cell count m² is computed by the actual unary multiplier. -/
def gaussianMultiplyLayout (d : ℕ) : Fin 5 → Registers d :=
  ![low d 49,low d 40,low d 51,low d 0,low d 1]

/-- Source assembly and exact storage/time correctness of `program` are separate:
no correctness axiom, theorem hole or runtime field/array instruction is present
in this concrete finite source table. -/
theorem scalar_injective (d : ℕ) : Function.Injective (scalar d) := by
  intro i j hij
  exact Fin.ext (congrArg (Fin.val : Registers d → ℕ) hij)

#print axioms program

@[simp] theorem low_eq_iff (d : ℕ) (i j : Fin 80) : low d i=low d j ↔ i=j := by
  constructor
  · intro hij
    exact Fin.ext (congrArg (Fin.val : Registers d → ℕ) hij)
  · exact congrArg (low d)

theorem low_outside_scalar (d : ℕ) (i : Fin 80) (hi : 33 ≤ i.val) :
    ∀ j,low d i≠scalar d j := by
  intro j hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  simp only [low,scalar,Fin.val_mk] at hh
  omega

theorem digit_ne_low (d : ℕ) (group : Fin 6) (i : Fin d) (j : Fin 80) :
    digit d group i≠low d j := by
  intro hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  simp only [digit,low,Fin.val_mk] at hh
  omega

theorem digit_outside_scalar (d : ℕ) (group : Fin 6) (i : Fin d) :
    ∀ j,digit d group i≠scalar d j :=
  fun j => digit_ne_low d group i ⟨j.val,by omega⟩

theorem caller_injective (d : ℕ) : Function.Injective (evaluationCaller d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [evaluationCaller]

theorem caller_outside_scalar (d : ℕ) : ∀ i j,evaluationCaller d i≠scalar d j := by
  intro i j hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  fin_cases i <;> simp [evaluationCaller,scalar,low] at hh <;> omega

theorem digit_outside_caller (d : ℕ) (group : Fin 6) (i : Fin d) :
    ∀ j,digit d group i≠evaluationCaller d j := by
  intro j
  fin_cases j <;> exact digit_ne_low d group i _

/-- The eager Gram leaf performs two actual canonical monomials, saves the first
value, and uses the checked source field multiply/add to accumulate their product.
All point/exponent counters and every caller register above69 are preserved. -/
theorem maskedTerm_stops (d ell : ℕ) (h : 0<ell)
    (a b z : Fin ((2^ell)^d)) (acc : Fin (2^ell))
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (s : TapeStore (80+6*d) 3)
    (hs : ∀ i,s.reg i ≤ M)
    (henv : SamplerProgram.Environment (termWorkspace d) ell
      (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) s)
    (ha : ∀ i,s.reg (digit d 0 i)=(EncodedTester.digits (2^ell) d a i).val)
    (hb : ∀ i,s.reg (digit d 2 i)=(EncodedTester.digits (2^ell) d b i).val)
    (hz : ∀ i,s.reg (digit d 4 i)=(EncodedTester.digits (2^ell) d z i).val)
    (hacc : s.reg (low d 69)=acc.val) (hdM : d*((2^ell)-1) ≤ M) :
    ∃ t e,t ≤ 2*TesterEvaluation.timeBound d M+13300*(M+1)^6+28*M+32 ∧
      (maskedTerm d).Stops inp (s.toCfg (maskedTerm d).entry) t e ∧
      e.reg (low d 69)=((ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h).add
        ((ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h).mul
          (EncodedTester.evaluation (ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h) (s.reg (low d 65)) a z).1
          (EncodedTester.evaluation (ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h) (s.reg (low d 65)) b z).1) acc).val ∧
      SamplerProgram.Environment (termWorkspace d) ell
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) e.store ∧
      (∀ i : Fin 80,70 ≤ i.val → e.reg (low d i)=s.reg (low d i)) ∧
      (∀ g i,e.reg (digit d g i)=s.reg (digit d g i)) ∧
      (∀ i,e.reg i ≤ M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s ∧
      e.reg (low d 65)=s.reg (low d 65) := by
  let O := ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h
  let A := (EncodedTester.evaluation O (s.reg (low d 65)) a z).1
  let C := (EncodedTester.evaluation O (s.reg (low d 65)) b z).1
  have hr := scalar_injective d
  have hc := caller_injective d
  have hcr := caller_outside_scalar d
  have hdigit g i : (∀ j,digit d g i≠scalar d j) ∧ (∀ j,digit d g i≠evaluationCaller d j) :=
    ⟨digit_outside_scalar d g i,digit_outside_caller d g i⟩
  obtain ⟨t₁,c₁,ht₁,h₁,hv₁,he₁,hf₁,hb₁,hd₁⟩ := TesterEvaluation.evaluate_canonical_stops
    (scalar d) hr (evaluationCaller d) hc hcr (digit d 0) (digit d 4)
    (hdigit 0) (hdigit 4) inp ell h a z M hM s hs henv ha hz hdM
  have hf₁low (i : Fin 80) (hi : 68 ≤ i.val ∨ i=65) : c₁.reg (low d i)=s.reg (low d i) := by
    apply hf₁
    · apply low_outside_scalar
      rcases hi with hi|rfl <;> simp_all <;> omega
    all_goals simp only [evaluationCaller,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals apply (low_eq_iff d _ _).not.mpr
    all_goals rcases hi with hi|rfl <;> apply Fin.ne_of_val_ne <;> simp_all <;> omega
  have hf₁digit g i : c₁.reg (digit d g i)=s.reg (digit d g i) :=
    hf₁ _ (digit_outside_scalar d g i) (digit_outside_caller d g i 0)
      (digit_outside_caller d g i 2) (digit_outside_caller d g i 3)
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := SamplerEvaluation.copy_stops_bound (low d 64) (low d 68) (low d 2)
    (by simp) (by simp) (by simp) inp M c₁.store hb₁
  have he₂ : SamplerProgram.Environment (termWorkspace d) ell
      (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) c₂.store := by
    rw [hs₂]
    exact (he₁.setExternal (low d 68) _ (fun i => low_outside_scalar d 68 (by decide) ⟨i.val,by omega⟩)).setReg
      (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 2 0 (by decide)
  have hf₂ (j : Registers d) (hj : j≠low d 68) (hj₂ : j≠low d 2) : c₂.reg j=c₁.reg j := by
    change c₂.store.reg j=_
    rw [hs₂]; simp [TapeStore.setReg,hj,hj₂]
  have hv₂ : c₂.reg (low d 68)=A.val := by
    change c₂.store.reg (low d 68)=_
    rw [hs₂]
    simpa [TapeStore.setReg,A,O,evaluationCaller] using hv₁
  obtain ⟨t₃,c₃,ht₃,h₃,hv₃,he₃,hf₃,hb₃,hd₃⟩ := TesterEvaluation.evaluate_canonical_stops
    (scalar d) hr (evaluationCaller d) hc hcr (digit d 2) (digit d 4)
    (hdigit 2) (hdigit 4) inp ell h b z M hM c₂.store hb₂ he₂
    (by intro i; change c₂.reg (digit d 2 i)=_; rw [hf₂ _ (digit_ne_low _ _ _ _) (digit_ne_low _ _ _ _),hf₁digit]; exact hb i)
    (by intro i; change c₂.reg (digit d 4 i)=_; rw [hf₂ _ (digit_ne_low _ _ _ _) (digit_ne_low _ _ _ _),hf₁digit]; exact hz i) hdM
  have hf₃low (i : Fin 80) (hi : 68 ≤ i.val ∨ i=65) : c₃.reg (low d i)=c₂.reg (low d i) := by
    apply hf₃
    · apply low_outside_scalar
      rcases hi with hi|rfl <;> simp_all <;> omega
    all_goals simp only [evaluationCaller,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals apply (low_eq_iff d _ _).not.mpr
    all_goals rcases hi with hi|rfl <;> apply Fin.ne_of_val_ne <;> simp_all <;> omega
  have hf₃digit g i : c₃.reg (digit d g i)=c₂.reg (digit d g i) :=
    hf₃ _ (digit_outside_scalar d g i) (digit_outside_caller d g i 0)
      (digit_outside_caller d g i 2) (digit_outside_caller d g i 3)
  have hdeg : c₂.reg (low d 65)=s.reg (low d 65) :=
    (hf₂ _ (by simp) (by simp)).trans (hf₁low 65 (Or.inr rfl))
  have hv₃' : c₃.reg (low d 64)=C.val := by
    simpa only [evaluationCaller,Matrix.cons_val_zero,Matrix.cons_val_one,hdeg,C,O] using hv₃
  have hv₃A : c₃.reg (low d 68)=A.val := (hf₃low 68 (Or.inl (by decide))).trans hv₂
  have hv₃acc : c₃.reg (low d 69)=acc.val := by
    rw [hf₃low 69 (Or.inl (by decide)),hf₂ _ (by simp) (by simp),hf₁low 69 (Or.inl (by decide))]
    exact hacc
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄⟩ := SamplerEvaluation.copy_stops_bound (low d 69) (low d 30) (low d 2)
    (by simp) (by simp) (by simp) inp M c₃.store hb₃
  have he₄ : SamplerProgram.Environment (termWorkspace d) ell
      (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) c₄.store := by
    rw [hs₄]
    exact (he₃.setReg (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 30 _ (by decide)).setReg
      (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 2 0 (by decide)
  have hv₄ (i : Fin 80) : c₄.reg (low d i)=if i=2 then 0 else if i=30 then acc.val else c₃.reg (low d i) := by
    change c₄.store.reg (low d i)=_
    rw [hs₄]
    change Function.update (Function.update c₃.reg (low d 30) (c₃.reg (low d 69))) (low d 2) 0 (low d i)=_
    rw [hv₃acc]
    simp [Function.update,low_eq_iff]
  obtain ⟨t₅,c₅,ht₅,h₅,hv₅,he₅,hf₅,hb₅,hd₅⟩ := SamplerProgram.term_stops (termWorkspace d)
    (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) (low d 68) (low d 64)
    (fun i => low_outside_scalar d 68 (by decide) ⟨i.val,by omega⟩)
    (fun i => low_outside_scalar d 64 (by decide) ⟨i.val,by omega⟩) inp ell h
    (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) A C acc M hM c₄.store hb₄ he₄
    (by simpa [termWorkspace,hv₄] using hv₃A) (by simpa [termWorkspace,hv₄] using hv₃')
    (by simp [termWorkspace,hv₄])
  obtain ⟨t₆,e,ht₆,h₆,hs₆,heb⟩ := SamplerEvaluation.copy_stops_bound (low d 30) (low d 69) (low d 2)
    (by simp) (by simp) (by simp) inp M c₅.store hb₅
  have hall := ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆
  refine ⟨t₁+1+t₂+1+t₃+1+t₄+1+t₅+1+t₆,_,?_,hall,?_,?_,?_,?_,heb,?_,?_⟩
  · omega
  · change e.store.reg (low d 69)=_
    rw [hs₆]
    simpa [TapeStore.setReg,termWorkspace,O,A,C,ExpandingCodes.PolynomialStretch.BinaryField.indexOperations] using hv₅
  · rw [hs₆]
    exact (he₅.setExternal (low d 69) _ (fun i => low_outside_scalar d 69 (by decide) ⟨i.val,by omega⟩)).setReg
      (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 2 0 (by decide)
  · intro i hi
    change e.store.reg (low d i)=_
    rw [hs₆]
    simp only [TapeStore.setReg]
    rw [Function.update_of_ne (by apply (low_eq_iff d _ _).not.mpr; intro hh; have hv := congrArg Fin.val hh; norm_num at hv; omega),
      Function.update_of_ne (by apply (low_eq_iff d _ _).not.mpr; intro hh; have hv := congrArg Fin.val hh; norm_num at hv; omega)]
    rw [hf₅ _ (fun j => low_outside_scalar d i (by omega) ⟨j.val,by omega⟩)]
    change c₄.reg (low d i)=_
    rw [hv₄]
    simp only [show i≠2 by intro hh; subst i; norm_num at hi,show i≠30 by intro hh; subst i; norm_num at hi,if_false]
    rw [hf₃low i (Or.inl (by omega)),hf₂ _ (by apply (low_eq_iff d _ _).not.mpr; intro hh; subst i; norm_num at hi)
      (by apply (low_eq_iff d _ _).not.mpr; intro hh; subst i; norm_num at hi),hf₁low i (Or.inl (by omega))]
  · intro g i
    change e.store.reg (digit d g i)=_
    rw [hs₆]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low _ _ _ _)]
    rw [hf₅ _ (fun j => digit_ne_low d g i ⟨j.val,by omega⟩)]
    change c₄.store.reg (digit d g i)=_
    rw [hs₄]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low _ _ _ _)]
    rw [hf₃digit,hf₂ _ (digit_ne_low _ _ _ _) (digit_ne_low _ _ _ _),hf₁digit]
  · change FieldConvolution.tapeData e.store=_
    rw [hs₆]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₅,hs₄]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₃,hs₂]
    simp only [FieldConvolution.tapeData_setReg]
    exact hd₁
  · change e.store.reg (low d 65)=_
    rw [hs₆]
    simp only [TapeStore.setReg,Function.update_of_ne (show low d 65≠low d 2 by simp),
      Function.update_of_ne (show low d 65≠low d 69 by simp)]
    rw [hf₅ _ (fun j => low_outside_scalar d 65 (by decide) ⟨j.val,by omega⟩)]
    change c₄.store.reg (low d 65)=_
    rw [hs₄]
    simp only [TapeStore.setReg,Function.update_of_ne (show low d 65≠low d 2 by simp),
      Function.update_of_ne (show low d 65≠low d 30 by simp)]
    rw [hf₃low 65 (Or.inr rfl),hf₂ _ (by simp) (by simp),hf₁low 65 (Or.inr rfl)]

#print axioms maskedTerm_stops


/-- Actual initial size parser and parameter arithmetic use only the static
construction dimension; k=1 is sufficient because tester buckets are unused. -/
def parameterLayout (d : ℕ) (i : Fin 14) : Registers d := low d ⟨i.val,by omega⟩

def fieldSetupLayout (d : ℕ) (i : Fin 32) : Registers d := low d ⟨i.val,by omega⟩

def setup (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (ParameterPrograms.setupInput (B := 3) (parameterLayout d) d 1)
    (TapeMacros.copy (low d 4) (low d 70) (low d 79)))
    (TapeMacros.copy (low d 2) (low d 20) (low d 79)))
    (TapeMacros.copy (low d 3) (low d 23) (low d 79)))
    (SourceFieldSetup.setup (fieldSetupLayout d))

def degreeLayout (d : ℕ) : Fin 5 → Registers d :=
  ![low d 23,low d 0,low d 1,low d 2,low d 65]

/-- Full actual finite tester matrix prefix, fixed before runtime n,q,ell,m,y.
It parses sizeInput, computes all size/field data and the canonical modulus,
stores the received word, computes the cutoff, and executes the eager Gram code.
The transitive execution refinement of the m³ loops remains a separate obligation. -/
def construct (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (setup d) (input d))
    (TesterEvaluation.degree (degreeLayout d) d)) (program d)

#print axioms construct
end ExpandingCodes.Computation.TesterGram
