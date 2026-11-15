import ExpandingCodes.Computation.GaussianProgram
import ExpandingCodes.Computation.SamplerOdometer

set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianPivot
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch

/-- A fixed finite embedding: scanned pivot6 is preserved, its inverse goes
to persistent50, and all other Gaussian caller registers40..63 stay outside. -/
def inverseLayout (i : Fin 31) : Fin 64 :=
  #v[6,1,2,38,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,37,19,20,21,0,36,22,23,50,24,25,26][i.val]

set_option maxRecDepth 10000 in
theorem inverseLayout_injective : Function.Injective inverseLayout := by decide

set_option maxRecDepth 10000 in
theorem inverseLayout_frame : ∀ r : Fin 64, 40 ≤ r.val → r ≠ 50 →
    ∀ i : Fin 31, r ≠ inverseLayout i := by decide

def invertPivot : TapeProgram 64 2 418 := SourceFieldArithmetic.inverse inverseLayout

structure InverseOutcome (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell))
    (d e : Store) (M : ℕ) : Prop where
  value : e.reg 50 = (BinaryField.inverseIndex ell h a).val
  pivot : e.reg 6 = d.reg 6
  setup : FieldSetup ell h e
  frame : ∀ r : Fin 64, 40 ≤ r.val → r ≠ 50 → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : TapeStore.SamePayload e d
  heads : e.bufferHead = d.bufferHead

/-- The actual 418-label exhaustive finite-field inverse routine, physically
mapped into the Gaussian driver's fixed register frame. -/
theorem invertPivot_stops (ell : ℕ) (h : 0 < ell) (inp : Inputs)
    (d : Store) (M : ℕ) (hs : FieldSetup ell h d) (hd : ∀ r, d.reg r ≤ M)
    (a : Fin (2^ell)) (ha : d.reg 6 = a.val) :
    ∃ t e, t ≤ 20000*(M+1)^7 ∧
      invertPivot.Stops inp (d.toCfg invertPivot.entry) t e ∧
      InverseOutcome ell h a d e.store M := by
  rcases hs with ⟨hq,hQ,hN,hm⟩
  have hM : 1 ≤ M := by
    have hp : 0 < 2^ell := pow_pos (by decide) ell
    have hb := hd 0
    omega
  have hi : SourceFieldArithmetic.InverseSetup inverseLayout ell h a d :=
    ⟨ha,hm,hN,hq,hQ⟩
  obtain ⟨t,e,ht,he,_,hv,hinput,houtside,hbound,htape⟩ := SourceFieldArithmetic.inverse_stops
    inverseLayout inverseLayout_injective inp ell h a M hM d hd hi
  refine ⟨t,e,ht,he,?_⟩
  have hro : e.store.roHead = d.roHead := congrArg Prod.fst htape
  have houtput : e.store.output = d.output := congrArg (fun x => x.2.1) htape
  have hbuffer : e.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) htape
  have hheads : e.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) htape
  refine ⟨hv,hinput 0 (by simp),?_,?_,hbound,⟨hro,houtput,?_⟩,hheads⟩
  · refine ⟨?_,?_,?_,?_⟩
    · exact (hinput 23 (by simp)).trans hq
    · exact (hinput 24 (by simp)).trans hQ
    · exact (hinput 19 (by simp)).trans hN
    · exact (hinput 3 (by simp)).trans hm
  · intro r hr hr₅₀
    exact houtside r (inverseLayout_frame r hr hr₅₀)
  · intro b k
    rw [hbuffer]

def coordinateDigits : List (SamplerOdometer.Digit 64) := [(43,52),(53,54)]

theorem coordinateDigits_nodup :
    ((40 : Fin 64)::59::SamplerOdometer.used coordinateDigits).Nodup := by decide

def coordinateStep : TapeProgram 64 2 43 := SamplerOdometer.program 40 59 coordinateDigits

private def decidablePreserves {R B L : ℕ} (r : Fin R) (i : TapeInstr R B L) :
    Decidable (TapeProgram.preservesRegister r i) := by
  cases i <;> simp only [TapeProgram.preservesRegister] <;> infer_instance

set_option maxRecDepth 10000 in
theorem coordinateStep_fresh : coordinateStep.Fresh 55 := by
  unfold TapeProgram.Fresh
  letI (j : Fin 43) : Decidable (TapeProgram.preservesRegister 55 (coordinateStep.code j)) :=
    decidablePreserves 55 (coordinateStep.code j)
  decide

def OutsideCoordinates (r : Fin 64) : Prop :=
  r ∉ ([43,52,53,54,55,58,59] : List (Fin 64))

instance (r : Fin 64) : Decidable (OutsideCoordinates r) := by
  unfold OutsideCoordinates
  infer_instance

theorem coordinateOutside (r : Fin 64) (hr : OutsideCoordinates r) :
    r ≠ 59 ∧ r ∉ SamplerOdometer.used coordinateDigits ∧ r ≠ 55 ∧ r ≠ 58 := by
  simp only [OutsideCoordinates,coordinateDigits,SamplerOdometer.used,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hr ⊢
  tauto

structure CoordinateInvariant (base : Store) (M remaining : ℕ) (s : Store) : Prop where
  remaining_le : remaining ≤ base.reg 2
  bounded : ∀ r, s.reg r ≤ M
  valid : SamplerOdometer.Valid 40 coordinateDigits s
  radix : s.reg 40 = base.reg 40
  number : Nat.ofDigits (base.reg 40) (SamplerOdometer.readings coordinateDigits s) =
    base.reg 2-remaining
  frame : ∀ r, OutsideCoordinates r → s.reg r = base.reg r
  payload : FieldConvolution.tapeData s = FieldConvolution.tapeData base

theorem coordinateInvariant_dec (base : Store) (M remaining : ℕ) (s : Store)
    (hi : CoordinateInvariant base M remaining s) :
    CoordinateInvariant base M remaining (TapeProgram.decStore 55 s) := by
  refine ⟨hi.remaining_le,?_,?_,?_,?_,?_,hi.payload⟩
  · intro r
    by_cases hr : r = 55
    · subst r
      simpa [TapeProgram.decStore] using (Nat.sub_le (s.reg 55) 1).trans (hi.bounded 55)
    · simpa [TapeProgram.decStore,hr] using hi.bounded r
  · simpa [SamplerOdometer.Valid,coordinateDigits,TapeProgram.decStore] using hi.valid
  · simpa [TapeProgram.decStore] using hi.radix
  · simpa [SamplerOdometer.readings,coordinateDigits,TapeProgram.decStore] using hi.number
  · intro r hr
    simpa [TapeProgram.decStore,(coordinateOutside r hr).2.2.1] using hi.frame r hr

theorem coordinateInvariant_next (base : Store) (M n : ℕ) (s : Store)
    (hq : 1 < base.reg 40) (hflat : base.reg 2 < (base.reg 40)^2)
    (hi : CoordinateInvariant base M (n+1) s) :
    CoordinateInvariant base M n (SamplerOdometer.nextStore 40 59 coordinateDigits s) := by
  have hq' : 1 < s.reg 40 := by rw [hi.radix]; exact hq
  have hnumber := SamplerOdometer.program_number 40 59 coordinateDigits coordinateDigits_nodup s hi.valid hq'
  have hnew : base.reg 2-(n+1)+1 = base.reg 2-n := by have := hi.remaining_le; omega
  have hnewlt : base.reg 2-(n+1)+1 < (base.reg 40)^2 := by have := hi.remaining_le; omega
  have hfinallt : base.reg 2-n < (base.reg 40)^2 := (Nat.sub_le _ _).trans_lt hflat
  have hvalue : Nat.ofDigits (base.reg 40)
      (SamplerOdometer.readings coordinateDigits (SamplerOdometer.nextStore 40 59 coordinateDigits s)) =
        base.reg 2-n := by
    rw [hi.radix,hi.number] at hnumber
    simpa only [coordinateDigits,List.length_cons,List.length_nil,Nat.zero_add,
      Nat.reduceAdd,Nat.mod_eq_of_lt hnewlt,hnew,Nat.mod_eq_of_lt hfinallt] using hnumber
  have hdata : FieldConvolution.tapeData (SamplerOdometer.nextStore 40 59 coordinateDigits s) =
      FieldConvolution.tapeData s := by
    obtain ⟨hr,ho,hb,hh⟩ := SamplerOdometer.nextStore_payload 40 59 coordinateDigits s
    exact Prod.ext hr (Prod.ext ho (Prod.ext hb hh))
  refine ⟨by have := hi.remaining_le; omega,
    SamplerOdometer.nextStore_bound 40 59 coordinateDigits coordinateDigits_nodup s hi.valid M hi.bounded,
    SamplerOdometer.program_valid 40 59 coordinateDigits coordinateDigits_nodup s hi.valid,
    ?_,hvalue,?_,hdata.trans hi.payload⟩
  · exact (SamplerOdometer.nextStore_fresh 40 59 coordinateDigits s 40 (by decide) (by decide)).trans hi.radix
  · intro r hr
    rw [SamplerOdometer.nextStore_fresh 40 59 coordinateDigits s r
      (coordinateOutside r hr).1 (coordinateOutside r hr).2.1]
    exact hi.frame r hr

theorem coordinateLoop_stops (base : Store) (M n : ℕ) (s : Store) (inp : Inputs)
    (hq : 1 < base.reg 40) (hflat : base.reg 2 < (base.reg 40)^2)
    (hi : CoordinateInvariant base M n s) (hn : s.reg 55 = n) :
    ∃ t e, t ≤ n*(2*(8*M+20)+2)+1 ∧
      (TapeProgram.countedLoop coordinateStep 55).Stops inp
        (s.toCfg (TapeProgram.loopHeader 43)) t (e.toCfg (TapeProgram.loopExit 43)) ∧
      CoordinateInvariant base M 0 e ∧ e.reg 55 = 0 := by
  apply TapeProgram.countedLoop_stops coordinateStep 55 coordinateStep_fresh inp
    (2*(8*M+20)) (CoordinateInvariant base M)
  · intro m d _ hd
    have hd₁ := coordinateInvariant_dec base M (m+1) d hd
    obtain ⟨t,c,ht,hc,hcs,hb⟩ := SamplerOdometer.program_stops_valid
      40 59 coordinateDigits coordinateDigits_nodup inp M (TapeProgram.decStore 55 d) hd₁.bounded hd₁.valid
    refine ⟨t,c,?_,hc,?_⟩
    · simpa [coordinateDigits] using ht
    · rw [hcs]
      exact coordinateInvariant_next base M m _ hq hflat hd₁
  · exact hn
  · exact hi

def coordinateInit : TapeProgram 64 2 42 :=
  TapeProgram.seq (SamplerOdometer.initDigits 40 59 coordinateDigits) (TapeMacros.copy 2 55 58)

def coordinateInitStore (d : Store) : Store :=
  ((SamplerOdometer.initializeStore 40 59 coordinateDigits d).setReg 55 (d.reg 2)).setReg 58 0

private theorem initialize_bound {R B : ℕ} (q tmp : Fin R)
    (ps : List (SamplerOdometer.Digit R)) (d : TapeStore R B) (M : ℕ)
    (hd : ∀ r, d.reg r ≤ M) :
    ∀ r, (SamplerOdometer.initializeStore q tmp ps d).reg r ≤ M := by
  induction ps generalizing d with
  | nil => exact hd
  | cons p ps ih => exact ih _ (SamplerOdometer.resetStore_bound q tmp p d M hd)

theorem coordinateInit_frame (d : Store) (r : Fin 64) (hr : OutsideCoordinates r) :
    (coordinateInitStore d).reg r = d.reg r := by
  have h := coordinateOutside r hr
  simp only [coordinateInitStore,TapeStore.setReg,Function.update_of_ne h.2.2.2,
    Function.update_of_ne h.2.2.1]
  exact SamplerOdometer.initializeStore_fresh 40 59 coordinateDigits d r h.1 h.2.1

theorem coordinateInit_invariant (d : Store) (M : ℕ) (hd : ∀ r, d.reg r ≤ M)
    (hq : 1 < d.reg 40) : CoordinateInvariant d M (d.reg 2) (coordinateInitStore d) := by
  refine ⟨le_rfl,?_,?_,coordinateInit_frame d 40 (by decide),?_,coordinateInit_frame d,rfl⟩
  · exact FieldPrograms.setReg_bound _ 58 0 M
      (FieldPrograms.setReg_bound _ 55 (d.reg 2) M
        (initialize_bound 40 59 coordinateDigits d M hd) (hd 2)) (Nat.zero_le _)
  · simp [SamplerOdometer.Valid,coordinateInitStore,coordinateDigits,
      SamplerOdometer.initializeStore,SamplerOdometer.resetStore,TapeStore.setReg]
    omega
  · simp [coordinateInitStore,coordinateDigits,SamplerOdometer.readings,
      SamplerOdometer.initializeStore,SamplerOdometer.resetStore,TapeStore.setReg,Nat.ofDigits_cons]

theorem coordinateInit_count (d : Store) : (coordinateInitStore d).reg 55 = d.reg 2 := by
  simp [coordinateInitStore,TapeStore.setReg]

theorem coordinateInit_stops (d : Store) (inp : Inputs) (M : ℕ) (hd : ∀ r, d.reg r ≤ M) :
    ∃ t e, t ≤ 64*(M+1) ∧ coordinateInit.Stops inp (d.toCfg coordinateInit.entry) t e ∧
      e.store = coordinateInitStore d := by
  obtain ⟨s,c,hs,hc,hcs,hb⟩ := SamplerOdometer.initialize_stops
    40 59 coordinateDigits coordinateDigits_nodup inp M d hd
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (B := 2) (2 : Fin 64) 55 58
    (by decide) (by decide) (by decide) inp c.store
  have hindex : c.store.reg 2 = d.reg 2 := by
    rw [hcs]
    exact SamplerOdometer.initializeStore_fresh 40 59 coordinateDigits d 2 (by decide) (by decide)
  refine ⟨s+1+(c.reg 55+c.reg 58+5*c.reg 2+7),e.mapPC (TapeProgram.rightLabel 31),?_,?_,?_⟩
  · have h55 := hb 55
    have h58 := hb 58
    have h2 := hb 2
    simp only [coordinateDigits,List.length_cons,List.length_nil,Nat.reduceAdd] at hs
    omega
  · convert hc.seq he using 1 <;> rfl
  · change e.store = _
    rw [hes,hindex,hcs]
    rfl

def coordinates : TapeProgram 64 2 111 :=
  TapeProgram.seq (TapeProgram.seq coordinateInit (TapeProgram.countedLoop coordinateStep 55))
    (UnaryArithmetic.multiply 53 40 44 56 57)

def OutsidePivotCoordinates (r : Fin 64) : Prop :=
  OutsideCoordinates r ∧ r ≠ 44 ∧ r ≠ 56 ∧ r ≠ 57

instance (r : Fin 64) : Decidable (OutsidePivotCoordinates r) := by
  unfold OutsidePivotCoordinates
  infer_instance

structure CoordinateOutcome (d e : Store) (M : ℕ) : Prop where
  col : e.reg 43 = d.reg 2 % d.reg 40
  rowBase : e.reg 44 = d.reg 2 / d.reg 40 * d.reg 40
  frame : ∀ r, OutsidePivotCoordinates r → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : FieldConvolution.tapeData e = FieldConvolution.tapeData d

theorem coordinates_stops (d : Store) (inp : Inputs) (M : ℕ)
    (hd : ∀ r, d.reg r ≤ M) (hq : 1 < d.reg 40) (hflat : d.reg 2 < (d.reg 40)^2) :
    ∃ t e, t ≤ 256*(M+1)^2 ∧ coordinates.Stops inp (d.toCfg coordinates.entry) t e ∧
      CoordinateOutcome d e.store M := by
  obtain ⟨s,c,hs,hc,hcs⟩ := coordinateInit_stops d inp M hd
  have hInv : CoordinateInvariant d M (d.reg 2) c.store := by
    rw [hcs]
    exact coordinateInit_invariant d M hd hq
  have hcount : c.store.reg 55 = d.reg 2 := by rw [hcs,coordinateInit_count]
  obtain ⟨t,f,ht,hf,hfi,hfz⟩ := coordinateLoop_stops d M (d.reg 2) c.store inp hq hflat hInv hcount
  have hlow : f.reg 43 < d.reg 40 := by
    have hh := hfi.valid (43,52) (by simp [coordinateDigits])
    rw [hfi.radix] at hh
    change f.reg 43+f.reg 52+1 = d.reg 40 at hh
    omega
  have hnumber : f.reg 43+d.reg 40*f.reg 53 = d.reg 2 := by
    simpa [SamplerOdometer.readings,coordinateDigits,Nat.ofDigits_cons] using hfi.number
  have hcol : f.reg 43 = d.reg 2 % d.reg 40 := by
    rw [← hnumber]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hlow]
  have hrow : f.reg 53 = d.reg 2 / d.reg 40 := by
    rw [← hnumber,Nat.add_mul_div_left _ _ (by omega : 0 < d.reg 40),Nat.div_eq_of_lt hlow,zero_add]
  obtain ⟨u,e,hu,he,hes⟩ := UnaryArithmetic.multiply_stops_polynomial
    (B := 2) (53 : Fin 64) 40 44 56 57 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) inp f M
    (hfi.bounded 53) (hfi.bounded 40) (hfi.bounded 44) (hfi.bounded 56) (hfi.bounded 57)
  have hall := (hc.seq hf).seq he
  refine ⟨s+1+t+1+u,e.mapPC (TapeProgram.rightLabel 87),?_,?_,?_⟩
  · have ht' := ht.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_right (2*(8*M+20)+2) (hd 2)) 1)
    nlinarith
  · convert hall using 1 <;> rfl
  · have hprod : f.reg 53*f.reg 40 ≤ M := by
      rw [hfi.radix]
      have hh := hd 2
      nlinarith
    refine ⟨?_,?_,?_,?_,?_⟩
    · change e.store.reg 43 = _
      rw [hes]
      simpa [UnaryArithmetic.multiplyStore,TapeStore.setReg] using hcol
    · change e.store.reg 44 = _
      rw [hes]
      simp [UnaryArithmetic.multiplyStore,TapeStore.setReg,hrow,hfi.radix]
    · intro r hr
      change e.store.reg r = _
      rw [hes]
      simpa [UnaryArithmetic.multiplyStore,TapeStore.setReg,hr.2.1,hr.2.2.1,hr.2.2.2] using hfi.frame r hr.1
    · change ∀ r, e.store.reg r ≤ M
      rw [hes]
      exact FieldPrograms.setReg_bound _ _ 0 M
        (FieldPrograms.setReg_bound _ _ 0 M
          (FieldPrograms.setReg_bound _ _ (f.reg 53*f.reg 40) M hfi.bounded hprod) (Nat.zero_le _)) (Nat.zero_le _)
    · change FieldConvolution.tapeData e.store = _
      rw [hes]
      exact hfi.payload

/-- Coordinates must be recovered before inversion, whose ordinary workspace
includes the old flat-index counter. Its persistent results are43,44,50. -/
def preparePivot : TapeProgram 64 2 529 := TapeProgram.seq coordinates invertPivot

structure PivotOutcome (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell))
    (d e : Store) (M : ℕ) : Prop where
  col : e.reg 43 = d.reg 2 % d.reg 40
  rowBase : e.reg 44 = d.reg 2 / d.reg 40 * d.reg 40
  inverse : e.reg 50 = (BinaryField.inverseIndex ell h a).val
  setup : FieldSetup ell h e
  frame : ∀ r, 40 ≤ r.val → OutsidePivotCoordinates r → r ≠ 50 → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : TapeStore.SamePayload e d
  heads : e.bufferHead = d.bufferHead
  pivot : e.reg 6 = d.reg 6

theorem preparePivot_stops (ell : ℕ) (h : 0 < ell) (d : Store) (inp : Inputs) (M : ℕ)
    (hs : FieldSetup ell h d) (hd : ∀ r, d.reg r ≤ M)
    (hq : 1 < d.reg 40) (hflat : d.reg 2 < (d.reg 40)^2)
    (a : Fin (2^ell)) (ha : d.reg 6 = a.val) :
    ∃ t e, t ≤ 21000*(M+1)^7 ∧ preparePivot.Stops inp (d.toCfg preparePivot.entry) t e ∧
      PivotOutcome ell h a d e.store M := by
  obtain ⟨t,c,ht,hc,hco⟩ := coordinates_stops d inp M hd hq hflat
  have hsetup : FieldSetup ell h c.store := by
    rcases hs with ⟨h0,h36,h37,h38⟩
    exact ⟨(hco.frame 0 (by decide)).trans h0,(hco.frame 36 (by decide)).trans h36,
      (hco.frame 37 (by decide)).trans h37,(hco.frame 38 (by decide)).trans h38⟩
  have hvalue : c.store.reg 6 = a.val := (hco.frame 6 (by decide)).trans ha
  obtain ⟨s,e,hs,he,heo⟩ := invertPivot_stops ell h inp c.store M hsetup hco.bounded a hvalue
  refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel 111),?_,?_,?_⟩
  · have hp : (M+1)^2 ≤ (M+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
    have hpos : 1 ≤ (M+1)^7 := one_le_pow₀ (by omega)
    nlinarith
  · convert hc.seq he using 1 <;> rfl
  · have hro : c.store.roHead = d.roHead := congrArg Prod.fst hco.payload
    have houtput : c.store.output = d.output := congrArg (fun x => x.2.1) hco.payload
    have hbuffer : c.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) hco.payload
    have hheads : c.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) hco.payload
    have hcp : TapeStore.SamePayload c.store d := ⟨hro,houtput,fun b k => by rw [hbuffer]⟩
    refine ⟨(heo.frame 43 (by decide) (by decide)).trans hco.col,
      (heo.frame 44 (by decide) (by decide)).trans hco.rowBase,heo.value,heo.setup,
      ?_,heo.bounded,heo.payload.trans hcp,heo.heads.trans hheads,
      heo.pivot.trans (hco.frame 6 (by decide))⟩
    intro r hr hrC hr50
    exact (heo.frame r hr hr50).trans (hco.frame r hrC)

#print axioms invertPivot_stops
#print axioms coordinateLoop_stops
#print axioms coordinates_stops
#print axioms preparePivot_stops
end ExpandingCodes.Computation.GaussianPivot
