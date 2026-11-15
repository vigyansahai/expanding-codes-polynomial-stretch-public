import ExpandingCodes.Computation.TesterBackendPrep

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendComplete
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch
open TesterBackendPrep

def registers (i : Fin 64) : Fin 80 := ⟨i.val,by omega⟩
def buffers (i : Fin 2) : Fin 3 := ⟨i.val,by omega⟩
theorem registers_injective : Function.Injective registers := by
  intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 80 => x.val) h
theorem buffers_injective : Function.Injective buffers := by
  intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 3 => x.val) h

def project (d : BigStore) : Store := d.projectStorage registers buffers

structure Ready (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : BigStore) : Prop where
  bounded : ∀ r,d.reg r ≤ M
  q : d.reg 23 = 2^ell
  qSquared : d.reg 24 = 2^(2*ell)
  coefficientCount : d.reg 19 = 3*ell+1
  monic : d.reg 3 = 2^ell+(BinaryPolynomial.selectedIndex ell h).val
  rows : d.reg 70 = m
  large : 1 < m
  cells : m*m*(2^ell) ≤ M
  gramHead : d.bufferHead 0 ≤ (M+1)^2
  spareHead : d.bufferHead 1 = 1
  gramMarked : BottomMarked d 0
  spareMarked : BottomMarked d 1

theorem result_metadata (d : BigStore) :
    (result d).reg 0 = d.reg 23 ∧ (result d).reg 36 = d.reg 24 ∧
    (result d).reg 37 = d.reg 19 ∧ (result d).reg 38 = d.reg 3 ∧
    (result d).reg 40 = d.reg 70 ∧ (result d).reg 49 = d.reg 70 ∧
    (result d).reg 51 = d.reg 70*d.reg 70 := by
  have hr : (result d).reg = Function.update (registerResult d).reg 54 0 := by
    rw [result,ZeroTables.result_reg,beforeZero_reg]
  rw [hr]
  simp [registerResult,TapeStore.setReg]

theorem beforeZero_tape (d : BigStore) : (beforeZero d).bufferTape = d.bufferTape :=
  congrArg (fun v => v.2.2.1) (beforeZero_data d)

theorem beforeZero_head (d : BigStore) : (beforeZero d).bufferHead = d.bufferHead :=
  congrArg (fun v => v.2.2.2) (beforeZero_data d)

theorem result_common (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : BigStore)
    (hr : Ready ell h m M d) (hb : ∀ r,(result d).reg r ≤ M) :
    GaussianDriver.Common ell h m M (project (result d)) := by
  obtain ⟨hq,hq2,hN,hp,hm,hm',hc⟩ := result_metadata d
  have hH : (beforeZero d).bufferHead 1 = 1 := by rw [beforeZero_head]; exact hr.spareHead
  have hheads := ZeroTables.result_head 54 1 (d.reg 70*d.reg 70*d.reg 23) (beforeZero d) hH
  have hbound : d.reg 70*d.reg 70*d.reg 23 ≤ M := by rw [hr.rows,hr.q]; exact hr.cells
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,hr.large⟩
  · change (result d).reg 0 = _ ∧ (result d).reg 36 = _ ∧
      (result d).reg 37 = _ ∧ (result d).reg 38 = _
    exact ⟨hq.trans hr.q,hq2.trans hr.qSquared,hN.trans hr.coefficientCount,hp.trans hr.monic⟩
  · intro r; exact hb (registers r)
  · change (result d).bufferHead 0 ≤ _
    rw [result,hheads]
    simpa only [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),beforeZero_head] using hr.gramHead
  · change (result d).bufferHead 1 ≤ _
    rw [result,hheads]
    simp only [Function.update_self]
    nlinarith
  · change BottomMarked (result d) (0 : Fin 3)
    have hz (j : ℕ) : ((result d).bufferTape 0).getD j .blank =
        (d.bufferTape 0).getD j .blank := by
      rw [result,ZeroTables.result_other_symbol _ _ _ _ _ (by decide),beforeZero_tape]
    exact ⟨(hz 0).trans hr.gramMarked.1,fun j hj => by rw [hz]; exact hr.gramMarked.2 j hj⟩
  · change BottomMarked (result d) (1 : Fin 3)
    apply ZeroTables.result_bottomMarked 54 1 _ (beforeZero d) hH
    simpa only [BottomMarked,beforeZero_tape] using hr.spareMarked
  · exact hm.trans hr.rows
  · exact hm'.trans hr.rows
  · change (result d).reg 51 = m*m
    simpa only [hr.rows] using hc

theorem result_gram {q m n : ℕ} (d : BigStore)
    (A : Gaussian.Table (Fin q) m n)
    (ha : ThermometerTable d 0 q (fun i : Fin (m*n) => flatEntry A i.val)) :
    MatrixStored (project (result d)) 0 A := by
  change ThermometerTable (result d) (0 : Fin 3) q _
  apply ZeroTables.result_other_table 54 1 _ (beforeZero d) 0 (by decide) q _
  simpa only [ThermometerTable,ThermometerAt,beforeZero_tape] using ha

def zeroTable (ell m : ℕ) : Gaussian.Table (Fin (2^ell)) m m :=
  Gaussian.ofMatrix fun _ _ => ⟨0,pow_pos (by decide) _⟩

theorem zeroTable_flat (ell m k : ℕ) : flatEntry (zeroTable ell m) k = 0 := by
  simp [flatEntry,zeroTable,Gaussian.toMatrix,Gaussian.ofMatrix]

theorem result_spare (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : BigStore)
    (hr : Ready ell h m M d) :
    MatrixStored (project (result d)) 1 (zeroTable ell m) := by
  have hH : (beforeZero d).bufferHead 1 = 1 := by rw [beforeZero_head]; exact hr.spareHead
  have ht := ZeroTables.result_table (K := m*m) 54 1 (2^ell) (beforeZero d) hH
  change ThermometerTable (result d) (1 : Fin 3) (2^ell) _
  simp only [zeroTable_flat]
  simpa only [result,hr.rows,hr.q] using ht

/-- The complete fixed tester suffix: physical frame preparation followed by
the actual Gaussian rank routine and rational acceptance comparison. -/
def program (θ : ℚ) : TapeProgram 80 3 (118+(4260+TesterSuffix.labels θ)) :=
  TapeProgram.seq TesterBackendPrep.program ((TesterBackend.program θ).renameStorage registers buffers)

def timeBound (θ : ℚ) (M : ℕ) : ℕ := 150*(M+1)^2+1+TesterBackend.timeBound θ M

theorem program_stops (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ) (inp : Inputs)
    (d : BigStore) (y : Word (rowCount degree n))
    (hr : Ready (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M d)
    (ha : ThermometerTable d 0 (fieldSize degree n)
      (fun i : Fin (rowCount degree n*rowCount degree n) => flatEntry (binaryTestTable degree n y) i.val)) :
    ∃ t e, t ≤ timeBound θ M ∧ (program θ).Stops inp (d.toCfg (program θ).entry) t e ∧
      e.output = d.output ++ [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  have hq : 0 < d.reg 23 := by rw [hr.q]; exact pow_pos (by decide) _
  have hn : d.reg 70*d.reg 70*d.reg 23 ≤ M := by rw [hr.rows,hr.q]; exact hr.cells
  obtain ⟨t,c,ht,hc,hcs,hcb⟩ := TesterBackendPrep.program_stops inp d M hr.bounded hq hn
  have hbc : ∀ r,(result d).reg r ≤ M := by
    have he : c.reg = (result d).reg := congrArg TapeStore.reg hcs
    simpa only [he] using hcb
  have hcommon := result_common _ _ _ _ d hr hbc
  have hGram := result_gram d (binaryTestTable degree n y) ha
  have hSpare := result_spare _ _ _ _ d hr
  obtain ⟨s,e,hs,he,heo⟩ := TesterBackend.program_stops θ hθ degree n M inp
    (project (result d)) y hcommon (zeroTable (fieldExponent degree n) (rowCount degree n)) hGram hSpare
  obtain ⟨f,hf,_,hfo⟩ := he.liftStorage registers buffers registers_injective buffers_injective
    (c.store.toCfg (TesterBackend.program θ).entry) (by rw [hcs]; rfl)
  refine ⟨t+1+s,f.mapPC (TapeProgram.rightLabel 118),by unfold timeBound; omega,?_,?_⟩
  · convert hc.seq hf using 1 <;> rfl
  · change f.output = _
    rw [hfo,heo]
    change (result d).output ++ _ = _
    have ho : (result d).output = d.output :=
      (ZeroTables.result_payload 54 1 _ (beforeZero d)).2.trans
        (congrArg (fun v => v.2.1) (beforeZero_data d))
    rw [ho]

theorem timeBound_polynomial (θ : ℚ) : PolynomialBound (timeBound θ) :=
  ((((PolynomialBound.const 150).mul
    ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2)).add
      (PolynomialBound.const 1)).add (TesterBackend.timeBound_polynomial θ))

#print axioms program_stops
#print axioms timeBound_polynomial
end ExpandingCodes.Computation.TesterBackendComplete
