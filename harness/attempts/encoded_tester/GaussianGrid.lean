import ExpandingCodes.Computation.GaussianProgram

set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianGrid

open NKtLB GaussianProgram

def sumInto (left right dest : Fin 64) : TapeProgram 64 2 20 :=
  TapeProgram.seq (TapeMacros.copy left dest 4) (TapeMacros.addPreserving right dest 4)

def sumPost (d : Store) (left right dest : Fin 64) : Store :=
  (d.setReg dest (d.reg left+d.reg right)).setReg 4 0

theorem sumInto_stops (left right dest : Fin 64)
    (hld : left ≠ dest) (hl4 : left ≠ 4) (hrd : right ≠ dest) (hr4 : right ≠ 4) (hd4 : dest ≠ 4)
    (inp : Inputs) (d : Store) :
    ∃ e, (sumInto left right dest).Stops inp (d.toCfg (sumInto left right dest).entry)
      (d.reg dest+d.reg 4+5*d.reg left+5*d.reg right+13) e ∧
      e.store = sumPost d left right dest := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops left dest 4 hld hl4 hd4 inp d
  obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops right dest 4 hrd hr4 hd4 inp c.store
  have hcr : c.reg = ((d.setReg dest (d.reg left)).setReg 4 0).reg := congrArg TapeStore.reg hcs
  have hc4 : c.reg 4 = 0 := by rw [hcr]; simp [TapeStore.setReg]
  have hcright : c.reg right = d.reg right := by rw [hcr]; simp [TapeStore.setReg, hr4, hrd]
  have hall := hc.seq he
  refine ⟨e.mapPC (TapeProgram.rightLabel 11),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (dsimp only [TapeCfg.store]; rw [hc4,hcright]; omega)
  · change e.store = _
    rw [hes,hcs]
    simp only [sumPost,TapeStore.setReg]
    congr 1
    funext r
    by_cases h4 : r = 4
    · subst r; simp
    · by_cases hd : r = dest
      · subst r; simp [hrd,hr4,hd4]
      · simp [Function.update,h4,hd]

theorem sumPost_bounded (d : Store) (left right dest : Fin 64) (M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) (hsum : d.reg left+d.reg right ≤ M) :
    ∀ r, (sumPost d left right dest).reg r ≤ M := by
  intro r
  simp only [sumPost,TapeStore.setReg,Function.update_apply]
  split_ifs <;> first | exact Nat.zero_le M | exact hsum | exact hM r

def prepareAddresses : TapeProgram 64 2 71 :=
  TapeProgram.seq (sumInto 41 42 9)
    (TapeProgram.seq (sumInto 41 43 10)
      (TapeProgram.seq (sumInto 44 42 11) (TapeMacros.copy 45 12 4)))

def addressStore (d : Store) : Store :=
  let d₁ := sumPost d 41 42 9
  let d₂ := sumPost d₁ 41 43 10
  let d₃ := sumPost d₂ 44 42 11
  (d₃.setReg 12 (d₃.reg 45)).setReg 4 0

/-- Runtime address arithmetic uses actual preserving unary additions. The
same 71-label code handles every matrix dimension and pivot position. -/
theorem prepareAddresses_stops (inp : Inputs) (d : Store) (M : ℕ)
    (hM : ∀ r,d.reg r ≤ M) (hD : d.reg 41+d.reg 42 ≤ M)
    (hC : d.reg 41+d.reg 43 ≤ M) (hB : d.reg 44+d.reg 42 ≤ M) :
    ∃ t e, t ≤ 100*(M+1) ∧ prepareAddresses.Stops inp (d.toCfg prepareAddresses.entry) t e ∧
      e.store = addressStore d ∧ (∀ r,e.reg r ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := sumInto_stops 41 42 9
    (by decide) (by decide) (by decide) (by decide) (by decide) inp d
  have hb₁ : ∀ r,c₁.store.reg r ≤ M := by rw [hs₁]; exact sumPost_bounded d 41 42 9 M hM hD
  have hC₁ : c₁.store.reg 41+c₁.store.reg 43 ≤ M := by
    rw [hs₁]; simpa [sumPost,TapeStore.setReg] using hC
  obtain ⟨c₂,h₂,hs₂⟩ := sumInto_stops 41 43 10
    (by decide) (by decide) (by decide) (by decide) (by decide) inp c₁.store
  have hb₂ : ∀ r,c₂.store.reg r ≤ M := by rw [hs₂]; exact sumPost_bounded _ 41 43 10 M hb₁ hC₁
  have hB₂ : c₂.store.reg 44+c₂.store.reg 42 ≤ M := by
    rw [hs₂,hs₁]; simpa [sumPost,TapeStore.setReg] using hB
  obtain ⟨c₃,h₃,hs₃⟩ := sumInto_stops 44 42 11
    (by decide) (by decide) (by decide) (by decide) (by decide) inp c₂.store
  have hb₃ : ∀ r,c₃.store.reg r ≤ M := by rw [hs₃]; exact sumPost_bounded _ 44 42 11 M hb₂ hB₂
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (45 : Fin 64) 12 4
    (by decide) (by decide) (by decide) inp c₃.store
  have hall := h₁.seq (h₂.seq (h₃.seq he))
  refine ⟨_,_,?_,hall,?_,?_⟩
  · have ht₁ : d.reg 9+d.reg 4+5*d.reg 41+5*d.reg 42+13 ≤ 12*M+13 := by
      have := hM 9; have := hM 4; have := hM 41; have := hM 42; omega
    have ht₂ : c₁.store.reg 10+c₁.store.reg 4+5*c₁.store.reg 41+5*c₁.store.reg 43+13 ≤ 12*M+13 := by
      have := hb₁ 10; have := hb₁ 4; have := hb₁ 41; have := hb₁ 43; omega
    have ht₃ : c₂.store.reg 11+c₂.store.reg 4+5*c₂.store.reg 44+5*c₂.store.reg 42+13 ≤ 12*M+13 := by
      have := hb₂ 11; have := hb₂ 4; have := hb₂ 44; have := hb₂ 42; omega
    have ht₄ : c₃.store.reg 12+c₃.store.reg 4+5*c₃.store.reg 45+7 ≤ 7*M+7 := by
      have := hb₃ 12; have := hb₃ 4; have := hb₃ 45; omega
    omega
  · change e.store = _
    rw [hes,hs₃,hs₂,hs₁]
    rfl
  · change ∀ r,e.store.reg r ≤ M
    rw [hes]
    exact FieldPrograms.setReg_bound _ 4 0 M
      (FieldPrograms.setReg_bound c₃.store 12 (c₃.store.reg 45) M hb₃ (hb₃ 45)) (Nat.zero_le M)

@[simp] theorem addressStore_D (d : Store) : (addressStore d).reg 9 = d.reg 41+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_C (d : Store) : (addressStore d).reg 10 = d.reg 41+d.reg 43 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_B (d : Store) : (addressStore d).reg 11 = d.reg 44+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_target (d : Store) : (addressStore d).reg 12 = d.reg 45 := by
  simp [addressStore,sumPost,TapeStore.setReg]

theorem addressStore_frame (d : Store) (r : Fin 64) (hr : 40 ≤ r.val) :
    (addressStore d).reg r = d.reg r := by
  have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
  have h9 : r ≠ 9 := by intro he;subst r;norm_num at hr
  have h10 : r ≠ 10 := by intro he;subst r;norm_num at hr
  have h11 : r ≠ 11 := by intro he;subst r;norm_num at hr
  have h12 : r ≠ 12 := by intro he;subst r;norm_num at hr
  simp [addressStore,sumPost,TapeStore.setReg,h4,h9,h10,h11,h12]

#print axioms prepareAddresses_stops

theorem addressStore_payload (d : Store) : TapeStore.SamePayload (addressStore d) d :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

theorem addressStore_setup (ell : ℕ) (h : 0 < ell) (d : Store) (hs : FieldSetup ell h d) :
    FieldSetup ell h (addressStore d) := by
  simpa [FieldSetup,addressStore,sumPost,TapeStore.setReg] using hs

theorem flatEntry_pair {q m n : ℕ} (A : Gaussian.Table (Fin q) m n) (i : Fin m) (j : Fin n) :
    flatEntry A (finProdFinEquiv (i,j)).val = (Gaussian.toMatrix A i j).val := by
  let k : Fin (m*n) := finProdFinEquiv (i,j)
  change flatEntry A k.val = _
  rw [flatEntry,dif_pos k.isLt]
  change (Gaussian.toMatrix A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).val = _
  rw [show finProdFinEquiv.symm k = (i,j) from finProdFinEquiv.symm_apply_apply (i,j)]

theorem storedEntry {q m n : ℕ} {d : Store} {b : Fin 2}
    {A : Gaussian.Table (Fin q) m n} (ht : MatrixStored d b A) (i : Fin m) (j : Fin n) :
    TapeArrays.ThermometerAt d b (TapeArrays.entryOffset (finProdFinEquiv (i,j)).val q) q
      (Gaussian.toMatrix A i j).val := by
  have h := ht (finProdFinEquiv (i,j))
  dsimp only at h
  rw [flatEntry_pair] at h
  exact h

structure Coordinates {m n : ℕ} (p : Fin m × Fin n) (i : Fin m) (j : Fin n) (d : Store) : Prop where
  rowBase : d.reg 41 = i.val*n
  column : d.reg 42 = j.val
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  target : d.reg 45 = i.val*n+j.val

def materializeCell (input output : Fin 2) : TapeProgram 64 2 1454 :=
  TapeProgram.seq prepareAddresses (concreteSchurEntry input output)

/-- A source-level matrix-entry refinement: runtime counters compute the
three physical addresses, actual finite field code computes the expression,
and exactly the corresponding padded-Schur cell is physically overwritten. -/
theorem materializeCell_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (j : Fin n) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r,d.reg r ≤ M) (hsize : m*n ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : TapeArrays.BottomMarked d input) (hmO : TapeArrays.BottomMarked d output)
    (hstored : MatrixStored d input A) (hcoord : Coordinates p i j d)
    (hInv : d.reg 13 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 1454) (beforeWrite : Store),
      t ≤ 100*(M+1)+460*((M+1)^2+1)^2+20000*(M+1)^6+3000*(M+1)^5+7 ∧
      (materializeCell input output).Stops inp (d.toCfg (materializeCell input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      TapeArrays.EntryWritten beforeWrite e.store output
        (TapeArrays.entryOffset (finProdFinEquiv (i,j)).val (2^ell)) (2^ell)
        (Gaussian.toMatrix (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) i j).val ∧
      (∀ r,40 ≤ r.val → e.reg r = d.reg r) ∧ SchurCellState ell h input output e.store M := by
  have hcell (i' : Fin m) (j' : Fin n) : i'.val*n+j'.val ≤ M := by
    have hidx := (finProdFinEquiv (i',j')).isLt
    change j'.val+n*i'.val < m*n at hidx
    nlinarith
  have hD : d.reg 41+d.reg 42 ≤ M := by rw [hcoord.rowBase,hcoord.column]; exact hcell i j
  have hC : d.reg 41+d.reg 43 ≤ M := by rw [hcoord.rowBase,hcoord.pivotColumn]; exact hcell i p.2
  have hB : d.reg 44+d.reg 42 ≤ M := by rw [hcoord.pivotBase,hcoord.column]; exact hcell p.1 j
  obtain ⟨t₁,c,ht₁,hc,hcs,hcb⟩ := prepareAddresses_stops inp d M hM hD hC hB
  have hcp : TapeStore.SamePayload c.store d := by rw [hcs]; exact addressStore_payload d
  have hch : c.store.bufferHead = d.bufferHead := by rw [hcs]; rfl
  have hc0 : c.store.reg 0 = 2^ell := by rw [hcs]; exact (addressStore_setup ell h d hs).1
  have hc9 : c.store.reg 9 = (finProdFinEquiv (i,j)).val := by
    rw [hcs,addressStore_D,hcoord.rowBase,hcoord.column]
    change i.val*n+j.val = j.val+n*i.val
    ring
  have hc10 : c.store.reg 10 = (finProdFinEquiv (i,p.2)).val := by
    rw [hcs,addressStore_C,hcoord.rowBase,hcoord.pivotColumn]
    change i.val*n+p.2.val = p.2.val+n*i.val
    ring
  have hc11 : c.store.reg 11 = (finProdFinEquiv (p.1,j)).val := by
    rw [hcs,addressStore_B,hcoord.pivotBase,hcoord.column]
    change p.1.val*n+j.val = j.val+n*p.1.val
    ring
  have hc12 : c.store.reg 12 = (finProdFinEquiv (i,j)).val := by
    rw [hcs,addressStore_target,hcoord.target]
    change i.val*n+j.val = j.val+n*i.val
    ring
  have hcInv : c.store.reg 13 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val := by
    rw [hcs]
    simpa [addressStore,sumPost,TapeStore.setReg] using hInv
  have hx : TapeArrays.ThermometerAt c.store input
      (TapeArrays.entryOffset (c.store.reg 9) (c.store.reg 0)) (c.store.reg 0)
      (Gaussian.toMatrix A i j).val := by
    rw [hc9,hc0]
    exact (storedEntry hstored i j).of_payload hcp
  have hy : TapeArrays.ThermometerAt c.store input
      (TapeArrays.entryOffset (c.store.reg 10) (c.store.reg 0)) (c.store.reg 0)
      (Gaussian.toMatrix A i p.2).val := by
    rw [hc10,hc0]
    exact (storedEntry hstored i p.2).of_payload hcp
  have hz : TapeArrays.ThermometerAt c.store input
      (TapeArrays.entryOffset (c.store.reg 11) (c.store.reg 0)) (c.store.reg 0)
      (Gaussian.toMatrix A p.1 j).val := by
    rw [hc11,hc0]
    exact (storedEntry hstored p.1 j).of_payload hcp
  obtain ⟨t₂,e,before,ht₂,he,hbefore,hew,hcaller,hstate⟩ := concreteSchurEntry_stops input output hio
    ell h inp c.store M (by rw [hcs]; exact addressStore_setup ell h d hs) hcb
    ((congrFun hch input).le.trans hhI) ((congrFun hch output).le.trans hhO)
    (hmI.of_payload hcp) (hmO.of_payload hcp)
    (Gaussian.toMatrix A i j) (Gaussian.toMatrix A i p.2) (Gaussian.toMatrix A p.1 j)
    ((PolynomialStretch.BinaryField.indexOperations ell h).inv (Gaussian.toMatrix A p.1 p.2)) hcInv hx hy hz
  have hall := hc.seq he
  refine ⟨_,_,before,by omega,hall,hbefore.trans hcp,?_,?_,hstate⟩
  · change TapeArrays.EntryWritten before e.store output _ _ _
    rw [hc12] at hew
    simpa only [paddedSchur_apply] using hew
  · intro r hr
    exact (hcaller r hr).trans (by rw [hcs]; exact addressStore_frame d r hr)

#print axioms materializeCell_stops

/-- The existing finite counted-loop code also supports semantic freshness:
actual body traces can certify the loop counter directly. This lets mapped
field subroutines restore protected counters internally without requiring a
syntactic no-touch condition. -/
theorem countedLoop_stops_of_body {R B L : ℕ} (P : TapeProgram R B L) (r : Fin R)
    (inp : Inputs) (C : ℕ) (Inv : ℕ → TapeStore R B → Prop)
    (hbody : ∀ n d, d.reg r = n+1 → Inv (n+1) d →
      ∃ t c, t ≤ C ∧ P.Stops inp ((TapeProgram.decStore r d).toCfg P.entry) t c ∧
        c.reg r = n ∧ Inv n c.store)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) (hi : Inv n d) :
    ∃ t e, t ≤ n*(C+2)+1 ∧
      (TapeProgram.countedLoop P r).Stops inp (d.toCfg (TapeProgram.loopHeader L)) t
        (e.toCfg (TapeProgram.loopExit L)) ∧ Inv 0 e ∧ e.reg r = 0 := by
  induction n generalizing d with
  | zero => exact ⟨1,d,by omega,TapeProgram.loop_zero P r inp d hd,hi,hd⟩
  | succ n ih =>
    obtain ⟨s,c,hs,hstop,hc,hInv⟩ := hbody n d hd hi
    obtain ⟨t,e,ht,he,hIe,hzero⟩ := ih c.store hc hInv
    have hheader := TapeProgram.loop_positive_header P r inp d (by omega)
    have hrun := hstop.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active P r)
    have hreturn := TapeProgram.loop_body_return P r inp c hstop.halted
    refine ⟨1+s+1+t,e,?_,⟨((hheader.trans hrun).trans hreturn).trans he.exec,he.halted⟩,hIe,hzero⟩
    rw [show (n+1)*(C+2) = n*(C+2)+(C+2) by ring]
    omega

#print axioms countedLoop_stops_of_body

theorem matrixStored_of_payload {q m n : ℕ} {d e : Store} {b : Fin 2}
    {A : Gaussian.Table (Fin q) m n} (ht : MatrixStored d b A) (hp : TapeStore.SamePayload e d) :
    MatrixStored e b A := fun i => (ht i).of_payload hp

def tickStore (d : Store) : Store :=
  (d.setReg 42 (d.reg 42+1)).setReg 45 (d.reg 45+1)

def cellBudget (M : ℕ) : ℕ :=
  100*(M+1)+460*((M+1)^2+1)^2+20000*(M+1)^6+3000*(M+1)^5+7

def tickBudget (M : ℕ) : ℕ := cellBudget M+7*M+12

def cellTick (input output : Fin 2) : TapeProgram 64 2 1469 :=
  TapeProgram.seq (TapeMacros.copy 50 13 4)
    (TapeProgram.seq (materializeCell input output)
      (TapeProgram.seq (TapeMacros.increment 42) (TapeMacros.increment 45)))

theorem cellTick_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (j : Fin n) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r,d.reg r ≤ M) (hsize : m*n ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : TapeArrays.BottomMarked d input) (hmO : TapeArrays.BottomMarked d output)
    (hstored : MatrixStored d input A) (hcoord : Coordinates p i j d)
    (hInv : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val)
    (hcol : d.reg 42+1 ≤ M) (hcut : d.reg 45+1 ≤ M) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 1469) (beforeWrite : Store), t ≤ tickBudget M ∧
      (cellTick input output).Stops inp (d.toCfg (cellTick input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      TapeArrays.EntryWritten beforeWrite e.store output
        (TapeArrays.entryOffset (finProdFinEquiv (i,j)).val (2^ell)) (2^ell)
        (Gaussian.toMatrix (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) i j).val ∧
      e.reg 42 = d.reg 42+1 ∧ e.reg 45 = d.reg 45+1 ∧
      (∀ r,40 ≤ r.val → r ≠ 42 → r ≠ 45 → e.reg r = d.reg r) ∧
      SchurCellState ell h input output e.store M := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (50 : Fin 64) 13 4 (by decide) (by decide) (by decide) inp d
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload d 13 (d.reg 50))
  have hcb : ∀ r,c.reg r ≤ M := by
    change ∀ r,c.store.reg r ≤ M
    rw [hcs]
    exact FieldPrograms.setReg_bound _ 4 0 M
      (FieldPrograms.setReg_bound d 13 (d.reg 50) M hM (hM 50)) (Nat.zero_le M)
  have hcf (r : Fin 64) (hr : 40 ≤ r.val) : c.store.reg r = d.reg r := by
    rw [hcs]
    have h13 : r ≠ 13 := by intro he;subst r;norm_num at hr
    have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
    simp [TapeStore.setReg,h13,h4]
  have hch : c.store.bufferHead = d.bufferHead := by rw [hcs];rfl
  have hcoordC : Coordinates p i j c.store :=
    ⟨(hcf 41 (by decide)).trans hcoord.rowBase,(hcf 42 (by decide)).trans hcoord.column,
      (hcf 43 (by decide)).trans hcoord.pivotColumn,(hcf 44 (by decide)).trans hcoord.pivotBase,
      (hcf 45 (by decide)).trans hcoord.target⟩
  have hInvC : c.store.reg 13 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val := by rw [hcs];simp [TapeStore.setReg,hInv]
  have hsC : FieldSetup ell h c.store := by rw [hcs];simpa [FieldSetup,TapeStore.setReg] using hs
  obtain ⟨s,f,before,hst,hf,hbefore,hew,hcaller,hstate⟩ := materializeCell_stops input output hio ell h inp A p i j
    c.store M hsC hcb hsize ((congrFun hch input).le.trans hhI) ((congrFun hch output).le.trans hhO)
    (hmI.of_payload hcp) (hmO.of_payload hcp) (matrixStored_of_payload hstored hcp) hcoordC hInvC
  have hff (r : Fin 64) (hr : 40 ≤ r.val) : f.store.reg r = d.reg r := (hcaller r hr).trans (hcf r hr)
  have hinc₁ := TapeMacros.increment_stops (42 : Fin 64) inp f.store
  let d₁ := f.store.setReg 42 (f.reg 42+1)
  have hinc₂ := TapeMacros.increment_stops (45 : Fin 64) inp d₁
  have hall := hc.seq (hf.seq (hinc₁.seq hinc₂))
  have hd₁45 : d₁.reg 45 = f.reg 45 := by simp [d₁,TapeStore.setReg]
  let e := d₁.setReg 45 (d₁.reg 45+1)
  have heStore : e = tickStore f.store := by simp [e,d₁,tickStore,TapeStore.setReg]
  refine ⟨_,_,before,?_,hall,hbefore.trans hcp,?_,?_,?_,?_,?_⟩
  · have h13 := hM 13
    have h4 := hM 4
    have h50 := hM 50
    change s ≤ cellBudget M at hst
    unfold tickBudget
    omega
  · change TapeArrays.EntryWritten before e output _ _ _
    rw [heStore]
    exact ⟨hew.roHead,hew.output,hew.head,hew.symbol⟩
  · change e.reg 42 = _
    rw [heStore]
    simpa [tickStore,TapeStore.setReg] using congrArg (fun v : ℕ => v+1) (hff 42 (by decide))
  · change e.reg 45 = _
    rw [heStore]
    simpa [tickStore,TapeStore.setReg] using congrArg (fun v : ℕ => v+1) (hff 45 (by decide))
  · intro r hr hr42 hr45
    change e.reg r = _
    rw [heStore]
    simpa [tickStore,TapeStore.setReg,hr42,hr45] using hff r hr
  · change SchurCellState ell h input output e M
    rw [heStore]
    constructor
    · simpa [FieldSetup,tickStore,TapeStore.setReg] using hstate.setup
    · exact FieldPrograms.setReg_bound _ 45 (f.store.reg 45+1) M
        (FieldPrograms.setReg_bound f.store 42 (f.store.reg 42+1) M hstate.bounded
          ((congrArg (fun v : ℕ => v+1) (hff 42 (by decide))).le.trans hcol))
        ((congrArg (fun v : ℕ => v+1) (hff 45 (by decide))).le.trans hcut)
    · exact hstate.inputHead
    · exact hstate.outputHead
    · exact hstate.inputMarked
    · exact hstate.outputMarked

#print axioms cellTick_stops

def prefixValues {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : ℕ) (k : Fin (m*n)) : ℕ :=
  if k.val < cut then flatEntry A k.val else old k

def PrefixStored {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : ℕ) (d : Store) (b : Fin 2) : Prop :=
  TapeArrays.ThermometerTable d b q (prefixValues A old cut)

theorem prefixValues_update {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : Fin (m*n)) :
    Function.update (prefixValues A old cut.val) cut (flatEntry A cut.val) =
      prefixValues A old (cut.val+1) := by
  funext j
  by_cases hj : j = cut
  · subst j;simp [prefixValues]
  · have hne : j.val ≠ cut.val := by intro he;exact hj (Fin.ext he)
    simp only [Function.update_of_ne hj,prefixValues]
    split_ifs <;> first | rfl | omega

theorem prefixStored_of_payload {q m n : ℕ} {A : Gaussian.Table (Fin q) m n}
    {old : Fin (m*n) → ℕ} {cut : ℕ} {d e : Store} {b : Fin 2}
    (ht : PrefixStored A old cut d b) (hp : TapeStore.SamePayload e d) : PrefixStored A old cut e b :=
  fun i => (ht i).of_payload hp

theorem prefixStored_written {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : Fin (m*n)) (d e : Store) (b : Fin 2)
    (ht : PrefixStored A old cut.val d b)
    (hw : TapeArrays.EntryWritten d e b (TapeArrays.entryOffset cut.val q) q (flatEntry A cut.val)) :
    PrefixStored A old (cut.val+1) e b := by
  have hv : flatEntry A cut.val ≤ q := by
    rw [flatEntry,dif_pos cut.isLt]
    exact Nat.le_of_lt (Fin.isLt _)
  have h := hw.table hv ht
  rw [prefixValues_update] at h
  exact h

theorem matrixStored_other_written {q m n : ℕ} {A : Gaussian.Table (Fin q) m n}
    {d e : Store} {input output : Fin 2} {start width value : ℕ}
    (ht : MatrixStored d input A) (hio : input ≠ output)
    (hw : TapeArrays.EntryWritten d e output start width value) : MatrixStored e input A := by
  intro i
  refine ⟨(ht i).1,?_⟩
  intro j hj
  rw [hw.symbol]
  simpa [hio] using (ht i).2 j hj

theorem prefixStored_complete {q m n : ℕ} {A : Gaussian.Table (Fin q) m n}
    {old : Fin (m*n) → ℕ} {d : Store} {b : Fin 2}
    (ht : PrefixStored A old (m*n) d b) : MatrixStored d b A := by
  intro i
  have h := ht i
  simpa [prefixValues,i.isLt] using h

#print axioms prefixStored_written

structure ColumnInv {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n) (i : Fin m)
    (old : Fin (m*n) → ℕ) (M : ℕ) (base : Store) (remaining : ℕ) (d : Store) : Prop where
  state : SchurCellState ell h input output d M
  columns : d.reg 40 = n
  rows : d.reg 49 = m
  rowBase : d.reg 41 = i.val*n
  columnCount : d.reg 42+remaining = n
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  cut : d.reg 45 = i.val*n+d.reg 42
  inverse : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored d input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old (d.reg 45) d output
  frame : ∀ r,40 ≤ r.val → r ≠ 42 → r ≠ 45 → r ≠ 47 → d.reg r = base.reg r
  io : d.roHead = base.roHead ∧ d.output = base.output

def columnLoop (input output : Fin 2) : TapeProgram 64 2 1471 :=
  TapeProgram.countedLoop (cellTick input output) 47

theorem columnLoop_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M)
    (base : Store) (remaining : ℕ) (d : Store) (hd : d.reg 47 = remaining)
    (hi : ColumnInv ell h input output A p i old M base remaining d) :
    ∃ t e,t ≤ remaining*(tickBudget M+2)+1 ∧
      (columnLoop input output).Stops inp (d.toCfg (TapeProgram.loopHeader 1469)) t
        (e.toCfg (TapeProgram.loopExit 1469)) ∧
      ColumnInv ell h input output A p i old M base 0 e ∧ e.reg 47 = 0 := by
  apply countedLoop_stops_of_body (cellTick input output) 47 inp (tickBudget M)
    (ColumnInv ell h input output A p i old M base) _ remaining d hd hi
  intro r s hs47 hs
  let s₀ := TapeProgram.decStore (47 : Fin 64) s
  have hp : TapeStore.SamePayload s₀ s := TapeStore.setReg_payload s 47 (s.reg 47-1)
  have hsf (k : Fin 64) (hk : k ≠ 47) : s₀.reg k = s.reg k := by
    simp [s₀,TapeProgram.decStore,hk]
  have hs0b : ∀ k,s₀.reg k ≤ M :=
    FieldPrograms.setReg_bound s 47 (s.reg 47-1) M hs.state.bounded
      ((Nat.sub_le _ _).trans (hs.state.bounded 47))
  have hs0s : FieldSetup ell h s₀ := by
    simpa [FieldSetup,s₀,TapeProgram.decStore] using hs.state.setup
  have hj : s.reg 42 < n := by have := hs.columnCount;omega
  let j : Fin n := ⟨s.reg 42,hj⟩
  have hc : Coordinates p i j s₀ :=
    ⟨(hsf 41 (by decide)).trans hs.rowBase,hsf 42 (by decide),
      (hsf 43 (by decide)).trans hs.pivotColumn,(hsf 44 (by decide)).trans hs.pivotBase,
      by rw [hsf 45 (by decide),hs.cut]⟩
  have hnm : n ≤ M := by
    have hm : 1 ≤ m := by have := i.isLt;omega
    exact (calc n = 1*n := by omega
                _ ≤ m*n := Nat.mul_le_mul_right n hm).trans hsize
  have hcol : s₀.reg 42+1 ≤ M := by rw [hsf 42 (by decide)];omega
  have hidx : s.reg 45 < m*n := by
    rw [hs.cut]
    have hh := (finProdFinEquiv (i,j)).isLt
    change j.val+n*i.val < m*n at hh
    change s.reg 42+n*i.val < m*n at hh
    nlinarith
  have hcut : s₀.reg 45+1 ≤ M := by rw [hsf 45 (by decide)];omega
  obtain ⟨t,e,before,ht,he,hbefore,hew,he42,he45,heframe,hestate⟩ := cellTick_stops input output hio
    ell h inp A p i j s₀ M hs0s hs0b hsize hs.state.inputHead hs.state.outputHead
    (hs.state.inputMarked.of_payload hp) (hs.state.outputMarked.of_payload hp)
    (matrixStored_of_payload hs.inputStored hp) hc
    ((hsf 50 (by decide)).trans hs.inverse) hcol hcut
  have he47 : e.reg 47 = r := by
    rw [heframe 47 (by decide) (by decide) (by decide)]
    simp [s₀,TapeProgram.decStore,hs47]
  have he42' : e.reg 42 = s.reg 42+1 := he42.trans (congrArg (fun v : ℕ => v+1) (hsf 42 (by decide)))
  have he45' : e.reg 45 = s.reg 45+1 := he45.trans (congrArg (fun v : ℕ => v+1) (hsf 45 (by decide)))
  have hef (k : Fin 64) (hk : 40 ≤ k.val) (hk42 : k ≠ 42) (hk45 : k ≠ 45) (hk47 : k ≠ 47) :
      e.reg k = s.reg k := (heframe k hk hk42 hk45).trans (hsf k hk47)
  have hbp : TapeStore.SamePayload before s := hbefore.trans hp
  refine ⟨t,e,ht,he,he47,?_⟩
  refine {
    state:=hestate,
    columns:=(hef 40 (by decide) (by decide) (by decide) (by decide)).trans hs.columns,
    rows:=(hef 49 (by decide) (by decide) (by decide) (by decide)).trans hs.rows,
    rowBase:=(hef 41 (by decide) (by decide) (by decide) (by decide)).trans hs.rowBase,
    columnCount:=?_,
    pivotColumn:=(hef 43 (by decide) (by decide) (by decide) (by decide)).trans hs.pivotColumn,
    pivotBase:=(hef 44 (by decide) (by decide) (by decide) (by decide)).trans hs.pivotBase,
    cut:=?_,
    inverse:=(hef 50 (by decide) (by decide) (by decide) (by decide)).trans hs.inverse,
    inputStored:=matrixStored_other_written (matrixStored_of_payload hs.inputStored hbp) (Ne.symm hio) hew,
    written:=?_,frame:=?_,io:=?_}
  · change e.reg 42+r = n
    rw [he42']
    have := hs.columnCount
    omega
  · change e.reg 45 = i.val*n+e.reg 42
    rw [he45',he42',hs.cut]
    omega
  · let cut : Fin (m*n) := finProdFinEquiv (i,j)
    have hcutidx : cut.val = s.reg 45 := by
      change s.reg 42+n*i.val = s.reg 45
      rw [hs.cut]
      ring
    have hpref : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
        old cut.val before output := by
      rw [hcutidx]
      exact prefixStored_of_payload hs.written hbp
    have hw : TapeArrays.EntryWritten before e.store output (TapeArrays.entryOffset cut.val (2^ell))
        (2^ell) (flatEntry (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) cut.val) := by
      simpa only [cut,flatEntry_pair] using hew
    have hnew := prefixStored_written (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
      old cut before e.store output hpref hw
    rw [hcutidx] at hnew
    change PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
      old (e.reg 45) e.store output
    rw [he45']
    exact hnew
  · intro k hk hk42 hk45 hk47
    exact (hef k hk hk42 hk45 hk47).trans (hs.frame k hk hk42 hk45 hk47)
  · exact ⟨hew.roHead.trans (hbp.roHead.trans hs.io.1),hew.output.trans (hbp.output.trans hs.io.2)⟩

#print axioms columnLoop_stops

theorem state_setReg {ell : ℕ} {h : 0 < ell} {input output : Fin 2} {d : Store} {M : ℕ}
    (hs : SchurCellState ell h input output d M) (r : Fin 64) (v : ℕ)
    (h0 : r ≠ 0) (h36 : r ≠ 36) (h37 : r ≠ 37) (h38 : r ≠ 38) (hv : v ≤ M) :
    SchurCellState ell h input output (d.setReg r v) M := by
  constructor
  · simpa [FieldSetup,TapeStore.setReg,Ne.symm h0,Ne.symm h36,Ne.symm h37,Ne.symm h38] using hs.setup
  · exact FieldPrograms.setReg_bound d r v M hs.bounded hv
  · exact hs.inputHead
  · exact hs.outputHead
  · exact hs.inputMarked.of_payload (TapeStore.setReg_payload d r v)
  · exact hs.outputMarked.of_payload (TapeStore.setReg_payload d r v)

def rowPrepare : TapeProgram 64 2 13 :=
  TapeProgram.seq (TapeMacros.clear 42) (TapeMacros.copy 40 47 4)

def rowPrepareStore (d : Store) : Store :=
  ((d.setReg 42 0).setReg 47 (d.reg 40)).setReg 4 0

theorem rowPrepare_stops (inp : Inputs) (d : Store) :
    ∃ e,rowPrepare.Stops inp (d.toCfg rowPrepare.entry)
      (d.reg 42+d.reg 47+d.reg 4+5*d.reg 40+9) e ∧ e.store = rowPrepareStore d := by
  have hclear := TapeMacros.clear_stops (42 : Fin 64) inp (d.reg 42) d rfl
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (40 : Fin 64) 47 4
    (by decide) (by decide) (by decide) inp (d.setReg 42 0)
  have hall := hclear.seq he
  refine ⟨e.mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (simp [TapeStore.setReg];omega)
  · change e.store = _
    simpa [rowPrepareStore,TapeStore.setReg] using hes

theorem rowPrepare_frame (d : Store) (r : Fin 64) (hr : 40 ≤ r.val) (hr42 : r ≠ 42) (hr47 : r ≠ 47) :
    (rowPrepareStore d).reg r = d.reg r := by
  have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
  simp [rowPrepareStore,TapeStore.setReg,hr42,hr47,h4]

def rowBudget (n M : ℕ) : ℕ := n*(tickBudget M+2)+20*(M+1)

def rowBody (input output : Fin 2) : TapeProgram 64 2 1493 :=
  TapeProgram.seq rowPrepare
    (TapeProgram.seq (columnLoop input output) (TapeMacros.addPreserving 40 41 4))

structure RowStart {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n) (i : Fin m)
    (old : Fin (m*n) → ℕ) (M : ℕ) (d : Store) : Prop where
  state : SchurCellState ell h input output d M
  columns : d.reg 40 = n
  rows : d.reg 49 = m
  rowBase : d.reg 41 = i.val*n
  cut : d.reg 45 = i.val*n
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  inverse : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored d input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old (i.val*n) d output

structure RowOutcome {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n) (i : Fin m)
    (old : Fin (m*n) → ℕ) (M : ℕ) (d e : Store) : Prop where
  state : SchurCellState ell h input output e M
  columns : e.reg 40 = n
  rows : e.reg 49 = m
  nextBase : e.reg 41 = (i.val+1)*n
  nextCut : e.reg 45 = (i.val+1)*n
  pivotColumn : e.reg 43 = p.2.val
  pivotBase : e.reg 44 = p.1.val*n
  inverse : e.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored e input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old ((i.val+1)*n) e output
  columnDone : e.reg 42 = n
  countDone : e.reg 47 = 0
  frame : ∀ r,40 ≤ r.val → r ≠ 41 → r ≠ 42 → r ≠ 45 → r ≠ 47 → e.reg r = d.reg r
  io : e.roHead = d.roHead ∧ e.output = d.output

theorem rowBody_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M)
    (d : Store) (hi : RowStart ell h input output A p i old M d) :
    ∃ t e,t ≤ rowBudget n M ∧
      (rowBody input output).Stops inp (d.toCfg (rowBody input output).entry) t e ∧
      RowOutcome ell h input output A p i old M d e.store := by
  obtain ⟨c,hc,hcs⟩ := rowPrepare_stops inp d
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans
      ((TapeStore.setReg_payload _ 47 (d.reg 40)).trans (TapeStore.setReg_payload d 42 0))
  have hcf (r : Fin 64) (hr : 40 ≤ r.val) (hr42 : r ≠ 42) (hr47 : r ≠ 47) : c.reg r = d.reg r := by
    change c.store.reg r = _
    rw [hcs]
    exact rowPrepare_frame d r hr hr42 hr47
  have hcstate : SchurCellState ell h input output c.store M := by
    rw [hcs]
    exact state_setReg (state_setReg (state_setReg hi.state 42 0 (by decide) (by decide) (by decide) (by decide)
      (Nat.zero_le M)) 47 (d.reg 40) (by decide) (by decide) (by decide) (by decide) (hi.state.bounded 40))
      4 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  have hc42 : c.reg 42 = 0 := by change c.store.reg 42 = _;rw [hcs];simp [rowPrepareStore,TapeStore.setReg]
  have hc47 : c.reg 47 = n := by change c.store.reg 47 = _;rw [hcs];simp [rowPrepareStore,TapeStore.setReg,hi.columns]
  have hInit : ColumnInv ell h input output A p i old M d n c.store := by
    refine {
      state:=hcstate,
      columns:=(hcf 40 (by decide) (by decide) (by decide)).trans hi.columns,
      rows:=(hcf 49 (by decide) (by decide) (by decide)).trans hi.rows,
      rowBase:=(hcf 41 (by decide) (by decide) (by decide)).trans hi.rowBase,
      columnCount:=by simpa only [hc42,Nat.zero_add],
      pivotColumn:=(hcf 43 (by decide) (by decide) (by decide)).trans hi.pivotColumn,
      pivotBase:=(hcf 44 (by decide) (by decide) (by decide)).trans hi.pivotBase,
      cut:=?_,inverse:=(hcf 50 (by decide) (by decide) (by decide)).trans hi.inverse,
      inputStored:=matrixStored_of_payload hi.inputStored hcp,written:=?_,frame:=?_,io:=⟨hcp.roHead,hcp.output⟩}
    · change c.reg 45 = i.val*n+c.reg 42
      rw [hcf 45 (by decide) (by decide) (by decide),hi.cut,hc42]
      omega
    · change PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
        old (c.reg 45) c.store output
      rw [hcf 45 (by decide) (by decide) (by decide),hi.cut]
      exact prefixStored_of_payload hi.written hcp
    · intro r hr hr42 hr45 hr47
      exact hcf r hr hr42 hr47
  obtain ⟨s,f,hs,hf,hfo,hf47⟩ := columnLoop_stops input output hio ell h inp A p i old M hsize d n c.store hc47 hInit
  have hf42 : f.reg 42 = n := by have := hfo.columnCount;omega
  have hf41 : f.reg 41 = i.val*n := hfo.rowBase
  have hf40 : f.reg 40 = n := hfo.columns
  have hf45 : f.reg 45 = (i.val+1)*n := by rw [hfo.cut,hf42];ring
  have hsum : f.reg 41+f.reg 40 ≤ M := by
    rw [hf41,hf40]
    have hp := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    nlinarith
  obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops (40 : Fin 64) 41 4
    (by decide) (by decide) (by decide) inp f
  have her : e.reg = ((f.setReg 41 (f.reg 41+f.reg 40)).setReg 4 0).reg := congrArg TapeStore.reg hes
  have hep : TapeStore.SamePayload e.store f := by
    rw [hes]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload f 41 (f.reg 41+f.reg 40))
  have hef (r : Fin 64) (hr : 40 ≤ r.val) (hr41 : r ≠ 41) : e.reg r = f.reg r := by
    rw [her]
    have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
    simp [TapeStore.setReg,hr41,h4]
  have hall := hc.seq (hf.seq he)
  refine ⟨_,_,?_,hall,?_⟩
  · have ht₁ : d.reg 42+d.reg 47+d.reg 4+5*d.reg 40+9 ≤ 8*M+9 := by
      have := hi.state.bounded 42;have := hi.state.bounded 47;have := hi.state.bounded 4;have := hi.state.bounded 40;omega
    have ht₂ : f.reg 4+5*f.reg 40+5 ≤ 6*M+5 := by
      have := hfo.state.bounded 4;have := hfo.state.bounded 40;omega
    unfold rowBudget
    omega
  · change RowOutcome ell h input output A p i old M d e.store
    refine {
      state:=?_,columns:=(hef 40 (by decide) (by decide)).trans hfo.columns,
      rows:=(hef 49 (by decide) (by decide)).trans hfo.rows,nextBase:=?_,nextCut:=?_,
      pivotColumn:=(hef 43 (by decide) (by decide)).trans hfo.pivotColumn,
      pivotBase:=(hef 44 (by decide) (by decide)).trans hfo.pivotBase,
      inverse:=(hef 50 (by decide) (by decide)).trans hfo.inverse,
      inputStored:=matrixStored_of_payload hfo.inputStored hep,written:=?_,
      columnDone:=(hef 42 (by decide) (by decide)).trans hf42,
      countDone:=(hef 47 (by decide) (by decide)).trans hf47,frame:=?_,
      io:=⟨hep.roHead.trans hfo.io.1,hep.output.trans hfo.io.2⟩}
    · rw [hes]
      exact state_setReg (state_setReg hfo.state 41 (f.reg 41+f.reg 40)
        (by decide) (by decide) (by decide) (by decide) hsum)
        4 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
    · change e.reg 41 = _
      rw [her]
      simp [TapeStore.setReg,hf41,hf40,Nat.add_mul]
    · exact (hef 45 (by decide) (by decide)).trans hf45
    · have hh := prefixStored_of_payload hfo.written hep
      rw [hf45] at hh
      exact hh
    · intro r hr hr41 hr42 hr45 hr47
      exact (hef r hr hr41).trans (hfo.frame r hr hr42 hr45 hr47)

#print axioms rowBody_stops

structure RowsInv {m n : ℕ} (ell : ℕ) (h : 0 < ell) (input output : Fin 2)
    (A : Gaussian.Table (Fin (2^ell)) m n) (p : Fin m × Fin n)
    (old : Fin (m*n) → ℕ) (M : ℕ) (base : Store) (remaining : ℕ) (d : Store) : Prop where
  atMost : remaining ≤ m
  state : SchurCellState ell h input output d M
  columns : d.reg 40 = n
  rows : d.reg 49 = m
  rowBase : d.reg 41 = (m-remaining)*n
  cut : d.reg 45 = (m-remaining)*n
  pivotColumn : d.reg 43 = p.2.val
  pivotBase : d.reg 44 = p.1.val*n
  inverse : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
    (Gaussian.toMatrix A p.1 p.2)).val
  inputStored : MatrixStored d input A
  written : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
    old ((m-remaining)*n) d output
  frame : ∀ r,40 ≤ r.val → r ≠ 41 → r ≠ 42 → r ≠ 45 → r ≠ 46 → r ≠ 47 → d.reg r = base.reg r
  io : d.roHead = base.roHead ∧ d.output = base.output

def rowLoop (input output : Fin 2) : TapeProgram 64 2 1495 := TapeProgram.countedLoop (rowBody input output) 46

theorem rowLoop_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M)
    (base : Store) (remaining : ℕ) (d : Store) (hd : d.reg 46 = remaining)
    (hi : RowsInv ell h input output A p old M base remaining d) :
    ∃ t e,t ≤ remaining*(rowBudget n M+2)+1 ∧
      (rowLoop input output).Stops inp (d.toCfg (TapeProgram.loopHeader 1493)) t
        (e.toCfg (TapeProgram.loopExit 1493)) ∧
      RowsInv ell h input output A p old M base 0 e ∧ e.reg 46 = 0 := by
  apply countedLoop_stops_of_body (rowBody input output) 46 inp (rowBudget n M)
    (RowsInv ell h input output A p old M base) _ remaining d hd hi
  intro r s hs46 hs
  let s₀ := TapeProgram.decStore (46 : Fin 64) s
  have hp : TapeStore.SamePayload s₀ s := TapeStore.setReg_payload s 46 (s.reg 46-1)
  have hsf (k : Fin 64) (hk : k ≠ 46) : s₀.reg k = s.reg k := by simp [s₀,TapeProgram.decStore,hk]
  have hj : m-(r+1) < m := by have := hs.atMost;omega
  let i : Fin m := ⟨m-(r+1),hj⟩
  have hstart : RowStart ell h input output A p i old M s₀ := by
    refine {
      state:=state_setReg hs.state 46 (s.reg 46-1) (by decide) (by decide) (by decide) (by decide)
        ((Nat.sub_le _ _).trans (hs.state.bounded 46)),
      columns:=(hsf 40 (by decide)).trans hs.columns,
      rows:=(hsf 49 (by decide)).trans hs.rows,
      rowBase:=(hsf 41 (by decide)).trans hs.rowBase,
      cut:=(hsf 45 (by decide)).trans hs.cut,
      pivotColumn:=(hsf 43 (by decide)).trans hs.pivotColumn,
      pivotBase:=(hsf 44 (by decide)).trans hs.pivotBase,
      inverse:=(hsf 50 (by decide)).trans hs.inverse,
      inputStored:=matrixStored_of_payload hs.inputStored hp,
      written:=prefixStored_of_payload hs.written hp}
  obtain ⟨t,e,ht,he,ho⟩ := rowBody_stops input output hio ell h inp A p i old M hsize s₀ hstart
  have he46 : e.reg 46 = r := by
    change e.store.reg 46 = r
    rw [ho.frame 46 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₀,TapeProgram.decStore,hs46]
  have hnext : (i.val+1)*n = (m-r)*n := by
    have heq : i.val+1 = m-r := by change m-(r+1)+1 = m-r;have := hs.atMost;omega
    rw [heq]
  refine ⟨t,e,ht,he,he46,?_⟩
  refine {
    atMost:=by have := hs.atMost;omega,
    state:=ho.state,columns:=ho.columns,rows:=ho.rows,
    rowBase:=ho.nextBase.trans hnext,cut:=ho.nextCut.trans hnext,
    pivotColumn:=ho.pivotColumn,pivotBase:=ho.pivotBase,inverse:=ho.inverse,
    inputStored:=ho.inputStored,written:=?_,frame:=?_,
    io:=⟨ho.io.1.trans (hp.roHead.trans hs.io.1),ho.io.2.trans (hp.output.trans hs.io.2)⟩}
  · simpa only [hnext] using ho.written
  · intro k hk hk41 hk42 hk45 hk46 hk47
    exact ((ho.frame k hk hk41 hk42 hk45 hk47).trans (hsf k hk46)).trans
      (hs.frame k hk hk41 hk42 hk45 hk46 hk47)

def gridPrepare : TapeProgram 64 2 15 :=
  TapeProgram.seq (TapeMacros.clear 41) (TapeProgram.seq (TapeMacros.clear 45) (TapeMacros.copy 49 46 4))

def gridPrepareStore (d : Store) : Store :=
  (((d.setReg 41 0).setReg 45 0).setReg 46 (d.reg 49)).setReg 4 0

theorem gridPrepare_stops (inp : Inputs) (d : Store) :
    ∃ e,gridPrepare.Stops inp (d.toCfg gridPrepare.entry)
      (d.reg 41+d.reg 45+d.reg 46+d.reg 4+5*d.reg 49+11) e ∧ e.store = gridPrepareStore d := by
  have h₁ := TapeMacros.clear_stops (41 : Fin 64) inp (d.reg 41) d rfl
  have h₂ := TapeMacros.clear_stops (45 : Fin 64) inp (d.reg 45) (d.setReg 41 0) (by simp [TapeStore.setReg])
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (49 : Fin 64) 46 4 (by decide) (by decide) (by decide)
    inp ((d.setReg 41 0).setReg 45 0)
  have hall := h₁.seq (h₂.seq he)
  refine ⟨(e.mapPC (TapeProgram.rightLabel 2)).mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (simp [TapeStore.setReg];omega)
  · change e.store = _
    simpa [gridPrepareStore,TapeStore.setReg] using hes

theorem gridPrepare_frame (d : Store) (r : Fin 64) (hr : 40 ≤ r.val)
    (hr41 : r ≠ 41) (hr45 : r ≠ 45) (hr46 : r ≠ 46) : (gridPrepareStore d).reg r = d.reg r := by
  have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
  simp [gridPrepareStore,TapeStore.setReg,h4,hr41,hr45,hr46]

def materializeGrid (input output : Fin 2) : TapeProgram 64 2 1510 :=
  TapeProgram.seq gridPrepare (rowLoop input output)

theorem materializeGrid_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M) (d : Store)
    (hstate : SchurCellState ell h input output d M)
    (hcols : d.reg 40 = n) (hrows : d.reg 49 = m)
    (hpc : d.reg 43 = p.2.val) (hpr : d.reg 44 = p.1.val*n)
    (hInv : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val)
    (hinput : MatrixStored d input A) (houtput : TapeArrays.ThermometerTable d output (2^ell) old) :
    ∃ t e,t ≤ 20*(M+1)+m*(rowBudget n M+2)+2 ∧
      (materializeGrid input output).Stops inp (d.toCfg (materializeGrid input output).entry) t e ∧
      SchurCellState ell h input output e.store M ∧ MatrixStored e.store input A ∧
      MatrixStored e.store output (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) ∧
      e.reg 41 = m*n ∧ e.reg 45 = m*n ∧ e.reg 46 = 0 ∧
      (∀ r,40 ≤ r.val → r ≠ 41 → r ≠ 42 → r ≠ 45 → r ≠ 46 → r ≠ 47 → e.reg r = d.reg r) ∧
      e.roHead = d.roHead ∧ e.output = d.output := by
  obtain ⟨c,hc,hcs⟩ := gridPrepare_stops inp d
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans ((TapeStore.setReg_payload _ 46 (d.reg 49)).trans
      ((TapeStore.setReg_payload _ 45 0).trans (TapeStore.setReg_payload d 41 0)))
  have hcf (r : Fin 64) (hr : 40 ≤ r.val) (hr41 : r ≠ 41) (hr45 : r ≠ 45) (hr46 : r ≠ 46) :
      c.reg r = d.reg r := by change c.store.reg r = _;rw [hcs];exact gridPrepare_frame d r hr hr41 hr45 hr46
  have hc41 : c.reg 41 = 0 := by change c.store.reg 41 = _;rw [hcs];simp [gridPrepareStore,TapeStore.setReg]
  have hc45 : c.reg 45 = 0 := by change c.store.reg 45 = _;rw [hcs];simp [gridPrepareStore,TapeStore.setReg]
  have hc46 : c.reg 46 = m := by change c.store.reg 46 = _;rw [hcs];simp [gridPrepareStore,TapeStore.setReg,hrows]
  have hcstate : SchurCellState ell h input output c.store M := by
    rw [hcs]
    exact state_setReg (state_setReg (state_setReg (state_setReg hstate 41 0 (by decide) (by decide) (by decide) (by decide)
      (Nat.zero_le M)) 45 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M))
      46 (d.reg 49) (by decide) (by decide) (by decide) (by decide) (hstate.bounded 49))
      4 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  have hInit : RowsInv ell h input output A p old M d m c.store := by
    refine {
      atMost:=le_rfl,state:=hcstate,
      columns:=(hcf 40 (by decide) (by decide) (by decide) (by decide)).trans hcols,
      rows:=(hcf 49 (by decide) (by decide) (by decide) (by decide)).trans hrows,
      rowBase:=by simpa only [Nat.sub_self,Nat.zero_mul] using hc41,
      cut:=by simpa only [Nat.sub_self,Nat.zero_mul] using hc45,
      pivotColumn:=(hcf 43 (by decide) (by decide) (by decide) (by decide)).trans hpc,
      pivotBase:=(hcf 44 (by decide) (by decide) (by decide) (by decide)).trans hpr,
      inverse:=(hcf 50 (by decide) (by decide) (by decide) (by decide)).trans hInv,
      inputStored:=matrixStored_of_payload hinput hcp,written:=?_,frame:=?_,io:=⟨hcp.roHead,hcp.output⟩}
    · have hout : TapeArrays.ThermometerTable c.store output (2^ell) old := fun j => (houtput j).of_payload hcp
      intro k
      simpa [prefixValues] using hout k
    · intro r hr hr41 hr42 hr45 hr46 hr47
      exact hcf r hr hr41 hr45 hr46
  obtain ⟨s,e,hs,he,ho,he46⟩ := rowLoop_stops input output hio ell h inp A p old M hsize d m c.store hc46 hInit
  have hall := hc.seq he
  refine ⟨_,_,?_,hall,ho.state,ho.inputStored,?_,?_,?_,he46,ho.frame,ho.io.1,ho.io.2⟩
  · have ht : d.reg 41+d.reg 45+d.reg 46+d.reg 4+5*d.reg 49+11 ≤ 20*(M+1) := by
      have := hstate.bounded 41;have := hstate.bounded 45;have := hstate.bounded 46
      have := hstate.bounded 4;have := hstate.bounded 49;omega
    omega
  · apply prefixStored_complete
    simpa only [Nat.sub_zero] using ho.written
  · simpa only [Nat.sub_zero] using ho.rowBase
  · simpa only [Nat.sub_zero] using ho.cut

#print axioms materializeGrid_stops

end ExpandingCodes.Computation.GaussianGrid
