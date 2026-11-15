import ExpandingCodes.Computation.ParameterFrames
import ExpandingCodes.Computation.ParameterPolynomial
import ExpandingCodes.Computation.SizeReader

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- Eight stable outputs followed by six ordinary unary scratch registers.
The ambient map permits the sampler's fixed point/neighbor registers to live
outside this frame. -/
def setupPowerPIndex : Fin 6 → Fin 14 := ![0,1,8,9,10,11]
def setupCeilingIndex : Fin 8 → Fin 14 := ![3,1,8,9,10,11,2,12]
def setupPowerMIndex : Fin 6 → Fin 14 := ![3,4,8,9,10,11]
def setupDivisionIndex : Fin 4 → Fin 14 := ![0,5,8,9]
def setupFloorIndex : Fin 9 → Fin 14 := ![7,5,8,9,10,11,6,12,13]

def setupPowerPLayout (r : Fin 14 → Fin R) : Fin 6 → Fin R := r ∘ setupPowerPIndex
def setupCeilingLayout (r : Fin 14 → Fin R) : Fin 8 → Fin R := r ∘ setupCeilingIndex
def setupPowerMLayout (r : Fin 14 → Fin R) : Fin 6 → Fin R := r ∘ setupPowerMIndex
def setupDivisionLayout (r : Fin 14 → Fin R) : Fin 4 → Fin R := r ∘ setupDivisionIndex
def setupFloorLayout (r : Fin 14 → Fin R) : Fin 9 → Fin R := r ∘ setupFloorIndex

theorem setupPowerP_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupPowerPLayout r) := hr.comp (by decide)
theorem setupCeiling_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupCeilingLayout r) := hr.comp (by decide)
theorem setupPowerM_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupPowerMLayout r) := hr.comp (by decide)
theorem setupDivision_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupDivisionLayout r) := hr.comp (by decide)
theorem setupFloor_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupFloorLayout r) := hr.comp (by decide)

def setupLabels (d k : ℕ) : ℕ := (((fixedPowerLabels (2*d)+77)+fixedPowerLabels d)+(13+(k+2)))+104

/-- Actual finite setup code: n^(2d), ceiling power of two, q^d, quotient by
fixed positive k, and floor power of two. Its labels depend only on fixed d,k. -/
def setup (r : Fin 14 → Fin R) (d k : ℕ) : TapeProgram R B (setupLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (fixedPower (setupPowerPLayout r) (2*d)) (ceilingPowerTwo (setupCeilingLayout r)))
    (fixedPower (setupPowerMLayout r) d)) (divideConstant (setupDivisionLayout r) k))
    (floorPowerTwo (setupFloorLayout r))

def setupStage₁ (r : Fin 14 → Fin R) (d : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  fixedPowerStore (setupPowerPLayout r) (2*d) σ
def setupStage₂ (r : Fin 14 → Fin R) (d : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  ceilingPowerStore (setupCeilingLayout r) (setupStage₁ r d σ)
def setupStage₃ (r : Fin 14 → Fin R) (d : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  fixedPowerStore (setupPowerMLayout r) d (setupStage₂ r d σ)
def setupStage₄ (r : Fin 14 → Fin R) (d k : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  divideConstantStore (setupDivisionLayout r) k (setupStage₃ r d σ)
def setupStore (r : Fin 14 → Fin R) (d k : ℕ) (σ : TapeStore R B) : TapeStore R B :=
  floorPowerStore (setupFloorLayout r) (setupStage₄ r d k σ)

theorem setupStage₁_n (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) : (setupStage₁ r d σ).reg (r 0)=σ.reg (r 0) :=
  fixedPowerStore_base _ (setupPowerP_inj r hr) _ _
theorem setupStage₁_p (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) : (setupStage₁ r d σ).reg (r 1)=σ.reg (r 0)^(2*d) :=
  fixedPowerStore_value _ (setupPowerP_inj r hr) _ _

theorem setupStage₂_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<2) :
    (setupStage₂ r d σ).reg (r j)=(setupStage₁ r d σ).reg (r j) := by
  apply ceilingPowerStore_fresh _ (setupCeiling_inj r hr)
  all_goals simp [setupCeilingLayout,setupCeilingIndex,hr.eq_iff]; omega

theorem setupStage₃_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<4) :
    (setupStage₃ r d σ).reg (r j)=(setupStage₂ r d σ).reg (r j) := by
  apply fixedPowerStore_fresh
  all_goals simp [setupPowerMLayout,setupPowerMIndex,hr.eq_iff]; omega

theorem setupStage₄_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<5) :
    (setupStage₄ r d k σ).reg (r j)=(setupStage₃ r d σ).reg (r j) := by
  apply divideConstantStore_fresh
  all_goals simp [setupDivisionLayout,setupDivisionIndex,hr.eq_iff]; omega

theorem setupStore_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<6) :
    (setupStore r d k σ).reg (r j)=(setupStage₄ r d k σ).reg (r j) := by
  apply floorPowerStore_fresh _ (setupFloor_inj r hr)
  all_goals simp [setupFloorLayout,setupFloorIndex,hr.eq_iff]; omega

theorem setupStage₂_qell (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (hp : 1≤σ.reg (r 0)^(2*d)) :
    ((setupStage₂ r d σ).reg (r 3),(setupStage₂ r d σ).reg (r 2)) =
      (2^Nat.clog 2 (σ.reg (r 0)^(2*d)),Nat.clog 2 (σ.reg (r 0)^(2*d))) := by
  have h := ceilingPowerStore_exact (setupCeilingLayout r) (setupCeiling_inj r hr)
    (setupStage₁ r d σ) (by simpa only [show setupCeilingLayout r 1=r 1 from rfl,setupStage₁_p r hr] using hp)
  simpa only [setupStage₂,show setupCeilingLayout r 0=r 3 from rfl,
    show setupCeilingLayout r 6=r 2 from rfl,show setupCeilingLayout r 1=r 1 from rfl,setupStage₁_p r hr] using h

theorem setupStage₃_m (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) :
    (setupStage₃ r d σ).reg (r 4)=(setupStage₂ r d σ).reg (r 3)^d :=
  fixedPowerStore_value _ (setupPowerM_inj r hr) _ _

theorem setupStage₄_u (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) :
    (setupStage₄ r d k σ).reg (r 5)=σ.reg (r 0)/k := by
  have h := divideConstantStore_value (setupDivisionLayout r) (setupDivision_inj r hr) k (setupStage₃ r d σ)
  change (setupStage₄ r d k σ).reg (r 5)=(setupStage₃ r d σ).reg (r 0)/k at h
  rw [setupStage₃_frame r hr d σ 0 (by decide),setupStage₂_frame r hr d σ 0 (by decide),setupStage₁_n r hr] at h
  exact h

/-- The eight setup counters, exactly identified with the frozen mission sizes.
No modulus-search or field-construction computation is asserted here. -/
theorem setupStore_values (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (hd : 1≤d) (hk : 0<k) (σ : TapeStore R B)
    (hn : 2≤σ.reg (r 0)) (hnk : k≤σ.reg (r 0)) :
    let n := σ.reg (r 0)
    let ell := ExpandingCodes.PolynomialStretch.fieldExponent d n
    let q := ExpandingCodes.PolynomialStretch.fieldSize d n
    (setupStore r d k σ).reg (r 0)=n ∧
    (setupStore r d k σ).reg (r 1)=n^(2*d) ∧
    (setupStore r d k σ).reg (r 2)=ell ∧
    (setupStore r d k σ).reg (r 3)=q ∧
    (setupStore r d k σ).reg (r 4)=ExpandingCodes.PolynomialStretch.rowCount d n ∧
    (setupStore r d k σ).reg (r 5)=n/k ∧
    (setupStore r d k σ).reg (r 6)=Nat.log 2 (n/k) ∧
    (setupStore r d k σ).reg (r 7)=2^Nat.log 2 (n/k) := by
  dsimp only
  have hp : 2≤σ.reg (r 0)^(2*d) := by
    have hpow := Nat.pow_le_pow_right (show 0<σ.reg (r 0) by omega) (show 1≤2*d by omega)
    simp only [pow_one] at hpow
    omega
  have hc : 1≤Nat.clog 2 (σ.reg (r 0)^(2*d)) := Nat.clog_pos (by decide) (by omega)
  have hqell := setupStage₂_qell r hr d σ (by omega)
  have hu : 1≤(setupStage₄ r d k σ).reg (r 5) := by
    rw [setupStage₄_u r hr]
    exact (Nat.le_div_iff_mul_le hk).mpr (by simpa using hnk)
  have hfloor := floorPowerStore_exact (setupFloorLayout r) (setupFloor_inj r hr) (setupStage₄ r d k σ) hu
  change ((setupStore r d k σ).reg (r 7),(setupStore r d k σ).reg (r 6)) = _ at hfloor
  have hfq := congrArg Prod.fst hqell
  have hfe := congrArg Prod.snd hqell
  dsimp only at hfq hfe
  have hfb := congrArg Prod.fst hfloor
  have hfl := congrArg Prod.snd hfloor
  simp only [Prod.fst,Prod.snd,show setupFloorLayout r 1=r 5 from rfl,setupStage₄_u r hr] at hfb hfl
  have hcommon : ∀ j : Fin 14, j.val<4 →
      (setupStore r d k σ).reg (r j)=(setupStage₂ r d σ).reg (r j) := by
    intro j hj
    rw [setupStore_frame r hr d k σ j (by omega),setupStage₄_frame r hr d k σ j (by omega),
      setupStage₃_frame r hr d σ j hj]
  refine ⟨?_,?_,?_,?_,?_,?_,hfl,hfb⟩
  · rw [hcommon 0 (by decide),setupStage₂_frame r hr d σ 0 (by decide),setupStage₁_n r hr]
  · rw [hcommon 1 (by decide),setupStage₂_frame r hr d σ 1 (by decide),setupStage₁_p r hr]
  · rw [hcommon 2 (by decide),hfe]
    simp [ExpandingCodes.PolynomialStretch.fieldExponent,max_eq_right hc]
  · rw [hcommon 3 (by decide),hfq]
    simp [ExpandingCodes.PolynomialStretch.fieldSize,ExpandingCodes.PolynomialStretch.fieldExponent,max_eq_right hc]
  · rw [setupStore_frame r hr d k σ 4 (by decide),setupStage₄_frame r hr d k σ 4 (by decide),setupStage₃_m r hr,hfq]
    simp [ExpandingCodes.PolynomialStretch.rowCount,ExpandingCodes.PolynomialStretch.fieldSize,
      ExpandingCodes.PolynomialStretch.fieldExponent,max_eq_right hc]
  · rw [setupStore_frame r hr d k σ 5 (by decide),setupStage₄_u r hr]

theorem setupStore_payload (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) : SamePayload σ (setupStore r d k σ) := by
  exact ((((fixedPowerStore_payload _ _ _).trans
    (ceilingPowerStore_payload _ (setupCeiling_inj r hr) _)).trans
    (fixedPowerStore_payload _ _ _)).trans (divideConstantStore_payload _ _ _)).trans
    (floorPowerStore_payload _ (setupFloor_inj r hr) _)

theorem setupStore_fresh (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin R) (h : ∀ i, j≠r i) :
    (setupStore r d k σ).reg j=σ.reg j := by
  calc
    (setupStore r d k σ).reg j=(setupStage₄ r d k σ).reg j :=
      floorPowerStore_fresh _ (setupFloor_inj r hr) _ j (h _) (h _) (h _) (h _) (h _) (h _) (h _) (h _)
    _=(setupStage₃ r d σ).reg j := divideConstantStore_fresh _ _ _ j (h _) (h _) (h _)
    _=(setupStage₂ r d σ).reg j := fixedPowerStore_fresh _ _ _ j (h _) (h _) (h _) (h _) (h _)
    _=(setupStage₁ r d σ).reg j :=
      ceilingPowerStore_fresh _ (setupCeiling_inj r hr) _ j (h _) (h _) (h _) (h _) (h _) (h _) (h _)
    _=σ.reg j := fixedPowerStore_fresh _ _ _ j (h _) (h _) (h _) (h _) (h _)

theorem powerCounterBound_pos (e M : ℕ) : 1≤powerCounterBound e M := by
  have h := Nat.one_le_pow (e+1) (M+1) (by omega)
  unfold powerCounterBound
  nlinarith

theorem setup_stops (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (hk : 0<k) (inp : Inputs) (M : ℕ) (hM : 1≤M)
    (σ : TapeStore R B) (hσ : ∀ j, σ.reg j≤M)
    (hn : 1≤σ.reg (r 0)) (hnk : k≤σ.reg (r 0)) :
    ∃ t z, t≤ setupTimeBound d M ∧
      (setup r d k).Stops inp (σ.toCfg (setup (B := B) r d k).entry) t z ∧
      z.store=setupStore r d k σ ∧ ∀ j, z.reg j≤ setupCounterBound d M := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := fixedPower_stops (setupPowerPLayout r) (setupPowerP_inj r hr)
    (2*d) inp M hM σ hσ hn
  have hs₁' : c₁.store=setupStage₁ r d σ := hs₁
  have hp : 1≤c₁.reg (r 1) := by
    change 1≤c₁.store.reg (r 1)
    rw [hs₁',setupStage₁_p r hr]
    exact Nat.one_le_pow _ _ hn
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := ceilingPowerTwo_stops (setupCeilingLayout r) (setupCeiling_inj r hr)
    inp (setupBound₁ d M) (powerCounterBound_pos _ _) c₁.store hb₁ hp
  have hs₂' : c₂.store=setupStage₂ r d σ := by rw [hs₂,hs₁']; rfl
  have hq : 1≤c₂.reg (r 3) := by
    change 1≤c₂.store.reg (r 3)
    rw [hs₂']
    have h := ceilingPowerStore_exact (setupCeilingLayout r) (setupCeiling_inj r hr) c₁.store hp
    have hval := congrArg Prod.fst h
    change (ceilingPowerStore (setupCeilingLayout r) c₁.store).reg (r 3)=_ at hval
    rw [hs₁'] at hval
    change (setupStage₂ r d σ).reg (r 3)=_ at hval
    rw [hval]
    exact Nat.one_le_pow _ _ (by decide)
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := fixedPower_stops (setupPowerMLayout r) (setupPowerM_inj r hr)
    d inp (setupBound₂ d M) (by unfold setupBound₂ ceilingCounterBound; omega) c₂.store hb₂ hq
  have hs₃' : c₃.store=setupStage₃ r d σ := by rw [hs₃,hs₂']; rfl
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄⟩ := divideConstant_stops (setupDivisionLayout r) (setupDivision_inj r hr)
    k hk inp (setupBound₃ d M) c₃.store hb₃
  have hs₄' : c₄.store=setupStage₄ r d k σ := by rw [hs₄,hs₃']; rfl
  have hu : 1≤c₄.reg (r 5) := by
    change 1≤c₄.store.reg (r 5)
    rw [hs₄',setupStage₄_u r hr]
    exact (Nat.le_div_iff_mul_le hk).mpr (by simpa using hnk)
  obtain ⟨t₅,c₅,ht₅,h₅,hs₅,hb₅⟩ := floorPowerTwo_stops (setupFloorLayout r) (setupFloor_inj r hr)
    inp (setupBound₃ d M) (powerCounterBound_pos _ _) c₄.store hb₄ hu
  have hall := (((h₁.seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_,hb₅⟩
  · unfold setupTimeBound powerTimeBound ceilingTimeBound divisionTimeBound floorTimeBound
    omega
  · change c₅.store=setupStore r d k σ
    rw [hs₅,hs₄']
    rfl

theorem setup_uniform_polynomial (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (hk : 0<k) :
    ∃ C a, ∀ (inp : Inputs) (M : ℕ) (σ : TapeStore R B),
      1≤M → (∀ j, σ.reg j≤M) → 1≤σ.reg (r 0) → k≤σ.reg (r 0) →
      ∃ t z, t≤C*(M+1)^a ∧
        (setup r d k).Stops inp (σ.toCfg (setup (B := B) r d k).entry) t z ∧
        z.store=setupStore r d k σ ∧ SamePayload σ z.store := by
  obtain ⟨C,a,hpoly⟩ := (setup_bounds_polynomial d).1
  refine ⟨C,a,?_⟩
  intro inp M σ hM hσ hn hnk
  obtain ⟨t,z,ht,hstop,hstore,hbound⟩ := setup_stops r hr d k hk inp M hM σ hσ hn hnk
  exact ⟨t,z,ht.trans (hpoly M),hstop,hstore,by rw [hstore]; exact setupStore_payload r hr d k σ⟩

/-- Complete unary-input frontend. The scanner consumes true^n,false; every
subsequent setup instruction preserves that input head and the random tape. -/
def setupInput (r : Fin 14 → Fin R) (d k : ℕ) : TapeProgram R B (5+setupLabels d k) :=
  TapeProgram.seq (SizeReader.sizeInput (r 0)) (setup r d k)

theorem setupInput_unary (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (hk : 0<k) :
    ∃ C a, ∀ (n : ℕ) (hn : 2≤n) (hnk : k≤n)
      (inp : Inputs) (tail : List Bool) (σ : TapeStore R B),
      (∀ j, σ.reg j=0) → σ.roHead 0=0 →
      inp.input=List.replicate n true ++ false :: tail →
      ∃ t z, t≤C*(n+1)^a ∧
        (setupInput r d k).Stops inp (σ.toCfg (setupInput (B := B) r d k).entry) t z ∧
        z.store=setupStore r d k (SizeReader.sizeStore (r 0) n σ) ∧
        SamePayload (SizeReader.sizeStore (r 0) n σ) z.store := by
  have hpoly : PolynomialMajorant (fun n => 2*n+4+setupTimeBound d (n+1)) :=
    (((PolynomialMajorant.const 2).mul PolynomialMajorant.id).add (PolynomialMajorant.const 4)).add
      ((setup_bounds_polynomial d).1.comp (PolynomialMajorant.id.add (PolynomialMajorant.const 1)))
  obtain ⟨C,a,hpoly⟩ := hpoly
  refine ⟨C,a,?_⟩
  intro n hn hnk inp tail σ hz hh hi
  have hread := SizeReader.sizeInput_unary (r 0) inp n tail σ hh hi
  have hb : ∀ j, (SizeReader.sizeStore (r 0) n σ).reg j≤n+1 := by
    intro j
    by_cases h : j=r 0
    · subst j; simp [SizeReader.sizeStore]
    · simp [SizeReader.sizeStore,TapeStore.setReg,h,hz]
  obtain ⟨t,z,ht,hsetup,hstore,hbound⟩ := setup_stops r hr d k hk inp (n+1) (by omega)
    (SizeReader.sizeStore (r 0) n σ) hb
    (by simp [SizeReader.sizeStore]; omega) (by simpa [SizeReader.sizeStore] using hnk)
  have hall := hread.seq hsetup
  refine ⟨_,_,?_,hall,hstore,?_⟩
  · have htime : σ.reg (r 0)+2*n+3+1+t≤2*n+4+setupTimeBound d (n+1) := by
      rw [hz]
      omega
    exact htime.trans (hpoly n)
  · rw [hstore]
    exact setupStore_payload r hr d k _

#print axioms setupStore_values
#print axioms setup_stops
#print axioms setup_uniform_polynomial
#print axioms setupInput_unary
end ParameterPrograms
end ExpandingCodes.Computation
