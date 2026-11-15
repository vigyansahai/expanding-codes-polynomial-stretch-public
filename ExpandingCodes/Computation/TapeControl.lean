import ExpandingCodes.Computation.TapeLoops

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace TapeProgram
variable {R B L K : ℕ}

def branchLeft (K : ℕ) (i : Fin L) : Fin (L+K+2) := leftLabel 2 (leftLabel K i)
def branchRight (L : ℕ) (i : Fin K) : Fin (L+K+2) := leftLabel 2 (rightLabel L i)
def branchTest (L K : ℕ) : Fin (L+K+2) := rightLabel (L+K) (0 : Fin 2)
def branchRestore (L K : ℕ) : Fin (L+K+2) := rightLabel (L+K) (1 : Fin 2)

/-- A physical zero test followed by one of two finite programs. A positive
counter is restored by an actual increment before entering its branch. -/
def branchZero (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    TapeProgram R B (L+K+2) where
  entry := branchTest L K
  code j := match finSumFinEquiv.symm j with
    | .inl p => match finSumFinEquiv.symm p with
      | .inl i => (P.code i).relabel (branchLeft K)
      | .inr i => (Q.code i).relabel (branchRight L)
    | .inr c => if c = 0 then
        .dec r (branchLeft K P.entry) (branchRestore L K)
      else .inc r (branchRight L Q.entry)

theorem branchZero_left (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (i : Fin L) : (branchZero r P Q).code (branchLeft K i) =
      (P.code i).relabel (branchLeft K) := by
  simp [branchZero, branchLeft, leftLabel]

theorem branchZero_right (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (i : Fin K) : (branchZero r P Q).code (branchRight L i) =
      (Q.code i).relabel (branchRight L) := by
  simp [branchZero, branchRight, leftLabel, rightLabel]

theorem branchZero_test (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    (branchZero r P Q).code (branchTest L K) =
      .dec r (branchLeft K P.entry) (branchRestore L K) := by
  simp [branchZero, branchTest, rightLabel]

theorem branchZero_restore (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    (branchZero r P Q).code (branchRestore L K) = .inc r (branchRight L Q.entry) := by
  simp [branchZero, branchRestore, rightLabel]

theorem branchZero_stops_zero (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg r = 0)
    {t : ℕ} {e : TapeCfg R B L} (hp : P.Stops inp (d.toCfg P.entry) t e) :
    (branchZero r P Q).Stops inp (d.toCfg (branchTest L K)) (1+t)
      (e.mapPC (branchLeft K)) := by
  have ht : (branchZero r P Q).Exec inp (d.toCfg (branchTest L K)) 1
      ((d.toCfg P.entry).mapPC (branchLeft K)) := by
    apply Exec.one
    · rw [halted, branchZero_test]
      simp
    · simp [step, branchZero_test, TapeStore.toCfg, TapeCfg.mapPC, hr]
  refine ⟨ht.trans (hp.exec.relabel (branchLeft K) (fun i _ => branchZero_left r P Q i)), ?_⟩
  change (branchZero r P Q).code (branchLeft K e.pc) = .halt
  rw [branchZero_left, hp.halted]
  rfl

theorem branchZero_stops_positive (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg r ≠ 0)
    {t : ℕ} {e : TapeCfg R B K} (hq : Q.Stops inp (d.toCfg Q.entry) t e) :
    (branchZero r P Q).Stops inp (d.toCfg (branchTest L K)) (2+t)
      (e.mapPC (branchRight L)) := by
  let c := decStore r d
  have hs₁ : (branchZero r P Q).step inp (d.toCfg (branchTest L K)) =
      c.toCfg (branchRestore L K) := by
    simp [step, branchZero_test, TapeStore.toCfg, c, decStore, hr]
  have hs₂ : (branchZero r P Q).step inp (c.toCfg (branchRestore L K)) =
      (d.toCfg Q.entry).mapPC (branchRight L) := by
    have hr₁ : d.reg r-1+1 = d.reg r := Nat.sub_add_cancel (Nat.pos_of_ne_zero hr)
    simp [step, branchZero_restore, TapeStore.toCfg, TapeCfg.mapPC, c, decStore,
      Function.update_idem, hr₁, Function.update_eq_self]
  have ht : (branchZero r P Q).Exec inp (d.toCfg (branchTest L K)) 2
      ((d.toCfg Q.entry).mapPC (branchRight L)) := by
    exact Exec.step (by rw [halted, branchZero_test]; simp) hs₁
      (Exec.one (by rw [halted, branchZero_restore]; simp) hs₂)
  refine ⟨ht.trans (hq.exec.relabel (branchRight L) (fun i _ => branchZero_right r P Q i)), ?_⟩
  change (branchZero r P Q).code (branchRight L e.pc) = .halt
  rw [branchZero_right, hq.halted]
  rfl

/-- A compositional bounded contract for the real branch transition table. -/
theorem branchZero_stops (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (inp : Inputs) (d f g : TapeStore R B) (A C : ℕ)
    (hp : ∃ t e, t ≤ A ∧ P.Stops inp (d.toCfg P.entry) t e ∧ e.store = f)
    (hq : ∃ t e, t ≤ C ∧ Q.Stops inp (d.toCfg Q.entry) t e ∧ e.store = g) :
    ∃ t e, t ≤ max A C + 2 ∧
      (branchZero r P Q).Stops inp (d.toCfg (branchZero r P Q).entry) t e ∧
      e.store = if d.reg r = 0 then f else g := by
  by_cases hr : d.reg r = 0
  · obtain ⟨t,e,ht,he,hes⟩ := hp
    refine ⟨1+t,e.mapPC (branchLeft K), ?_, branchZero_stops_zero r P Q inp d hr he, ?_⟩
    · have := le_max_left A C
      omega
    · simpa [hr] using hes
  · obtain ⟨t,e,ht,he,hes⟩ := hq
    refine ⟨2+t,e.mapPC (branchRight L), ?_, branchZero_stops_positive r P Q inp d hr he, ?_⟩
    · have := le_max_right A C
      omega
    · simpa [hr] using hes

def skip : TapeProgram R B 1 where
  entry := 0
  code _ := .halt

theorem skip_stops (inp : Inputs) (d : TapeStore R B) :
    skip.Stops inp (d.toCfg (0 : Fin 1)) 0 (d.toCfg 0) :=
  ⟨Exec.refl _, rfl⟩

#print axioms branchZero_stops_zero
#print axioms branchZero_stops_positive
#print axioms branchZero_stops
end TapeProgram
end ExpandingCodes.Computation
