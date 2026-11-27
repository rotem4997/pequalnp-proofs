import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Count every pair already witnessed by a sound internal wire of line-degree at most two.
-- The remaining pairs have no such witness anywhere in the circuit.
theorem PEqualNP.Outside.R_meta_3051_482
    (paid : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → Fintype.card { e2 : Fin N × Fin N // I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true} ≤ 48 * (Ckt.size + Jn) + 2 * N)
    (residual : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      let sound := fun j : Fin C.size => ∀ x : Fin (N+N) → Bool,
        gateVal (N+N) C j.val x = true → ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
      let low := fun j : Fin C.size => (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD (N+N+j.val) 0 ≤ 2
      let pair := fun e : Fin N × Fin N => pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)
      300 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      Monotone2 C →
      (∀ p l, I p l → circuitFun (N+N) C (pair (p,l)) = true) →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) → circuitFun (N+N) C x = false) →
      3*C.size < Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        ¬∃ j : Fin C.size, low j ∧ sound j ∧ gateVal (N+N) C j.val (pair e) = true} →
      N*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C many order degree join mono accepts rejects
  let pair (e : Fin N × Fin N) := pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)
  let low (j : Fin C.size) := (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD (N+N+j.val) 0 ≤ 2
  let sound (j : Fin C.size) := ∀ x : Fin (N+N) → Bool,
    gateVal (N+N) C j.val x = true → ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
  let A := Finset.univ.filter fun j : Fin C.size => low j ∧ sound j
  let covered (e : Fin N × Fin N) := ∃ j : Fin C.size, low j ∧ sound j ∧ gateVal (N+N) C j.val (pair e) = true
  let E := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2
  let L := E.filter covered
  let H := E.filter fun e => ¬ covered e
  by_cases rare : H.card ≤ 3*C.size
  · let enum : Fin A.card ≃ ↥A := (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm
    have condition (i : Fin A.card) : low (enum i).val ∧ sound (enum i).val :=
      (Finset.mem_filter.mp (enum i).property).2
    have square : ∀ p r a b : Fin N, p ≠ r → a ≠ b → ¬(I p a ∧ I p b ∧ I r a ∧ I r b) := by
      rintro p r a b pr ab ⟨pa,pb,ra,rb⟩
      exact ab ((join p r pr).unique ⟨pa,ra⟩ ⟨pb,rb⟩)
    have count := paid N A.card I C (fun i => N+N+(enum i).val.val) square mono
      (fun i => (condition i).1) (fun i => (condition i).2)
    rw [Fintype.card_subtype] at count
    have lower : L.card ≤ 48*(C.size+A.card)+2*N := by
      apply le_trans (Finset.card_le_card ?_) count
      intro e he
      obtain ⟨edge,hit⟩ := Finset.mem_filter.mp he
      obtain ⟨j,jlow,jsound,jhit⟩ := hit
      let a : ↥A := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,jlow,jsound⟩⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp edge).2,enum.symm a,?_⟩
      rw [enum.apply_symm_apply]
      have same : (fun z : Fin (N+N) => if z = Fin.castAdd N e.1 then true else if z = Fin.natAdd N e.2 then true else false) = pair e := by
        funext z
        change _ = decide (z = Fin.castAdd N e.1 ∨ z = Fin.natAdd N e.2)
        by_cases hp : z=Fin.castAdd N e.1 <;> by_cases hl : z=Fin.natAdd N e.2 <;> simp [hp, hl]
      rw [same]
      change gateVal (N+N) C j.val (pair e) = true
      exact jhit
    let flags : {e : Fin N × Fin N // I e.1 e.2} ≃ (Σ l : Fin N, {p : Fin N // I p l}) :=
      { toFun := fun e => ⟨e.val.2, e.val.1, e.property⟩
        invFun := fun a => ⟨⟨a.2.val, a.1⟩, a.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have total : E.card = N*(q+1) := by
      calc
        _ = Fintype.card {e : Fin N × Fin N // I e.1 e.2} := (Fintype.card_subtype _).symm
        _ = _ := Fintype.card_congr flags
        _ = _ := by simp [Fintype.card_sigma, degree]
    have split : L.card + H.card = E.card := Finset.card_filter_add_card_filter_not _
    have budget : A.card ≤ C.size := by simpa using Finset.card_le_univ A
    have scale : 300*N ≤ N*q := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left N many
    rw [total, Nat.mul_add, Nat.mul_one] at split
    omega
  · apply residual q N I C many order degree join mono accepts rejects
    have equal : H = Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ ¬ covered e) := by
      ext e
      simp only [H, E, Finset.mem_filter, Finset.mem_univ, true_and]
    change 3*C.size < Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ ¬covered e}
    rw [Fintype.card_subtype, ← equal]
    omega
