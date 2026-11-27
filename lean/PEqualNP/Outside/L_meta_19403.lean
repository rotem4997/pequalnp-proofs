import PEqualNP.Defs

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit in
theorem PEqualNP.Outside.L_meta_19403 : ∀ (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1))) (x4 : Fin x2 → Finset (Fin x1)) (x5 : Fin x2 → Fin (2 : ℕ) → Finset (Finset (Fin x1))) (x6 : Fin x2 → Finset (Finset (Fin x1))),   have x7 : Finset (Fin x2) := Finset.univ;   have x8 : Fin x2 → Finset (Finset (Fin x1)) := fun (x8 : Fin x2) => x5 x8 (0 : Fin (2 : ℕ)) ∪ x5 x8 (1 : Fin (2 : ℕ));   (∀ (x9 : Fin x2), ∀ x10 ∈ x6 x9, ∀ (x12 : Fin (2 : ℕ)), (∃ x13 ∈ x4 x9, x13 ∈ x10 ∧ ∀ x14 ∈ x5 x9 x12, x13 ∉ x14) ∨ ∃ x13 < x9, x10 ∈ x6 x13 ∧ x5 x9 x12 ⊆ x8 x13) →     ∃ (x10 : PEqualNP.AndCount.AndCountCircuit x1),       x10.WellFormed ∧         x10.size = x2 ∧           (have x11 : Finset (Fin x10.size) := Finset.univ;             ∀ (x12 : Fin x1), {x13 ∈ x11 | x12 ∈ x10.leftVars x13 ∨ x12 ∈ x10.rightVars x13}.card ≤ {x13 ∈ x7 | x12 ∈ x4 x13}.card) ∧             (∀ x11 ∈ x3, x10.eval x11 = Bool.false) ∧ ∀ (x11 : Fin x2), x3 ⊆ x8 x11 → ∀ x13 ∈ x6 x11, ∀ (x15 : Finset (Fin x1)), x13 ⊆ x15 → x10.eval x15 = Bool.true := by
  classical
  intro n k neg allowed sides pos

  dsimp only
  intro feasible
  let both (i : Fin k) := sides i 0 ∪ sides i 1
  let bare (i : Fin k) (b : Fin 2) := (allowed i).filter
    (fun v => ∀ N ∈ sides i b, v ∉ N)
  let prior (i : Fin k) (b : Fin 2) := Finset.univ.filter
    (fun j => j < i ∧ sides i b ⊆ both j)
  let outputs := Finset.univ.filter (fun i => neg ⊆ both i)
  let C : AndCountCircuit n := ⟨k,fun i => bare i 0,fun i => prior i 0,
    fun i => bare i 1,fun i => prior i 1,∅,outputs⟩
  have off : ∀ d (i : Fin k) (N : Finset (Fin n)), N ∈ both i →
      C.gateValFuel N d i = false := by
    intro d
    induction d with
    | zero => intro i N _; rfl
    | succ d ih =>
      intro i N mem
      have sideOff (b : Fin 2) (hb : N ∈ sides i b) :
          sideTrue N (bare i b) (prior i b) i (C.gateValFuel N d) = false := by
        apply decide_eq_false
        rintro (⟨v,hv,hit⟩ | ⟨j,hj,_,hit⟩)
        · exact (Finset.mem_filter.mp hv).2 N hb hit
        · have hsub : sides i b ⊆ both j := (Finset.mem_filter.mp hj).2.2
          have z := ih j N (hsub hb)
          rw [z] at hit
          contradiction
      change (sideTrue N (bare i 0) (prior i 0) i (C.gateValFuel N d) &&
        sideTrue N (bare i 1) (prior i 1) i (C.gateValFuel N d)) = false
      rcases Finset.mem_union.mp mem with h | h
      · simp [sideOff 0 h]
      · simp [sideOff 1 h]
  have on : ∀ d (i : Fin k) (P X : Finset (Fin n)), i.val < d →
      P ∈ pos i → P ⊆ X → C.gateValFuel X d i = true := by
    intro d
    induction d with
    | zero => intro i P X h; omega
    | succ d ih =>
      intro i P X hd hP hPX
      have sideOn (b : Fin 2) :
          sideTrue X (bare i b) (prior i b) i (C.gateValFuel X d) = true := by
        apply decide_eq_true
        rcases feasible i P hP b with ⟨v,hv,hvp,hAvoid⟩ | ⟨j,hji,hp,hSub⟩
        · exact Or.inl ⟨v,Finset.mem_filter.mpr ⟨hv,hAvoid⟩,hPX hvp⟩
        · have hjlt : j.val < i.val := hji
          exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji,hSub⟩,
            hji,ih j P X (by omega) hp hPX⟩
      change (sideTrue X (bare i 0) (prior i 0) i (C.gateValFuel X d) &&
        sideTrue X (bare i 1) (prior i 1) i (C.gateValFuel X d)) = true
      simp only [sideOn, Bool.true_and]
  refine ⟨C, ?_,rfl,?_,?_,?_⟩
  · intro i
    exact ⟨fun j h => (Finset.mem_filter.mp h).2.1,fun j h => (Finset.mem_filter.mp h).2.1⟩
  · intro v
    apply Finset.card_le_card
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases (Finset.mem_filter.mp hi).2 with h | h <;> exact (Finset.mem_filter.mp h).1
  · intro N hN
    apply decide_eq_false
    rintro (⟨v,hv,_⟩ | ⟨j,hj,hit⟩)
    · exact Finset.notMem_empty _ hv
    · have hsub : neg ⊆ both j := (Finset.mem_filter.mp hj).2
      have z := off k j N (hsub hN)
      change C.gateValFuel N k j = true at hit
      rw [z] at hit
      contradiction
  · intro i hsub P hp X hX
    apply decide_eq_true
    exact Or.inr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub⟩,on k i P X i.isLt hp hX⟩
