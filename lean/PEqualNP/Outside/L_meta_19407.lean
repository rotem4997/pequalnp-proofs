import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19407_aux

open PEqualNP.AndCount

private theorem synthesize {n s : ℕ}
    (negative : Finset (Finset (Fin n)))
    (bare : Fin s → Finset (Fin n))
    (bad : Fin s → Fin 2 → Finset (Finset (Fin n)))
    (good : Fin s → Finset (Finset (Fin n)))
    (coverage : ∀ j, ∀ P ∈ good j, ∀ b,
      (∃ v ∈ bare j, v ∈ P ∧ ∀ S ∈ bad j b, v ∉ S) ∨
        ∃ k < j, P ∈ good k ∧ bad j b ⊆ bad k 0 ∪ bad k 1) :
    ∃ C : AndCountCircuit n, C.WellFormed ∧ C.size = s ∧
      (∀ v : Fin n, (Finset.univ.filter
        (fun j => v ∈ C.leftVars j ∨ v ∈ C.rightVars j)).card ≤
          (Finset.univ.filter (fun j => v ∈ bare j)).card) ∧
      (∀ S ∈ negative, C.eval S = false) ∧
      ∀ j, negative ⊆ bad j 0 ∪ bad j 1 →
        ∀ P ∈ good j, ∀ S : Finset (Fin n), P ⊆ S → C.eval S = true := by
  classical
  let B (j : Fin s) := bad j 0 ∪ bad j 1
  let vars (j : Fin s) (b : Fin 2) :=
    (bare j).filter (fun v => ∀ S ∈ bad j b, v ∉ S)
  let refs (j : Fin s) (b : Fin 2) :=
    Finset.univ.filter (fun k : Fin s => k < j ∧ bad j b ⊆ B k)
  let outputs := Finset.univ.filter (fun j : Fin s => negative ⊆ B j)
  let C : AndCountCircuit n :=
    { size := s
      leftVars := fun j => vars j 0
      leftGates := fun j => refs j 0
      rightVars := fun j => vars j 1
      rightGates := fun j => refs j 1
      outVars := ∅
      outGates := outputs }
  have ref_properties {j k : Fin s} {b : Fin 2} (hk : k ∈ refs j b) :
      k < j ∧ bad j b ⊆ B k :=
    (Finset.mem_filter.mp hk).2

  have gate_spec (S : Finset (Fin n)) (fuel : ℕ) :
      ∀ j : Fin s, j.val < fuel →
        (S ∈ B j → C.gateValFuel S fuel j = false) ∧
        (∀ P ∈ good j, P ⊆ S → C.gateValFuel S fuel j = true) := by
    induction fuel with
    | zero =>
        intro j hj
        exact (Nat.not_lt_zero _ hj).elim
    | succ fuel ih =>
        intro j hj
        let side (b : Fin 2) :=
          AndCountCircuit.sideTrue S (vars j b) (refs j b) j (C.gateValFuel S fuel)
        have earlier {k : Fin s} (hk : k < j) : k.val < fuel :=
          Nat.lt_of_lt_of_le (Fin.lt_def.mp hk) (Nat.le_of_lt_succ hj)
        have side_false (b : Fin 2) (hS : S ∈ bad j b) : side b = false := by
          change decide _ = false
          rw [decide_eq_false_iff_not]
          rintro (⟨v, hv, hvS⟩ | ⟨k, hk, hkj, htrue⟩)
          · exact (Finset.mem_filter.mp hv).2 S hS hvS
          · have hfalse := (ih k (earlier hkj)).1 ((ref_properties hk).2 hS)
            simp [hfalse] at htrue
        have side_true (b : Fin 2) (P : Finset (Fin n))
            (hP : P ∈ good j) (hPS : P ⊆ S) : side b = true := by
          change decide _ = true
          rw [decide_eq_true_eq]
          rcases coverage j P hP b with ⟨v, hv, hvP, hvBad⟩ | ⟨k, hkj, hkP, hkBad⟩
          · exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hvBad⟩, hPS hvP⟩
          · exact Or.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj, hkBad⟩,
              hkj, (ih k (earlier hkj)).2 P hkP hPS⟩
        constructor
        · intro hS
          change (side 0 && side 1) = false
          rcases Finset.mem_union.mp hS with hS | hS
          · simp [side_false 0 hS]
          · simp [side_false 1 hS]
        · intro P hP hPS
          change (side 0 && side 1) = true
          simp [side_true 0 P hP hPS, side_true 1 P hP hPS]
  refine ⟨C, ?_, rfl, ?_, ?_, ?_⟩
  · intro j
    exact ⟨fun k hk => (ref_properties hk).1, fun k hk => (ref_properties hk).1⟩
  · intro v
    apply Finset.card_le_card
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change j ∈ Finset.univ.filter (fun j => v ∈ vars j 0 ∨ v ∈ vars j 1) at hj
    rcases (Finset.mem_filter.mp hj).2 with hv | hv
    · exact (Finset.mem_filter.mp hv).1
    · exact (Finset.mem_filter.mp hv).1
  · intro S hS
    unfold AndCountCircuit.eval
    rw [decide_eq_false_iff_not]
    rintro (⟨v, hv, _⟩ | ⟨j, hj, htrue⟩)
    · change v ∈ (∅ : Finset (Fin n)) at hv
      simp at hv
    · have hSj : S ∈ B j := (Finset.mem_filter.mp hj).2 hS
      have hfalse : C.gateVal S j = false := (gate_spec S s j j.isLt).1 hSj
      simp [hfalse] at htrue
  · intro j hj P hP S hPS
    unfold AndCountCircuit.eval
    rw [decide_eq_true_eq]
    exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩,
      (gate_spec S s j j.isLt).2 P hP hPS⟩

end PEqualNP.Outside.L_meta_19407_aux

theorem PEqualNP.Outside.L_meta_19407 : (∀ (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1))) (x4 : Fin x2 → Finset (Fin x1)) (x5 : Fin x2 → Fin (2 : ℕ) → Finset (Finset (Fin x1))) (x6 : Fin x2 → Finset (Finset (Fin x1))),   x1 < (50 : ℕ) →     have x8 : Finset (Fin x2) := Finset.univ;     have x9 : Fin x2 → Finset (Finset (Fin x1)) := fun (x9 : Fin x2) => x5 x9 (0 : Fin (2 : ℕ)) ∪ x5 x9 (1 : Fin (2 : ℕ));     (∀ (x10 : Fin x2), ∀ x11 ∈ x6 x10, ∀ (x13 : Fin (2 : ℕ)), (∃ x14 ∈ x4 x10, x14 ∈ x11 ∧ ∀ x15 ∈ x5 x10 x13, x14 ∉ x15) ∨ ∃ x14 < x10, x11 ∈ x6 x14 ∧ x5 x10 x13 ⊆ x9 x14) →       ∃ (x11 : PEqualNP.AndCount.AndCountCircuit x1),         x11.WellFormed ∧           x11.size = x2 ∧             (have x12 : Finset (Fin x11.size) := Finset.univ;               ∀ (x13 : Fin x1), {x14 ∈ x12 | x13 ∈ x11.leftVars x14 ∨ x13 ∈ x11.rightVars x14}.card ≤ {x14 ∈ x8 | x13 ∈ x4 x14}.card) ∧               (∀ x12 ∈ x3, x11.eval x12 = Bool.false) ∧ ∀ (x12 : Fin x2), x3 ⊆ x9 x12 → ∀ x14 ∈ x6 x12, ∀ (x16 : Finset (Fin x1)), x14 ⊆ x16 → x11.eval x16 = Bool.true) := by
  intro n s negative bare bad good _
  exact PEqualNP.Outside.L_meta_19407_aux.synthesize negative bare bad good
