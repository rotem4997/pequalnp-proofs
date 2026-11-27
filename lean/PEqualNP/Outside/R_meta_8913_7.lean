import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8913_7
    (ands : (let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9;
      ∀ (n : ℕ) (X Y : Fin n → Finset (Fin 13)),
        (∀ p l : Fin 13, I p l → ∃ i, X i = {p} ∧ Y i = {l}) →
        (∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬I p l) → (∀ l : Fin 13, {p ∈ P | I p l}.card ≤ 2) →
          (∀ p : Fin 13, {l ∈ Q | I p l}.card ≤ 2) → ∃ i, X i = P ∧ Y i = Q) →
        have B : Set (Set (Fin n)) := {∅, Set.univ} ∪ Set.range fun v : Fin (13 + 13) =>
          {i : Fin n | Fin.addCases (fun p : Fin 13 => decide (p ∈ X i)) (fun l : Fin 13 => decide (l ∈ Y i)) v = true};
        ∀ s : List (Set (Fin n)), s.length ≤ 63 →
          (∀ k : Fin s.length, s.getD k ∅ ∉ B ∪ {t | t ∈ s.take k} ∧
            ∃ a ∈ B ∪ {t | t ∈ s.take k}, ∃ b ∈ B ∪ {t | t ∈ s.take k}, s.getD k ∅ = a ∪ b ∨ s.getD k ∅ = a ∩ b) →
          {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} ∈ B ∪ {t | t ∈ s} →
          13 ≤ {k : Fin s.length | ¬∃ a ∈ B ∪ {t | t ∈ s.take k}, ∃ b ∈ B ∪ {t | t ∈ s.take k}, s.getD k ∅ = a ∪ b}.ncard))
    (ors : (let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9;
      ∀ (n : ℕ) (X Y : Fin n → Finset (Fin 13)),
        (∀ p l : Fin 13, I p l → ∃ i, X i = {p} ∧ Y i = {l}) →
        (∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬I p l) → (∀ l : Fin 13, {p ∈ P | I p l}.card ≤ 2) →
          (∀ p : Fin 13, {l ∈ Q | I p l}.card ≤ 2) → ∃ i, X i = P ∧ Y i = Q) →
        have B : Set (Set (Fin n)) := {∅, Set.univ} ∪ Set.range fun v : Fin (13 + 13) =>
          {i : Fin n | Fin.addCases (fun p : Fin 13 => decide (p ∈ X i)) (fun l : Fin 13 => decide (l ∈ Y i)) v = true};
        ∀ s : List (Set (Fin n)), s.length ≤ 63 →
          (∀ k : Fin s.length, s.getD k ∅ ∉ B ∪ {t | t ∈ s.take k} ∧
            ∃ a ∈ B ∪ {t | t ∈ s.take k}, ∃ b ∈ B ∪ {t | t ∈ s.take k}, s.getD k ∅ = a ∪ b ∨ s.getD k ∅ = a ∩ b) →
          {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} ∈ B ∪ {t | t ∈ s} →
          51 ≤ {k : Fin s.length | ¬∃ a ∈ B ∪ {t | t ∈ s.take k}, ∃ b ∈ B ∪ {t | t ∈ s.take k}, s.getD k ∅ = a ∩ b}.ncard)) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∃ (x2 : ℕ) (x3 : Fin x2 → Finset (Fin (13 : ℕ))) (x4 : Fin x2 → Finset (Fin (13 : ℕ))) (x5 : Set (Fin x2)),   (∀ x6 ∈ x5, ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x3 x6 = {x8} ∧ x4 x6 = {x9}) ∧     (∀ x6 ∉ x5, (∀ x8 ∈ x3 x6, ∀ x10 ∈ x4 x6, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x3 x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x4 x6 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧       have x6 : Fin x2 → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x6 : Fin x2) (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x3 x6)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x4 x6)) x7;       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | x6 x8 x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))),         x8.length ≤ (63 : ℕ) →           (∀ (x10 : Fin x8.length),               have x11 : Set (Set (Fin x2)) := x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8};               x8.getD ↑x10 ∅ ∉ x11 ∧ ∃ x12 ∈ x11, ∃ x13 ∈ x11, x8.getD ↑x10 ∅ = x12 ∪ x13 ∨ x8.getD ↑x10 ∅ = x12 ∩ x13) →             x5 ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ x8}) := by
  classical
  intro x1
  obtain ⟨m, X, Y, hcls, hpos, hneg⟩ : ∃ (m : ℕ) (X Y : Fin m → Finset (Fin 13)),
      (∀ i, (∃ p l, x1 p l ∧ X i = {p} ∧ Y i = {l}) ∨
        ((∀ p ∈ X i, ∀ l ∈ Y i, ¬x1 p l) ∧ (∀ l : Fin 13, {p ∈ X i | x1 p l}.card ≤ 2) ∧
          ∀ p : Fin 13, {l ∈ Y i | x1 p l}.card ≤ 2)) ∧
      (∀ p l : Fin 13, x1 p l → ∃ i, X i = {p} ∧ Y i = {l}) ∧
      (∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬x1 p l) → (∀ l : Fin 13, {p ∈ P | x1 p l}.card ≤ 2) →
        (∀ p : Fin 13, {l ∈ Q | x1 p l}.card ≤ 2) → ∃ i, X i = P ∧ Y i = Q) := by
    let e := Fintype.equivFin {t : Finset (Fin 13) × Finset (Fin 13) //
      (∃ p l, x1 p l ∧ t.1 = {p} ∧ t.2 = {l}) ∨
        ((∀ p ∈ t.1, ∀ l ∈ t.2, ¬x1 p l) ∧ (∀ l : Fin 13, {p ∈ t.1 | x1 p l}.card ≤ 2) ∧
          ∀ p : Fin 13, {l ∈ t.2 | x1 p l}.card ≤ 2)}
    refine ⟨_, fun i => (e.symm i).1.1, fun i => (e.symm i).1.2, fun i => (e.symm i).2, ?_, ?_⟩
    · intro p l h
      exact ⟨e ⟨({p}, {l}), Or.inl ⟨p, l, h, rfl, rfl⟩⟩, by simp⟩
    · intro P Q h1 h2 h3
      exact ⟨e ⟨(P, Q), Or.inr ⟨h1, h2, h3⟩⟩, by simp⟩
  refine ⟨m, X, Y, {i | ∃ p l, x1 p l ∧ X i = {p} ∧ Y i = {l}}, ?_, ?_, ?_⟩
  · intro i hi
    exact hi
  · intro i hi
    rcases hcls i with h | h
    · exact absurd h hi
    · exact h
  · intro x6 x7 s hlen hval hmem
    have hA := ands m X Y hpos hneg s hlen hval hmem
    have hB := ors m X Y hpos hneg s hlen hval hmem
    have key : ∀ (A B : Set (Fin s.length)), (∀ k, k ∈ A → k ∈ B → False) →
        A.ncard + B.ncard ≤ s.length := by
      intro A B h
      have hd : Disjoint A B := Set.disjoint_left.mpr h
      have h1 := Set.ncard_union_eq hd
      have h2 := (Set.ncard_le_ncard (Set.subset_univ (A ∪ B)) Set.finite_univ).trans_eq
        (Set.ncard_univ (Fin s.length))
      rw [Nat.card_fin] at h2
      omega
    refine absurd (le_trans (Nat.add_le_add hA hB) (key _ _ ?_)) (by omega)
    intro k hkA hkB
    obtain ⟨-, a, ha, b, hb, h | h⟩ := hval k
    · exact hkA ⟨a, ha, b, hb, h⟩
    · exact hkB ⟨a, ha, b, hb, h⟩
