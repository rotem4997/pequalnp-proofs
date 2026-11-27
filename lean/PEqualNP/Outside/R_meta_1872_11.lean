import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1872_11
    (h1 : let P : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
    let X := fun (T L : Finset (Fin 13)) =>
      (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
    let W := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
    let G := PEqualNP.MetaComplexity.NestedCover.gateAt
    let A := PEqualNP.CircuitLowerBounds.GateOp.and
    let aa := fun (C : Circuit) (j : ℕ) => (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C → a < 26 + C.size →
      b < 26 + C.size → (∀ p l : Fin 13, p ∈ P l → (W C a (X {p} {l}) = true ∨ W C b (X {p} {l}) = true)) →
      (∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle P S → (W C a (X S (PEqualNP.HeptadCover.missLines P S)) = false ∧ W C b (X S (PEqualNP.HeptadCover.missLines P S)) = false)) → (∃ p l : Fin 13, p ∈ P l ∧ W C a (X {p} {l}) = true ∧ W C b (X {p} {l}) = false) → (∃ p l : Fin 13, p ∈ P l ∧ W C b (X {p} {l}) = true ∧ W C a (X {p} {l}) = false) → (∀ j ∈ Finset.range C.size, ∀ j' ∈ Finset.range C.size, aa C j → aa C j' → j = j') → 63 ≤ C.size)
    (h2 : let P : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
    let X := fun (T L : Finset (Fin 13)) =>
      (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
    let W := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
    let G := PEqualNP.MetaComplexity.NestedCover.gateAt
    let A := PEqualNP.CircuitLowerBounds.GateOp.and
    let aa := fun (C : Circuit) (j : ℕ) => (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C → a < 26 + C.size →
      b < 26 + C.size → (∀ p l : Fin 13, p ∈ P l → (W C a (X {p} {l}) = true ∨ W C b (X {p} {l}) = true)) →
      (∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle P S → (W C a (X S (PEqualNP.HeptadCover.missLines P S)) = false ∧ W C b (X S (PEqualNP.HeptadCover.missLines P S)) = false)) → (∃ p l : Fin 13, p ∈ P l ∧ W C a (X {p} {l}) = true ∧ W C b (X {p} {l}) = false) → (∃ p l : Fin 13, p ∈ P l ∧ W C b (X {p} {l}) = true ∧ W C a (X {p} {l}) = false) → (∃ j ∈ Finset.range C.size, ∃ j' ∈ Finset.range C.size, j ≠ j' ∧ aa C j ∧ aa C j' ∧ ∀ k ∈ Finset.range C.size, aa C k → k = j ∨ k = j') → 63 ≤ C.size)
    (h3 : let P : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
    let X := fun (T L : Finset (Fin 13)) =>
      (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
    let W := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
    let G := PEqualNP.MetaComplexity.NestedCover.gateAt
    let A := PEqualNP.CircuitLowerBounds.GateOp.and
    let aa := fun (C : Circuit) (j : ℕ) => (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C → a < 26 + C.size →
      b < 26 + C.size → (∀ p l : Fin 13, p ∈ P l → (W C a (X {p} {l}) = true ∨ W C b (X {p} {l}) = true)) →
      (∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle P S → (W C a (X S (PEqualNP.HeptadCover.missLines P S)) = false ∧ W C b (X S (PEqualNP.HeptadCover.missLines P S)) = false)) → (∃ p l : Fin 13, p ∈ P l ∧ W C a (X {p} {l}) = true ∧ W C b (X {p} {l}) = false) → (∃ p l : Fin 13, p ∈ P l ∧ W C b (X {p} {l}) = true ∧ W C a (X {p} {l}) = false) → (∃ j ∈ Finset.range C.size, ∃ j' ∈ Finset.range C.size, ∃ k ∈ Finset.range C.size, j ≠ j' ∧ j ≠ k ∧ j' ≠ k ∧ aa C j ∧ aa C j' ∧ aa C k) → 63 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro x1 x2 x3 hm hr ha hb x8 x9 x10 x11 x12 hpos hneg hea heb
  have mem_inc : ∀ q l : Fin 13, q ∈ PEqualNP.HeptadCover.singerLines3 l ↔ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    intro q l
    delta PEqualNP.HeptadCover.singerLines3
    simp [← Fin.val_eq_val, Fin.val_sub]
    constructor <;> intro h <;> rcases h with (h | h | h | h) <;> omega
  have card_inc : ∀ (S : Finset (Fin 13)) (c : Fin 13),
      (S ∩ PEqualNP.HeptadCover.singerLines3 c).card = {q ∈ S | q - c ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card := by
    intro S c
    congr 1
    ext q
    simp [mem_inc]
  have hI : ∀ p l : Fin 13, ((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))) = ((List.ofFn fun q : Fin 13 => decide (q = p)) ++ (List.ofFn fun q : Fin 13 => decide (q = l))) := by
    intro p l
    simp
  have hM : ∀ S : Finset (Fin 13),
      ((List.ofFn fun q : Fin 13 => decide (q ∈ (S))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 S)))) = ((List.ofFn fun q : Fin 13 => decide (q ∈ S)) ++
        (List.ofFn fun l : Fin 13 => decide ((∀ q ∈ S, q - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)))))) := by
    intro S
    delta PEqualNP.HeptadCover.missLines
    simp [Finset.disjoint_right, mem_inc]
  have hQ : ∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 S ↔
      (S.card = 4 ∧ ∀ c : Fin 13, {q ∈ S | q - c ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card ≤ 2) := by
    intro S
    constructor
    · intro h
      obtain ⟨h1, h2⟩ : S.card = 4 ∧ ∀ l : Fin 13, (S ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2 := h
      exact ⟨h1, fun c => by rw [← card_inc]; exact h2 c⟩
    · rintro ⟨h1, h2⟩
      show S.card = 4 ∧ ∀ l : Fin 13, (S ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2
      exact ⟨h1, fun c => by rw [card_inc]; exact h2 c⟩
  have hacc : ∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l → (((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))))).getD (x2) false = true ∨ ((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))))).getD (x3) false = true) := by
    intro p l hp
    rw [hI]
    exact hpos p l ((mem_inc p l).mp hp)
  have hrej : ∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 S → (((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (S))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 S)))))).getD (x2) false = false ∧ ((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (S))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 S)))))).getD (x3) false = false) := by
    intro S hS
    rw [hQ] at hS
    rw [hM]
    exact hneg S hS
  have he1 : ∃ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ ((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))))).getD (x2) false = true ∧ ((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))))).getD (x3) false = false := by
    obtain ⟨p, l, hp, h1, h2⟩ := hea
    refine ⟨p, l, (mem_inc p l).mpr hp, ?_, ?_⟩
    · rw [hI]
      exact h1
    · rw [hI]
      exact h2
  have he2 : ∃ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ ((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))))).getD (x3) false = true ∧ ((x1).wires (((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))))).getD (x2) false = false := by
    obtain ⟨p, l, hp, h1, h2⟩ := heb
    refine ⟨p, l, (mem_inc p l).mpr hp, ?_, ?_⟩
    · rw [hI]
      exact h1
    · rw [hI]
      exact h2
  by_cases hatmost : ∀ j ∈ Finset.range x1.size, ∀ j' ∈ Finset.range x1.size, ((gateAt x1 j).op = GateOp.and ∧ ∃ i ∈ (gateAt x1 j).inputs, 26 ≤ i ∧ (gateAt x1 (i - 26)).op = GateOp.and) → ((gateAt x1 j').op = GateOp.and ∧ ∃ i ∈ (gateAt x1 j').inputs, 26 ≤ i ∧ (gateAt x1 (i - 26)).op = GateOp.and) → j = j'
  · exact h1 x1 x2 x3 hm hr ha hb hacc hrej he1 he2 hatmost
  · have hex : ∃ j ∈ Finset.range x1.size, ∃ j' ∈ Finset.range x1.size, ((gateAt x1 j).op = GateOp.and ∧ ∃ i ∈ (gateAt x1 j).inputs, 26 ≤ i ∧ (gateAt x1 (i - 26)).op = GateOp.and) ∧ ((gateAt x1 j').op = GateOp.and ∧ ∃ i ∈ (gateAt x1 j').inputs, 26 ≤ i ∧ (gateAt x1 (i - 26)).op = GateOp.and) ∧ j ≠ j' := by
      by_contra hcon
      apply hatmost
      intro j hj j' hj' haa haa'
      by_contra hne
      exact hcon ⟨j, hj, j', hj', haa, haa', hne⟩
    obtain ⟨j, hj, j', hj', haa, haa', hne⟩ := hex
    by_cases hthird : ∃ k ∈ Finset.range x1.size, ((gateAt x1 k).op = GateOp.and ∧ ∃ i ∈ (gateAt x1 k).inputs, 26 ≤ i ∧ (gateAt x1 (i - 26)).op = GateOp.and) ∧ k ≠ j ∧ k ≠ j'
    · obtain ⟨k, hk, haak, kj, kj'⟩ := hthird
      exact h3 x1 x2 x3 hm hr ha hb hacc hrej he1 he2
        ⟨j, hj, j', hj', k, hk, hne, Ne.symm kj, Ne.symm kj', haa, haa', haak⟩
    · exact h2 x1 x2 x3 hm hr ha hb hacc hrej he1 he2 ⟨j, hj, j', hj', hne, haa, haa',
        fun k hk haak => by
          by_cases kj : k = j
          · exact Or.inl kj
          · by_cases kj' : k = j'
            · exact Or.inr kj'
            · exact absurd ⟨k, hk, haak, kj, kj'⟩ hthird⟩
