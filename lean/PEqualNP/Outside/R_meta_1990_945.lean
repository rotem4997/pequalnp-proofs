import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1990_945
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (n : ℕ) (a b : Fin n → Bool), (∀ i, a i = true → b i = true) →
        ∀ k : ℕ, (C.wires (List.ofFn a)).getD k false = true →
          (C.wires (List.ofFn b)).getD k false = true)
    (h2 : ∀ (X Y : Finset (Fin 13)),
      (∀ i ∈ X, ∀ j ∈ Y, ¬ ((i : ℕ) + (j : ℕ)) % 13 ∈ [(0 : ℕ), 1, 3, 9]) →
        X.card ≤ 3 ∨ Y.card ≤ 3)
    (h3 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → o.length ≤ 2 →
      (∀ (X Y : Finset (Fin 13)),
        PEqualNP.CircuitLowerBounds.GateOp.or.eval (o.map fun k =>
          (C.wires (List.ofFn (fun i : Fin 26 => if (i : ℕ) < 13 then decide (Fin.ofNat 13 (i : ℕ) ∈ X)
            else decide (Fin.ofNat 13 (i : ℕ) ∈ Y)))).getD k false) = true ↔
        ∃ i ∈ X, ∃ j ∈ Y, ((i : ℕ) + (j : ℕ)) % 13 ∈ [(0 : ℕ), 1, 3, 9]) →
      63 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C o hM ho hP
  dsimp only at hP
  obtain ⟨hE, hN⟩ := hP
  have hmono : ∀ X Y X' Y' : Finset (Fin 13), X ⊆ X' → Y ⊆ Y' →
      PEqualNP.CircuitLowerBounds.GateOp.or.eval (o.map fun k =>
          (C.wires (List.ofFn (fun i : Fin 26 => if (i : ℕ) < 13 then decide (Fin.ofNat 13 (i : ℕ) ∈ X)
            else decide (Fin.ofNat 13 (i : ℕ) ∈ Y)))).getD k false) = true →
      PEqualNP.CircuitLowerBounds.GateOp.or.eval (o.map fun k =>
          (C.wires (List.ofFn (fun i : Fin 26 => if (i : ℕ) < 13 then decide (Fin.ofNat 13 (i : ℕ) ∈ X')
            else decide (Fin.ofNat 13 (i : ℕ) ∈ Y')))).getD k false) = true := by
    intro X Y X' Y' hX hY h
    have e : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id :=
      fun l => rfl
    rw [e] at h ⊢
    simp only [List.any_eq_true, List.mem_map] at h ⊢
    obtain ⟨b, ⟨k, hk, rfl⟩, hb⟩ := h
    refine ⟨_, ⟨k, hk, rfl⟩, ?_⟩
    refine h1 C hM 26 _ _ ?_ k hb
    intro i hi
    split_ifs at hi ⊢
    · simp only [decide_eq_true_eq] at hi ⊢
      exact hX hi
    · simp only [decide_eq_true_eq] at hi ⊢
      exact hY hi
  apply h3 C o hM ho
  intro X Y
  constructor
  · intro hF
    by_contra hne
    have hne : ∀ i ∈ X, ∀ j ∈ Y, ¬ ((i : ℕ) + (j : ℕ)) % 13 ∈ [(0 : ℕ), 1, 3, 9] := fun i hi j hj h => hne ⟨i, hi, j, hj, h⟩
    rcases h2 X Y (fun i hi j hj h => hne i hi j hj h) with hX | hY
    · have hsub : Y ⊆ ({x8 : Fin 13 | ∀ x9 ∈ X, ¬ ((x9 : ℕ) + (x8 : ℕ)) % 13 ∈ [(0 : ℕ), 1, 3, 9]} : Finset (Fin 13)) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        exact hne i hi j hj
      have h' := hmono X Y X _ subset_rfl hsub hF
      have hf := (hN X hX).1
      exact absurd (hf.symm.trans h') (by decide)
    · have hsub : X ⊆ ({x8 : Fin 13 | ∀ x9 ∈ Y, ¬ ((x9 : ℕ) + (x8 : ℕ)) % 13 ∈ [(0 : ℕ), 1, 3, 9]} : Finset (Fin 13)) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro j hj
        rw [Nat.add_comm]
        exact hne i hi j hj
      have h' := hmono X Y _ Y hsub subset_rfl hF
      have hf := (hN Y hY).2
      exact absurd (hf.symm.trans h') (by decide)
  · rintro ⟨i, hi, j, hj, hij⟩
    exact hmono {i} {j} X Y (Finset.singleton_subset_iff.2 hi) (Finset.singleton_subset_iff.2 hj)
      (hE i j hij)
