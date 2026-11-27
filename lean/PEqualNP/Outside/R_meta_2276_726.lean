import PEqualNP.Defs

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_2276_726
  (hmono : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 C →
    ∀ (a b : Fin 14 → Bool), (∀ i, a i = true → b i = true) →
      C.eval (List.ofFn a) = true → C.eval (List.ofFn b) = true)
  (hpos : ∀ (E : List (ℕ × ℕ)) (f : (Fin 14 → Bool) → Bool),
    E.all (fun e => decide (e.1 < e.2)) = true →
    (∀ (a b : Fin 14 → Bool), (∀ i, a i = true → b i = true) →
      f a = true → f b = true) →
    (∀ a, ((∃ i j : Fin 14, (↑i, ↑j) ∈ E ∧ a i = true ∧ a j = true) ∧
      ∀ i, a i = true → ¬ (∃ j k : Fin 14, (↑j, ↑k) ∈ E ∧
        Function.update a i false j = true ∧ Function.update a i false k = true)) →
      a 0 = false ∨ a 7 = false →
      (f a = true ↔ ∃ i j : Fin 14, (↑i, ↑j) ∈ E ∧ a i = true ∧ a j = true)) →
    ∀ a, (∃ i j : Fin 14, (↑i, ↑j) ∈ E ∧ (i ≠ 0 ∨ j ≠ 7) ∧ a i = true ∧ a j = true) →
      f a = true)
  (hneg : ∀ (E : List (ℕ × ℕ)) (f : (Fin 14 → Bool) → Bool),
    (0, 7) ∈ E →
    (∀ (a b : Fin 14 → Bool), (∀ i, a i = true → b i = true) →
      f a = true → f b = true) →
    (∀ a, ¬ (∃ i j : Fin 14, (↑i, ↑j) ∈ E ∧ a i = true ∧ a j = true) →
      (∀ i, a i = false → ∃ j k : Fin 14, (↑j, ↑k) ∈ E ∧
        Function.update a i true j = true ∧ Function.update a i true k = true) →
      a 0 = false ∨ a 7 = false → f a ≠ true) →
    ∀ a, f a = true → ∃ i j : Fin 14, (↑i, ↑j) ∈ E ∧ a i = true ∧ a j = true)
  (hbound : let E : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ a : Fin 14 → Bool,
      (∃ i j : Fin 14, (↑i, ↑j) ∈ E ∧ (i ≠ 0 ∨ j ≠ 7) ∧ a i = true ∧ a j = true) →
      C.eval (List.ofFn a) = true) →
    (∀ a : Fin 14 → Bool, C.eval (List.ofFn a) = true →
      ∃ i j : Fin 14, (↑i, ↑j) ∈ E ∧ a i = true ∧ a j = true) →
    C.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = false →
    25 ≤ C.size) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → x6 (0 : Fin (14 : ℕ)) = Bool.false ∨ x6 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x6) = Bool.true ↔ x2 x6)) → x4.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = (0 : Fin (14 : ℕ)) ∨ x7 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x4.size := by
  intro E0 P0 B0 C hM hA hB
  let E : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]
  let f : (Fin 14 → Bool) → Bool := fun a => C.eval (List.ofFn a)
  have hm : ∀ (a b : Fin 14 → Bool), (∀ i, a i = true → b i = true) →
      f a = true → f b = true := hmono C hM
  have hp := hpos E f (by decide) hm (by
    intro a ha hs
    exact hA a (Or.inl ha) hs)
  have hn := hneg E f (by decide) hm (by
    intro a ha hb hs hf
    exact ha ((hA a (Or.inr ⟨ha, hb⟩) hs).mp hf))
  exact hbound C hM hp hn hB
