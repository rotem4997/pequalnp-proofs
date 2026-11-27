import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_5827_318
    (edge : ∀ (c : ℕ), (([97329797398559, 0, 140754668224512, 96779974475804, 0, 0, 549822922753, 0, 140754668224512] : List ℕ).getD (c/48) 0).testBit (c%48)=true →
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 16 → ∃ x : Fin 10 → Bool,
        let v := List.ofFn x ++ [x 0 || x 1]
        let a := v.getD (c / 12 % 12) false
        let b := v.getD (c % 12) false
        let w := D.wires (v ++ [if c < 144 then a && b else if c < 288 then a || b else !a])
        (w.getD i false || w.getD j false) ≠ ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
    (nonedge : ∀ (c : ℕ), (([140187738087775, 22548578304, 140754668226304, 139637982265690, 21474836480, 1536, 549755822081, 1073741824, 140754668224768] : List ℕ).getD (c/48) 0).testBit (c%48)=true →
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 16 → ∃ x : Fin 10 → Bool,
        let v := List.ofFn x ++ [x 0 || x 2]
        let a := v.getD (c / 12 % 12) false
        let b := v.getD (c % 12) false
        let w := D.wires (v ++ [if c < 144 then a && b else if c < 288 then a || b else !a])
        (w.getD i false || w.getD j false) ≠ ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (17 : ℕ) →       have x8 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };       have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));       have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x3.wires ({ gates := [x8], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;       (∃ (x11 : Fin (10 : ℕ) → Bool), x10 x11 ((10 : ℕ) + ↑x4) = Bool.true ∧ x10 x11 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x12 : Fin (10 : ℕ) → Bool), x10 x12 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x12 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x13 : Fin (10 : ℕ) → Bool), x9 x13 = Bool.false → x10 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x13 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x14 : Fin (10 : ℕ) → Bool), x9 x14 = Bool.true ∧ x10 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x14 ((10 : ℕ) + ↑x5) = Bool.false := by
  have firstReduction : (∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
        ∃ x : Fin 10 → Bool, let w := D.wires (List.ofFn x ++ [x 0 || x 1]);
          (w.getD i false || w.getD j false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) → (∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
        ∃ x : Fin 10 → Bool, let w := D.wires (List.ofFn x ++ [x 0 || x 2]);
          (w.getD i false || w.getD j false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) → (∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (17 : ℕ) →       have x8 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };       have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));       have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x3.wires ({ gates := [x8], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;       (∃ (x11 : Fin (10 : ℕ) → Bool), x10 x11 ((10 : ℕ) + ↑x4) = Bool.true ∧ x10 x11 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x12 : Fin (10 : ℕ) → Bool), x10 x12 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x12 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x13 : Fin (10 : ℕ) → Bool), x9 x13 = Bool.false → x10 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x13 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x14 : Fin (10 : ℕ) → Bool), x9 x14 = Bool.true ∧ x10 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x14 ((10 : ℕ) + ↑x5) = Bool.false) := by
    clear edge nonedge
    intro adjacent nonadjacent
    intro a b C u v fan budget
    let target (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
    let generator (g : Bool) (i : Fin 10) : Fin 10 :=
      ((if g then [2, 1, 6, 8, 3, 7, 0, 9, 5, 4] else [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]) : List (Fin 10)).getD i.val 0
    let run (w : List Bool) (i : Fin 10) := w.foldr generator i
    let words : List (List Bool) := [[], [], [], [false, true, false, true, true, true], [false, true, false, true, true, true], [false, true, false], [true, true, true, false, true, true, true, false], [false, true, false], [false, true, true, true, true, false], [true, true, true, false, true, true, false], [], [false], [false], [false, true, false, true, true, true, false], [false, true, false, true, true, true, false], [false], [false, true, true, true], [false, true, true, true, true], [true, true, true, false, true, true], [false, true, true, true, true], [false, true], [false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, false, true, true, false], [true, false, true, false, true, true, false], [false, true, false, true, false, true, true, true, false], [true, true, true, true, true], [false, true, false, true, false, true, true, true, false], [true, false, true, false, true, false, true, false], [false, true, true, true, true, true, false, true, true], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, true, true, true, false, true, true], [true, true, true, true, false, true, true], [false, true, false, true, false, true, true], [false, true, false, true, false, true, true], [true, false, true, false, true, false], [true, false, true, false, true], [false, true, false, true, false, true, false, true, false], [true, false, true, false, true, false], [false, true, false, true, false, true, false, true], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false, true, true, true], [true, false, true, false, true, true], [true, false, true, false, true, true], [true, false, true, true, true], [true, true, false], [false, true, false, true, false, true, true, true], [false, true, false, true, true, true, true, true, false], [false, true, false, true, true, false], [false, true, false, true, false, true, true, true], [true, false, true, true, true], [true, false], [true, false], [false, true, false, true, true, true, true, false], [false, true, true, true, true, false, true, false], [true, true, false, true, true, true], [true, false], [false, true, false, true, false], [false, true, false, true, true, true, true, false], [false, true, false, true, false], [true, true, false, true, true, false, true, true], [true, false], [true], [true], [true, true, false, true, true, true, false], [true, true, false, true, false, true, false], [false, true, false, true, true, true, true], [false, true, false, true], [true], [false, true, true, false, true], [false, true, false, true], [false, true, false, true, true, true, true], [true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, false], [true, false, true, false, true, true, true, false], [true, true, true, true, true, false, true, true], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, true], [true, false, true, true, true, true, false], [true, true, false, true, false], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true], [false, true, false, true, false, true], [false, true, false, true, false, true, false], [false, true, false, true, false, true, false], [true, false, true, false], [true, false, true], [false, true, true, false, true, false, true], [true, false, true, false], [true, true, false, true, true, true, true], [true, false, true, false], [true, false, true, false, true, true, true], [true, false, true, true, true, true], [false, true, false, true, false, true, true, true, true], [true, false, true, false, true, false, true, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true, true, false], [true, false, true, true, true, true], [true, false, true, false, true, true, true, true, false], [true, true, false, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true], [], [false], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false], [true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true, false, true, true, true], []]
    let second : List (Fin 10) := [1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    let source : List Nat := [0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99]
    let ix (a b : Fin 11) := a.val * 11 + b.val
    let σ (a b : Fin 11) (i : Fin 10) : Fin 10 :=
      run (words.getD (ix a b) []) i
    let k (a b : Fin 11) := second.getD (ix a b) 1
    let src (a b : Fin 11) := source.getD (ix a b) 0
    have choices : ∀ a b : Fin 11, k a b = 1 ∨ k a b = 2 := by decide +kernel
    have kinds : ∀ a b : Fin 11,
        (src a b = 99 ∧ a.val = 10 ∧ b.val = 10) ∨
        (src a b = 0 ∧ (a.val = 10 ∨ σ a b ⟨a.val % 10, Nat.mod_lt _ (by decide)⟩ = 0) ∧
            (b.val = 10 ∨ σ a b ⟨b.val % 10, Nat.mod_lt _ (by decide)⟩ = 0) ∧ (a.val < 10 ∨ b.val < 10)) ∨
        (src a b = 10 ∧ a.val < 10 ∧ b.val < 10 ∧
            σ a b ⟨a.val % 10, Nat.mod_lt _ (by decide)⟩ = 0 ∧
            σ a b ⟨b.val % 10, Nat.mod_lt _ (by decide)⟩ = k a b) := by decide +kernel
    have one (g : Bool) (x : Fin 10 → Bool) : target (x ∘ generator g) = target x := by
      cases g
      · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 6 && x 9) || (x 9 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 1 && x 0) || (x 6 && x 9) || (x 8 && x 5) || (x 3 && x 4) || (x 7 && x 9) || (x 9 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 5 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
    have word (w : List Bool) (x : Fin 10 → Bool) : target (x ∘ run w) = target x := by
      induction w generalizing x with
      | nil => rfl
      | cons g w ih => exact (ih (x ∘ generator g)).trans (one g x)
    have invariant (x : Fin 10 → Bool) : target (x ∘ σ a b) = target x := word _ x
    let ρ (i : Nat) := if h : i < 10 then (σ a b ⟨i,h⟩).val else if i = 10 then src a b else i
    have srcCases : src a b = 99 ∨ src a b = 0 ∨ src a b = 10 := by
      rcases kinds a b with h | h | h
      · exact Or.inl h.1
      · exact Or.inr (Or.inl h.1)
      · exact Or.inr (Or.inr h.1)
    have hρ (n : Nat) (lo : 11 ≤ n) (hi : n ≤ 28) (i : Nat) : ρ i = n ↔ i = n := by
      by_cases h : i < 10
      · simp only [ρ,dite_eq_left h]
        have := (σ a b ⟨i,h⟩).isLt
        omega
      · by_cases e : i = 10
        · simp only [ρ,dite_eq_right h,ite_eq_left e]
          rcases srcCases with s|s|s <;> omega
        · simp [ρ,h,e]
    let raw (x : Fin 10 → Bool) (i : Fin 11) := (List.ofFn (x ∘ σ a b)).getD i.val false
    have rawGood (x : Fin 10 → Bool) (i : Fin 11) (h : i.val < 10) :
        raw x i = x (σ a b ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩) := by
      change (List.ofFn (x ∘ σ a b)).getD i.val false = _
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
      simp [Nat.mod_eq_of_lt h]
    have rawBad (x : Fin 10 → Bool) (i : Fin 11) (h : i.val = 10) : raw x i = false := by
      simp [raw,h,List.getD_eq_getElem?_getD]
    let observed (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 || x (k a b)]
    have gift (x : Fin 10 → Bool) : (raw x a || raw x b) = (observed x).getD (src a b) false := by
      rcases kinds a b with ⟨s,ha,hb⟩ | ⟨s,ha,hb,hn⟩ | ⟨s,ha,hb,za,zb⟩
      · rw [rawBad _ _ ha,rawBad _ _ hb,s,List.getD_eq_default _ _ (by simp [observed])]
        rfl
      · have each (i : Fin 11) (hi : i.val = 10 ∨ σ a b ⟨i.val % 10,Nat.mod_lt _ (by decide)⟩ = 0) :
            raw x i = if i.val = 10 then false else x 0 := by
          by_cases e : i.val = 10
          · simp [e,rawBad _ _ e]
          · have lt : i.val < 10 := by have := i.isLt; omega
            simp [e,rawGood _ _ lt,hi.resolve_left e]
        rw [each a ha,each b hb,s,List.getD_append _ _ _ _ (by simp)]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,show 0 < 10 by decide,dite_eq_left,Option.getD_some]
        rcases hn with h | h <;> split_ifs <;> simp_all <;> omega
      · rw [rawGood _ _ ha,rawGood _ _ hb,za,zb,s]
        change _ = (List.ofFn x ++ [x 0 || x (k a b)]).getD 10 false
        rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
        rfl

    let rg (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
    have app (w : List Bool) (z : Bool) (i : Nat) :
        (w ++ [z]).getD i false = if i = w.length then z else w.getD i false := by
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
      · by_cases eq : i = w.length
        · subst i
          simp [List.getD_eq_getElem?_getD]
        · rw [ite_eq_right eq, List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by omega)]
    have simulation (gs : List Gate) (xs ys : List Bool)
        (len : xs.length = ys.length) (lower : 11 ≤ xs.length) (cap : xs.length + gs.length ≤ 28)
        (initial : ∀ i, xs.getD i false = ys.getD (ρ i) false) :
        ∀ i, ((⟨gs,0⟩ : Circuit).wires xs).getD i false =
          ((⟨gs.map rg,0⟩ : Circuit).wires ys).getD (ρ i) false := by
      induction gs generalizing xs ys with
      | nil => exact initial
      | cons g gs ih =>
        let z := g.op.eval (g.inputs.map fun i => xs.getD i false)
        have next : (rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false) = z := by
          change g.op.eval _ = g.op.eval _
          congr 1
          simp only [rg,List.map_map,Function.comp_def]
          exact List.map_congr_left fun i _ => (initial i).symm
        change ∀ i, ((⟨gs,0⟩ : Circuit).wires (xs ++ [z])).getD i false =
          ((⟨gs.map rg,0⟩ : Circuit).wires (ys ++ [(rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false)])).getD (ρ i) false
        rw [next]
        apply ih
        · simp [len]
        · simp; omega
        · simp_all only [List.length_cons,List.length_append,List.length_nil]; omega
        · intro i
          simp only [app,←len,hρ _ lower (by omega) i,initial i]
    let D : Circuit := ⟨C.gates.map rg,0⟩
    have newFan : FanInTwo D := by
      intro g hg
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
      simpa [rg] using fan h hh
    have newCap : D.size ≤ 17 := by
      change (C.gates.map rg).length ≤ 17
      rw [List.length_map]
      exact budget
    have physical (x : Fin 10 → Bool) (i : Nat) :
        (C.wires (List.ofFn (x ∘ σ a b) ++ [raw x a || raw x b])).getD i false =
          (D.wires (observed x)).getD (ρ i) false := by
      apply simulation
      · simp [observed]
      · simp
      · have h : C.gates.length ≤ 17 := budget
        simpa only [List.length_append,List.length_ofFn,List.length_cons,List.length_nil] using (show 10 + (0+1) + C.gates.length ≤ 28 by omega)
      · intro j
        by_cases hj : j < 10
        · simp only [ρ,dite_eq_left hj,observed]
          rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simp)]
          rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hj),List.getElem_ofFn,
            List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact (σ a b ⟨j,hj⟩).isLt),List.getElem_ofFn]
          rfl
        · by_cases he : j = 10
          · subst j
            simp only [ρ,show ¬ 10 < 10 by decide,ite_eq_left]
            rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
            exact gift x
          · have high : 11 ≤ j := by omega
            simp only [ρ,dite_eq_right hj,ite_eq_right he]
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [observed]; omega)]
    let I := 10 + u.val
    let J := 10 + v.val
    have miss : ∃ x : Fin 10 → Bool,
        (((D.wires (observed x)).getD (ρ I) false) || ((D.wires (observed x)).getD (ρ J) false)) ≠ target x := by
      rcases choices a b with h | h
      · simpa only [observed,h,target] using adjacent D (ρ I) (ρ J) newFan newCap
      · simpa only [observed,h,target] using nonadjacent D (ρ I) (ρ J) newFan newCap
    obtain ⟨x,hx⟩ := miss
    dsimp only
    intro _ _ sound
    let y := x ∘ σ a b
    let pre := (⟨[⟨.or,[a.val,b.val]⟩],0⟩ : Circuit).wires (List.ofFn y)
    have starter : pre = List.ofFn y ++ [raw x a || raw x b] := by
      change (_ ++ [raw x a || (raw x b || false)]) = _
      simp
    have mismatch : ((C.wires pre).getD I false || (C.wires pre).getD J false) ≠ target y := by
      rw [starter,physical,physical,invariant]
      exact hx
    have zsound : target y = false → (C.wires pre).getD I false = false ∧ (C.wires pre).getD J false = false := sound y
    refine ⟨y,?_⟩
    change target y = true ∧ (C.wires pre).getD I false = false ∧ (C.wires pre).getD J false = false
    cases ht : target y <;> cases hu : (C.wires pre).getD I false <;> cases hv : (C.wires pre).getD J false <;> simp_all only [Bool.false_eq_true, Bool.true_eq_false, Bool.false_or,Bool.true_or,not_true_eq_false, ne_eq, and_self,true_and, and_true]

  let target (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let key (b : Bool) : Fin 10 := if b then 2 else 1
  let perms : List (List (List (Fin 10))) := [[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 7, 5, 4, 6, 3, 9, 8], [0, 1, 6, 8, 5, 4, 2, 9, 3, 7], [0, 1, 6, 9, 4, 5, 2, 8, 7, 3], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [1, 0, 4, 9, 6, 2, 5, 3, 7, 8], [1, 0, 5, 7, 2, 6, 4, 8, 9, 3], [1, 0, 5, 8, 6, 2, 4, 7, 3, 9]], [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 7, 5, 4, 6, 3, 9, 8], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 1, 0, 5, 7, 3, 6, 4, 8, 9], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 7, 5, 4, 6, 3, 9, 8], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 1, 0, 5, 7, 3, 6, 4, 8, 9]]]
  let perm (b : Bool) (s : Fin 8) (i : Fin 10) : Fin 10 :=
    ((perms.getD (if b then 1 else 0) []).getD s.val []).getD i.val 0
  let extend (f : Fin 10 → Fin 10) (i : ℕ) := if h : i<10 then (f ⟨i,h⟩).val else i
  let codes (b : Bool) : List ℕ := if b then [0, 1, 2, 3, 4, 6, 8, 13, 15, 18, 20, 22, 39, 40, 41, 42, 43, 44, 45, 46, 78, 80, 82, 104, 105, 106, 130, 143, 145, 147, 148, 150, 152, 159, 162, 164, 166, 184, 185, 186, 187, 188, 189, 190, 224, 226, 249, 250, 288, 301, 327, 366, 392, 418, 431] else [0, 1, 2, 3, 4, 26, 27, 28, 30, 32, 34, 39, 43, 44, 46, 130, 143, 146, 147, 148, 171, 172, 174, 176, 178, 187, 188, 190, 288, 314, 327, 418, 431]
  let masks (b : Bool) : List ℕ := if b then [140187738087775, 22548578304, 140754668226304, 139637982265690, 21474836480, 1536, 549755822081, 1073741824, 140754668224768] else [97329797398559, 0, 140754668224512, 96779974475804, 0, 0, 549822922753, 0, 140754668224512]
  have packed : ∀ (b : Bool), ∀ c∈codes b, ((masks b).getD (c/48) 0).testBit (c%48)=true := by decide +kernel
  let table : List (List (List (List ℕ))) := [[[[0, 8, 16, 24, 32, 33, 18, 25, 26, 27, 0, 1144], [8, 4, 36, 28, 20, 21, 38, 29, 31, 30, 4, 1144], [16, 36, 208, 216, 224, 225, 240, 217, 256, 257, 272, 1144], [24, 28, 216, 312, 220, 263, 258, 344, 352, 348, 368, 1144], [32, 20, 224, 220, 212, 244, 227, 262, 260, 222, 276, 1144], [33, 21, 225, 263, 244, 213, 226, 221, 223, 261, 277, 1144], [18, 38, 240, 258, 227, 226, 210, 259, 218, 219, 274, 1144], [25, 29, 217, 344, 262, 221, 259, 313, 349, 353, 369, 1144], [26, 31, 256, 352, 260, 223, 218, 349, 314, 346, 370, 1144], [27, 30, 257, 348, 222, 261, 219, 353, 346, 315, 371, 1144], [0, 4, 272, 368, 276, 277, 274, 369, 370, 371, 1040, 1144], [1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144]], [[0, 1040, 1168, 1176, 1184, 1185, 1170, 1177, 1178, 1179, 1040, 0], [1040, 4, 1188, 1180, 1172, 1173, 1190, 1181, 1183, 1182, 1040, 4], [1168, 1188, 208, 1368, 1376, 1377, 1392, 1369, 1408, 1409, 1424, 208], [1176, 1180, 1368, 312, 1372, 1415, 1410, 1496, 1504, 1500, 1520, 312], [1184, 1172, 1376, 1372, 212, 1396, 1379, 1414, 1412, 1374, 1428, 212], [1185, 1173, 1377, 1415, 1396, 213, 1378, 1373, 1375, 1413, 1429, 213], [1170, 1190, 1392, 1410, 1379, 1378, 210, 1411, 1370, 1371, 1426, 210], [1177, 1181, 1369, 1496, 1414, 1373, 1411, 313, 1501, 1505, 1521, 313], [1178, 1183, 1408, 1504, 1412, 1375, 1370, 1501, 314, 1498, 1522, 314], [1179, 1182, 1409, 1500, 1374, 1413, 1371, 1505, 1498, 315, 1523, 315], [1040, 1040, 1424, 1520, 1428, 1429, 1426, 1521, 1522, 1523, 1040, 1040], [0, 4, 208, 312, 212, 213, 210, 313, 314, 315, 1040, 1144]], [[2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304], [2308, 2308, 2308, 2308, 2308, 2308, 2308, 2308, 2308, 2308, 2308, 2308], [2512, 2512, 2512, 2512, 2512, 2512, 2512, 2512, 2512, 2512, 2512, 2512], [2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616], [2516, 2516, 2516, 2516, 2516, 2516, 2516, 2516, 2516, 2516, 2516, 2516], [2517, 2517, 2517, 2517, 2517, 2517, 2517, 2517, 2517, 2517, 2517, 2517], [2514, 2514, 2514, 2514, 2514, 2514, 2514, 2514, 2514, 2514, 2514, 2514], [2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617], [2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618], [2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619], [3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344], [3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448]]], [[[0, 8, 16, 24, 32, 33, 48, 25, 64, 65, 0, 1144], [8, 104, 10, 120, 122, 123, 144, 121, 160, 161, 176, 1144], [16, 10, 2, 34, 26, 27, 50, 35, 67, 66, 2, 1144], [24, 120, 34, 312, 320, 328, 336, 344, 352, 360, 368, 1144], [32, 122, 26, 320, 314, 346, 338, 329, 362, 354, 370, 1144], [33, 123, 27, 328, 346, 315, 339, 321, 355, 363, 371, 1144], [48, 144, 50, 336, 338, 339, 624, 337, 640, 641, 656, 1144], [25, 121, 35, 344, 329, 321, 337, 313, 361, 353, 369, 1144], [64, 160, 67, 352, 362, 355, 640, 361, 832, 840, 848, 1144], [65, 161, 66, 360, 354, 363, 641, 353, 840, 833, 849, 1144], [0, 176, 2, 368, 370, 371, 656, 369, 848, 849, 1040, 1144], [1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144, 1144]], [[0, 1160, 1040, 1176, 1184, 1185, 1200, 1177, 1216, 1217, 1040, 0], [1160, 104, 1162, 1272, 1274, 1275, 1296, 1273, 1312, 1313, 1328, 104], [1040, 1162, 2, 1186, 1178, 1179, 1202, 1187, 1219, 1218, 1040, 2], [1176, 1272, 1186, 312, 1472, 1480, 1488, 1496, 1504, 1512, 1520, 312], [1184, 1274, 1178, 1472, 314, 1498, 1490, 1481, 1514, 1506, 1522, 314], [1185, 1275, 1179, 1480, 1498, 315, 1491, 1473, 1507, 1515, 1523, 315], [1200, 1296, 1202, 1488, 1490, 1491, 624, 1489, 1792, 1793, 1808, 624], [1177, 1273, 1187, 1496, 1481, 1473, 1489, 313, 1513, 1505, 1521, 313], [1216, 1312, 1219, 1504, 1514, 1507, 1792, 1513, 832, 1992, 2000, 832], [1217, 1313, 1218, 1512, 1506, 1515, 1793, 1505, 1992, 833, 2001, 833], [1040, 1328, 1040, 1520, 1522, 1523, 1808, 1521, 2000, 2001, 1040, 1040], [0, 104, 2, 312, 314, 315, 624, 313, 832, 833, 1040, 1144]], [[2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304, 2304], [2408, 2408, 2408, 2408, 2408, 2408, 2408, 2408, 2408, 2408, 2408, 2408], [2306, 2306, 2306, 2306, 2306, 2306, 2306, 2306, 2306, 2306, 2306, 2306], [2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616, 2616], [2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618, 2618], [2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619, 2619], [2928, 2928, 2928, 2928, 2928, 2928, 2928, 2928, 2928, 2928, 2928, 2928], [2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617, 2617], [3136, 3136, 3136, 3136, 3136, 3136, 3136, 3136, 3136, 3136, 3136, 3136], [3137, 3137, 3137, 3137, 3137, 3137, 3137, 3137, 3137, 3137, 3137, 3137], [3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344, 3344], [3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448, 3448]]]]
  let lookup (b : Bool) (o : Fin 3) (i j : Fin 12) :=
    (((table.getD (if b then 1 else 0) []).getD o.val []).getD i.val []).getD j.val 0
  let op (o : Fin 3) (a b : Bool) := if o=0 then a && b else if o=1 then a || b else !a
  let decode (c : ℕ) (w : ℕ → Bool) :=
    if c<144 then w (c/12%12) && w (c%12) else if c<288 then w (c/12%12) || w (c%12) else !w (c/12%12)
  let support (b : Bool) (i j : ℕ) : List ℕ := [0,(key b).val,10,11,i,j]
  let sample (b : Bool) (i j : ℕ) (a d u v : Bool) (h : ℕ) :=
    if h=0 then a else if h=(key b).val then d else if h=10 then a || d else if h=11 then false
    else if h=i then u else if h=j then v else false
  have cert : ∀ (b : Bool) (o : Fin 3) (i j : Fin 12),
      let e := lookup b o i j
      let c := e/8
      let s : Fin 8 := ⟨e%8,Nat.mod_lt _ (by decide)⟩
      let I := extend (perm b s) i.val
      let J := extend (perm b s) j.val
      c ∈ codes b ∧ c/12%12 ∈ support b I J ∧ c%12 ∈ support b I J ∧
      ∀ a d u v : Bool, let R := sample b I J a d u v
        op o (R I) (R J)=decode c R := by decide +kernel
  have stable : ∀ b s, (perm b s 0=0 ∧ perm b s (key b)=key b) ∨
      (perm b s 0=key b ∧ perm b s (key b)=0) := by decide +kernel
  have invariant2 (b : Bool) (s : Fin 8) (x : Fin 10→Bool) : target (x ∘ perm b s)=target x := by
    cases b <;> fin_cases s
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && x 9) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 2) || (x 6 && x 9) || (x 8 && x 3) || (x 5 && x 7) || (x 4 && x 9) || (x 9 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 9) || (x 9 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 9 && x 7) || (x 4 && x 3) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 6 && x 9) || (x 9 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 9) || (x 9 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 5) || (x 4 && x 3) || (x 9 && x 7) || (x 6 && x 8) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 7 && x 9) || (x 2 && x 3) || (x 6 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 9) || (x 9 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 6 && x 9) || (x 2 && x 7) || (x 7 && x 9) || (x 9 && x 4) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && x 9) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 7 && x 9) || (x 3 && x 4) || (x 4 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && x 9) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 7 && x 9) || (x 3 && x 4) || (x 4 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)); ac_rfl
  let start (b : Bool) (x : Fin 10→Bool) := List.ofFn x ++ [x 0 || x (key b)]
  let port (b : Bool) (x : Fin 10→Bool) (i : ℕ) := (start b x).getD i false
  have smallPort (b : Bool) (x : Fin 10→Bool) (i : Fin 10) : port b x i.val=x i := by
    change (List.ofFn x++[_]).getD i.val false=_
    rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have headPort (b : Bool) (x : Fin 10→Bool) : port b x 10=(x 0 || x (key b)) := by
    change (List.ofFn x++[_]).getD 10 false=_
    rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
    rfl
  have badPort (b : Bool) (x : Fin 10→Bool) (i : ℕ) (hi : 11 ≤ i) : port b x i=false :=
    List.getD_eq_default _ _ (by simp [start];omega)
  have atPorts (b : Bool) (s : Fin 8) (x : Fin 10→Bool) (i : ℕ) :
      port b (x ∘ perm b s) i=port b x (extend (perm b s) i) := by
    by_cases h : i<10
    · rw [show extend (perm b s) i=(perm b s ⟨i,h⟩).val by simp [extend,h],smallPort]
      exact smallPort b (x ∘ perm b s) ⟨i,h⟩
    · rw [show extend (perm b s) i=i by simp [extend,h]]
      by_cases e : i=10
      · subst i
        rw [headPort,headPort]
        rcases stable b s with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> simp [Function.comp_def,h₁,h₂,Bool.or_comm]
      · rw [badPort _ _ _ (by omega),badPort _ _ _ (by omega)]
  let clamp (i : ℕ) : Fin 12 := ⟨min i 11,by omega⟩
  have clamped (b : Bool) (x : Fin 10→Bool) (i : ℕ) : port b x (clamp i).val=port b x i := by
    by_cases h : i≤11
    · simp [clamp,Nat.min_eq_left h]
    · change port b x (min i 11)=_
      rw [Nat.min_eq_right (by omega),badPort _ _ _ le_rfl,badPort _ _ _ (by omega)]
  have encode (b : Bool) (g : Gate) (good : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
      ∃ (o : Fin 3) (i j : Fin 12), ∀ x,
        g.op.eval (g.inputs.map (port b x))=op o (port b x i.val) (port b x j.val) := by
    obtain ⟨q,l⟩ := g
    obtain ⟨allowed,short⟩ := good
    change q=.and ∨ q=.or ∨ q=.not at allowed
    change l.length≤2 at short
    rcases l with _|⟨i,_|⟨j,rest⟩⟩
    · rcases allowed with rfl|rfl|rfl
      · exact ⟨2,11,11,fun x => by change true= !(port b x 11);rw [badPort _ _ _ le_rfl] <;> rfl⟩
      · exact ⟨1,11,11,fun x => by change false=(port b x 11 || port b x 11);rw [badPort _ _ _ le_rfl] <;> rfl⟩
      · exact ⟨2,11,11,fun x => by change true= !(port b x 11);rw [badPort _ _ _ le_rfl] <;> rfl⟩
    · rcases allowed with rfl|rfl|rfl
      · exact ⟨0,clamp i,clamp i,fun x => by change (port b x i && true)=(port b x _ && port b x _);simp [clamped]⟩
      · exact ⟨1,clamp i,clamp i,fun x => by change (port b x i || false)=(port b x _ || port b x _);simp [clamped]⟩
      · exact ⟨2,clamp i,clamp i,fun x => by change (!(port b x i))= (!(port b x _));rw [clamped]⟩
    · cases rest with
      | cons t ts => simp at short
      | nil =>
        rcases allowed with rfl|rfl|rfl
        · exact ⟨0,clamp i,clamp j,fun x => by change (port b x i && (port b x j && true))=(port b x _ && port b x _);simp [clamped]⟩
        · exact ⟨1,clamp i,clamp j,fun x => by change (port b x i || (port b x j || false))=(port b x _ || port b x _);simp [clamped]⟩
        · exact ⟨2,clamp i,clamp i,fun x => by change (!(port b x i))= (!(port b x _));rw [clamped]⟩
  have late (w : List Bool) (z : Bool) (i : ℕ) :
      (w++[z]).getD i false = if i=w.length then z else w.getD i false := by
    by_cases h : i<w.length
    · rw [List.getD_append _ _ _ _ h,ite_eq_right (by omega)]
    · by_cases e : i=w.length
      · subst i
        simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right e,List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
  let ren (f : Fin 10→Fin 10) (g : Gate) : Gate := ⟨g.op,g.inputs.map (extend f)⟩
  have fixes (f : Fin 10→Fin 10) (n i : ℕ) (h : 10≤n) : extend f i=n ↔ i=n := by
    by_cases j : i<10
    · simp only [extend,dite_eq_left j]
      have := (f ⟨i,j⟩).isLt
      omega
    · simp [extend,j]
  have transport (f : Fin 10→Fin 10) (gs : List Gate) (xs ys : List Bool)
      (len : xs.length=ys.length) (low : 10≤xs.length)
      (base : ∀ i,xs.getD i false=ys.getD (extend f i) false) : ∀ i,
      ((⟨gs,0⟩ : Circuit).wires xs).getD i false =
      ((⟨gs.map (ren f),0⟩ : Circuit).wires ys).getD (extend f i) false := by
    induction gs generalizing xs ys with
    | nil => exact base
    | cons g gs ih =>
      let z := g.op.eval (g.inputs.map fun i => xs.getD i false)
      have step : (ren f g).op.eval ((ren f g).inputs.map fun i => ys.getD i false)=z := by
        change g.op.eval _ = g.op.eval _
        congr 1
        simp only [ren,List.map_map,Function.comp_def]
        exact List.map_congr_left fun i _ => (base i).symm
      change ∀ i, ((⟨gs,0⟩ : Circuit).wires (xs++[z])).getD i false=
        ((⟨gs.map (ren f),0⟩ : Circuit).wires (ys++[(ren f g).op.eval ((ren f g).inputs.map fun i => ys.getD i false)])).getD (extend f i) false
      rw [step]
      apply ih
      · simp [len]
      · simp;omega
      · intro i
        simp only [late,←len,fixes f _ i low,base]
  have spread (b : Bool) (I J : ℕ) (x : Fin 10→Bool) (t : ℕ) (e : t∈support b I J) :
      sample b I J (x 0) (x (key b)) (port b x I) (port b x J) t = port b x t := by
    have z := smallPort b x 0
    have d := smallPort b x (key b)
    have h := headPort b x
    have f := badPort b x 11 le_rfl
    change port b x 0=x 0 at z
    simp only [support,List.mem_cons,List.not_mem_nil,or_false] at e
    simp only [sample]
    split_ifs <;> first | subst_vars; assumption | subst_vars; symm; assumption | subst_vars; rfl | tauto
  have solve (b : Bool) (code : ℕ) (hc : code∈codes b) (D : Circuit) (i j : ℕ)
      (ok : FanInTwo D) (short : D.size≤16) :
      ∃ x,let w := D.wires (start b x++[decode code (port b x)])
          (w.getD i false || w.getD j false) ≠ target x := by
    have graph (x : Fin 10→Bool) : ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2) = target x := by
      simp [target,Bool.or_assoc]
    have selected := packed b code hc
    cases b
    · obtain ⟨x,h⟩ := edge code selected D i j ok short
      exact ⟨x,by simpa only [start,port,key,decode,Bool.false_eq_true,ite_false,graph] using h⟩
    · obtain ⟨x,h⟩ := nonedge code selected D i j ok short
      exact ⟨x,by simpa only [start,port,key,decode,ite_true,graph] using h⟩
  have second (b : Bool) (g : Gate) (gs : List Gate) (i j : ℕ)
      (fan : FanInTwo (⟨g::gs,0⟩ : Circuit)) (short : gs.length≤16) :
      ∃ x,let w := (⟨g::gs,0⟩ : Circuit).wires (start b x)
        (w.getD i false || w.getD j false) ≠ target x := by
    obtain ⟨o,u,v,write⟩ := encode b g (fan g List.mem_cons_self)
    let e := lookup b o u v
    let c := e/8
    let s : Fin 8 := ⟨e%8,Nat.mod_lt _ (by decide)⟩
    let f := perm b s
    let I := extend f u.val
    let J := extend f v.val
    obtain ⟨mem,ha,hb,tableEq⟩ := cert b o u v
    change c∈codes b at mem
    change c/12%12∈support b I J at ha
    change c%12∈support b I J at hb
    let D : Circuit := ⟨gs.map (ren f),0⟩
    have ok : FanInTwo D := by
      intro g' hg
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
      simpa [ren] using fan t (List.mem_cons_of_mem _ ht)
    have sz : D.size≤16 := by
      change (gs.map (ren f)).length≤16
      simpa only [List.length_map] using short
    obtain ⟨x,miss⟩ := solve b c mem D (extend f i) (extend f j) ok sz
    let y := x ∘ f
    let z := g.op.eval (g.inputs.map (port b y))
    have val : z=decode c (port b x) := by
      change g.op.eval (g.inputs.map (port b y))=_
      rw [write]
      have a := atPorts b s x u.val
      have d := atPorts b s x v.val
      change port b y u.val=port b x I at a
      change port b y v.val=port b x J at d
      rw [a,d]
      let R := sample b I J (x 0) (x (key b)) (port b x I) (port b x J)
      have equal : op o (R I) (R J)=decode c R := tableEq (x 0) (x (key b)) (port b x I) (port b x J)
      have on (t : ℕ) (ht : t∈support b I J) : R t=port b x t := spread b I J x t ht
      rw [on I (by simp [support]),on J (by simp [support])] at equal
      rw [equal]
      simp only [decode,on _ ha,on _ hb]
    have sim : ∀ t, ((⟨gs,0⟩ : Circuit).wires (start b y++[z])).getD t false =
        (D.wires (start b x++[decode c (port b x)])).getD (extend f t) false := by
      apply transport f gs
      · simp [start]
      · simp [start]
      · intro t
        simp only [late]
        have len (q : Fin 10→Bool) : (start b q).length=11 := by simp [start]
        simp only [len,fixes f 11 t (by decide),val]
        exact if_congr Iff.rfl rfl (atPorts b s x t)
    refine ⟨y,?_⟩
    change (((⟨gs,0⟩ : Circuit).wires (start b y++[z])).getD i false ||
      ((⟨gs,0⟩ : Circuit).wires (start b y++[z])).getD j false) ≠ target y
    rw [sim,sim,show target y=target x from invariant2 b s x]
    exact miss
  have allCases (b : Bool) (D : Circuit) (i j : ℕ) (ok : FanInTwo D) (cap : D.size≤17) :
      ∃ x,let w := D.wires (start b x)
        (w.getD i false || w.getD j false) ≠ target x := by
    obtain ⟨gs,out⟩ := D
    cases gs with
    | cons g gs =>
      apply second b g gs i j ok
      change (g::gs).length≤17 at cap
      simp at cap;omega
    | nil =>
      let g : Gate := ⟨.or,[]⟩
      have good : FanInTwo (⟨[g],0⟩ : Circuit) := by intro t ht;obtain rfl:=List.mem_singleton.mp ht;simp [g]
      obtain ⟨x,h⟩ := second b g [] i j good (by decide)
      refine ⟨x,?_⟩
      have id (u : ℕ) : (start b x++[false]).getD u false=(start b x).getD u false := by
        rw [late]
        split_ifs with eq
        · rw [eq,List.getD_eq_default _ _ le_rfl]
        · rfl
      change ((start b x++[false]).getD i false || (start b x++[false]).getD j false) ≠ target x at h
      rwa [id,id] at h
  have adjacent : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
        ∃ x : Fin 10 → Bool, let w := D.wires (List.ofFn x ++ [x 0 || x 1]);
          (w.getD i false || w.getD j false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := fun D i j h s => allCases false D i j h s
  have nonadjacent : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
        ∃ x : Fin 10 → Bool, let w := D.wires (List.ofFn x ++ [x 0 || x 2]);
          (w.getD i false || w.getD j false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := fun D i j h s => allCases true D i j h s

  exact firstReduction adjacent nonadjacent
