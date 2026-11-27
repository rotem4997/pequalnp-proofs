import PEqualNP.Defs

-- On a vertex cover, start with the stars of its vertices and their subsets.
-- One instruction joins two available edge sets and makes all subsets of their union available.
-- Use the same list of instructions for every cover.
theorem PEqualNP.Outside.R_meta_4653_37
    (simulate : ∀ n : ℕ,
      let V := Fin n
      let Pair := V × V
      let step := fun (F : Set (Set Pair)) (r : Set Pair × Set Pair) =>
        {s : Set Pair | s ∈ F ∨ (r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2)}
      let start := fun (Z : Set V) =>
        {s : Set Pair | s = ∅ ∨ ∃ v ∈ Z, ∀ e ∈ s, e.1 = v ∨ e.2 = v}
      ∀ (E : Set Pair) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
        ∃ e ∈ E, x e.1 = true ∧ x e.2 = true) →
      ∃ R : List (Set Pair × Set Pair),
        R.length ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧
        ∀ Z : Set V, (∀ e ∈ E, e.1 ∈ Z ∨ e.2 ∈ Z) → E ∈ R.foldl step (start Z))
    (count : let V := Fin 42
      let Pair := V × V
      let E : Set Pair := {e | e.1.val < 21 ∧ 21 ≤ e.2.val ∧
        (e.2.val + 21 - e.1.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)}
      let step := fun (F : Set (Set Pair)) (r : Set Pair × Set Pair) =>
        {s : Set Pair | s ∈ F ∨ (r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2)}
      let start := fun (Z : Set V) =>
        {s : Set Pair | s = ∅ ∨ ∃ v ∈ Z, ∀ e ∈ s, e.1 = v ∨ e.2 = v}
      ∀ R : List (Set Pair × Set Pair),
        (∀ Z : Set V, (∀ e ∈ E, e.1 ∈ Z ∨ e.2 ∈ Z) → E ∈ R.foldl step (start Z)) →
        104 ≤ R.length) :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => {x3 : Fin x2.gates.length | (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) => { gates := x3.gates.set x4 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }, output := x3.output : PEqualNP.CircuitLowerBounds.Circuit }; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (42 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true; have x5 : Fin (42 : ℕ) → Fin (42 : ℕ) → Fin (42 : ℕ) → Bool := fun (x5 x6 x7 : Fin (42 : ℕ)) => Decidable.decide (x7 = x5 ∨ x7 = x6); have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x7 : Fin x6.gates.length),     (x6.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ x9 ∈ (x6.gates.get x7).inputs,         ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)),           x1 x11 x12 ∧             (x3 x6 (↑x7) x9).eval (List.ofFn (x5 x11 x12)) = Bool.false ∧               have x13 : List Bool := { gates := List.take (↑x7) x6.gates, output := x6.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (x5 x11 x12));               x13.getD x9 Bool.false = Bool.false ∧ ∃ x14 ∈ (x6.gates.get x7).inputs, x13.getD x14 Bool.false = Bool.true; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x4 x7 → x6 x7 → (104 : ℕ) ≤ x2 x7 := by
  dsimp only
  intro C mono computes _
  let E : Set (Fin 42 × Fin 42) := {e | e.1.val < 21 ∧ 21 ≤ e.2.val ∧
    (e.2.val + 21 - e.1.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)}
  have he (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ e ∈ E, x e.1 = true ∧ x e.2 = true := by
    constructor
    · intro h
      obtain ⟨a, b, edge, ha, hb⟩ := (computes x).mp h
      exact ⟨(a,b), edge, ha, hb⟩
    · rintro ⟨⟨a,b⟩, edge, ha, hb⟩
      exact (computes x).mpr ⟨a, b, edge, ha, hb⟩
  obtain ⟨R, cost, covers⟩ := simulate 42 E C mono he
  exact le_trans (count R covers) cost
