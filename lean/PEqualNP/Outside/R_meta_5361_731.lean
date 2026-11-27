import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5361_731
    (append : ∀ (n : ℕ) (D : Circuit) (g : Gate), Monotone2 D → ReadsBack n D →
      (g.op = .and ∨ g.op = .or) → g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < n + D.size) →
      ∃ E : Circuit, Monotone2 E ∧ ReadsBack n E ∧ E.size = D.size + 1 ∧
        ∀ xs : List Bool, xs.length = n →
          E.eval xs = g.op.eval (g.inputs.map fun i => (D.wires xs).getD i false))
    (search : ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (D : Circuit) (g : Gate),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     (have x5 : List ℕ := if x1 = (1 : Fin (42 : ℕ)) then [(81788948 : ℕ), (0 : ℕ), (4398145077304 : ℕ), (0 : ℕ), (4398077984768 : ℕ), (4398059094016 : ℕ), (4398256226304 : ℕ), (4406653222912 : ℕ)] else if x1 = (21 : Fin (42 : ℕ)) then [(71303174 : ℕ), (4398126202900 : ℕ), (4398067482760 : ℕ)] else [(10485770 : ℕ), (4398258323484 : ℕ), (0 : ℕ), (4402383429648 : ℕ)];       (x5.getD (List.idxOf ↑x2 [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (21 : ℕ), (22 : ℕ), (23 : ℕ)]) (0 : ℕ)).testBit ↑x3 = Bool.true) ∧
    Monotone2 D ∧ ReadsBack 44 D ∧ D.size ≤ 121 ∧
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, i < 44 + D.size) ∧
    ∀ (x5 : Fin (42 : ℕ) → Bool),               have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;              
      let xs := List.ofFn (fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7)
      g.op.eval (g.inputs.map fun i => (D.wires xs).getD i false) = true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) :
    ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     (have x5 : List ℕ := if x1 = (1 : Fin (42 : ℕ)) then [(81788948 : ℕ), (0 : ℕ), (4398145077304 : ℕ), (0 : ℕ), (4398077984768 : ℕ), (4398059094016 : ℕ), (4398256226304 : ℕ), (4406653222912 : ℕ)] else if x1 = (21 : Fin (42 : ℕ)) then [(71303174 : ℕ), (4398126202900 : ℕ), (4398067482760 : ℕ)] else [(10485770 : ℕ), (4398258323484 : ℕ), (0 : ℕ), (4402383429648 : ℕ)];       (x5.getD (List.idxOf ↑x2 [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (21 : ℕ), (22 : ℕ), (23 : ℕ)]) (0 : ℕ)).testBit ↑x3 = Bool.true) ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧           x4.size ≤ (122 : ℕ) ∧             ∀ (x5 : Fin (42 : ℕ) → Bool),               have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;               x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  obtain ⟨a, b, c, D, g, first, menu, mono, earlier, size, op, fan, args, fits⟩ := search
  obtain ⟨E, legal, past, lastSize, agrees⟩ := append 44 D g mono earlier op fan args
  refine ⟨a, b, c, E, first, menu, legal, past, ?_, ?_⟩
  · omega
  · intro x
    dsimp only
    rw [agrees _ (by simp only [List.length_ofFn])]
    exact fits x
