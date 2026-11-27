import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3602_918 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size) →
    (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.IsMinimalCircuit n C → 0 < C.size →
  C.output + 1 = n + C.size ∧
  ∀ i, i + 1 < C.size →
    ∃ j : Fin C.gates.length, i < (j : ℕ) ∧ n + i ∈ (C.gates.get j).inputs) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → x1.size = (15 : ℕ) ∧ x1.output = (23 : ℕ) ∧ ∀ x5 < (14 : ℕ), ∃ (x7 : Fin x1.gates.length), x5 < ↑x7 ∧ (9 : ℕ) + x5 ∈ (x1.gates.get x7).inputs) := by
  intro lower structural C hfan heval hmax
  have hsize : C.size = 15 := Nat.le_antisymm hmax (lower C hfan heval)
  have hmin : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C := by
    refine ⟨hfan, ?_⟩
    intro D hD heq
    rw [hsize]
    exact lower D hD (heq.trans heval)
  have hpos : 0 < C.size := hsize.symm ▸ Nat.zero_lt_succ 14
  obtain ⟨hout, hread⟩ := structural 9 C hmin hpos
  have hout' : C.output + 1 = 23 + 1 := by simpa only [hsize] using hout
  refine ⟨hsize, Nat.add_right_cancel hout', ?_⟩
  intro i hi
  have hi' : i + 1 < 15 := Nat.succ_lt_succ hi
  exact hread i (hsize.symm ▸ hi')
