import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1924_1
    (normalize : ∀ C : Circuit, ∃ D : Circuit,
      D.size = C.size ∧
      (Monotone2 C → Monotone2 D) ∧
      (FanInTwo C → FanInTwo D) ∧
      D.output ≤ 24 ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) ∧
      ∀ xs : List Bool, xs.length + C.size ≤ 24 →
        D.wires xs = C.wires xs ∧ D.eval xs = C.eval xs ∧
        (C.wires xs).length = xs.length + C.size)
    (finite : ∀ C D : Circuit,
      C.output ≤ 24 → D.output ≤ 24 →
      (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      C.size + D.size ≤ 13 → Monotone2 C → FanInTwo D →
      ¬ (∀ x : Fin 9 → Bool,
        let w := C.wires (List.ofFn x ++ [x 0 || x 4])
        D.eval (w ++ [!w.getD C.output false]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
           (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
           (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
           (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))) :
    ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.FanInTwo x2 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := x1.wires (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]);           x2.eval (x6 ++ [!x6.getD x1.output Bool.false]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size + x2.size := by
  intro C D hC hD heval
  by_contra hlarge
  have hsmall : C.size + D.size ≤ 13 := by omega
  obtain ⟨C', hCs, hCm, _, hCo, hCi, hCsem⟩ := normalize C
  obtain ⟨D', hDs, _, hDf, hDo, hDi, hDsem⟩ := normalize D
  apply finite C' D' hCo hDo hCi hDi (by omega) (hCm hC) (hDf hD)
  intro x
  let xs : List Bool := List.ofFn x ++ [x 0 || x 4]
  have hxs : xs.length = 10 := by simp [xs]
  have hbudget : xs.length + C.size ≤ 24 := by omega
  obtain ⟨hwire, hout, hlen⟩ := hCsem xs hbudget
  change D'.eval (C'.wires xs ++ [!C'.eval xs]) = _
  rw [hwire, hout]
  have hnext : (C.wires xs ++ [!C.eval xs]).length + D.size ≤ 24 := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [(hDsem (C.wires xs ++ [!C.eval xs]) hnext).2.1]
  exact heval x
