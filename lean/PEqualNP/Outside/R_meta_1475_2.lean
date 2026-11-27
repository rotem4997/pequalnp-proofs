import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Treat the first two OR outputs as additional raw wires for the remaining gates.
-- The first pair represents the same-side, incident, or nonincident case.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1475_2 :
    (∃ (j : Fin 42) (a b : Fin 43) (D : Circuit),
      (j = 1 ∨ j = 21 ∨ j = 22) ∧ a < b ∧
      (a, b) ≠ (0, Fin.castSucc j) ∧
      (b = Fin.last 42 → a ≠ 0 ∧ a ≠ Fin.castSucc j) ∧
      (∀ i : Fin 42, ([0, j.val, a.val, b.val] : List ℕ).count i.val = 1 →
        ∃ g ∈ D.gates, i.val ∈ g.inputs) ∧
      Monotone2 D ∧ NestedCover.ReadsBack 44 D ∧ D.size ≤ 122 ∧
      ∀ x : Fin 42 → Bool,
        let y := Fin.lastCases (x 0 || x j) x
        D.eval (List.ofFn (Fin.lastCases (y a || y b) y)) = true ↔
          ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
            x u = true ∧ x v = true) →
    (∀ (j : Fin 42) (a b : Fin 43) (D : Circuit),
      Monotone2 D → NestedCover.ReadsBack 44 D →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 2 ∧
        ∀ x : Fin 42 → Bool,
          let y := Fin.lastCases (x 0 || x j) x
          C.eval (List.ofFn x) = D.eval (List.ofFn (Fin.lastCases (y a || y b) y))) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro search materialize
  obtain ⟨j, a, b, D, _, _, _, _, _, hMon, hBack, hSize, hEval⟩ := search
  obtain ⟨C, cMon, cSize, eval⟩ := materialize j a b D hMon hBack
  have incidence : ∀ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ↔
      (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) := by decide +kernel
  refine ⟨C, cMon, cSize.trans (Nat.add_le_add_right hSize 2), ?_⟩
  intro x
  rw [eval]
  simpa only [incidence] using hEval x
