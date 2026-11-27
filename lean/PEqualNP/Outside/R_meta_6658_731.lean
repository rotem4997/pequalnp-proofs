import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_6658_731
    (prepend : ∀ C : Circuit, C.output < 16 + C.size →
      (∀ j (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
          g.inputs = [a, b] ∧ a ≠ b ∧ a < 16 + j ∧ b < 16 + j) →
      ∃ D : Circuit, D.size ≤ C.size + 2 ∧ D.output < 14 + D.size ∧ 15 < 14 + D.size ∧
        (∀ j (g : Gate), D.gates[j]? = some g →
          (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
            g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
        ∀ x : Fin 14 → Bool,
          D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 7 || x 13, (x 7 || x 13) || x 11]) ∧
          (D.wires (List.ofFn x)).getD 15 false = ((x 7 || x 13) || x 11))
    (seeded : ∃ C : Circuit, C.size ≤ 22 ∧ C.output < 16 + C.size ∧
      (∀ j (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
          g.inputs = [a, b] ∧ a ≠ b ∧ a < 16 + j ∧ b < 16 + j) ∧
      ∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x ++ [x 7 || x 13, (x 7 || x 13) || x 11]) = true ↔
          ∃ p l : Fin 7, p ≠ 0 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (24 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 < (14 : ℕ) + x1.size ∧ x3 < (14 : ℕ) + x1.size ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), ((x1.wires (List.ofFn x4)).getD x2 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ≠ (0 : Fin (7 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) ∧ ((x1.wires (List.ofFn x4)).getD x3 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)), ((0 : Fin (7 : ℕ)) = x5 ∨ (0 : Fin (7 : ℕ)) = x5 + (1 : Fin (7 : ℕ)) ∨ (0 : Fin (7 : ℕ)) = x5 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.natAdd (7 : ℕ) x5) = Bool.true) := by
  obtain ⟨C, hsize, hout, hnormal, hinc⟩ := seeded
  obtain ⟨D, hDsize, hDout, hseed, hDnormal, hagree⟩ := prepend C hout hnormal
  refine ⟨D, by omega, hDnormal, D.output, 15, hDout, hseed, fun x => ⟨?_, ?_⟩⟩
  · change D.eval (List.ofFn x) = true ↔ _
    rw [(hagree x).1]
    exact hinc x
  · rw [(hagree x).2]
    simp [Fin.exists_fin_succ, Bool.or_eq_true, Bool.or_assoc, or_comm]
