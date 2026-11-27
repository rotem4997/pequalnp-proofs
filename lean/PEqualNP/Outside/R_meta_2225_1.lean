import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Formula rigidity at the Fano plane, cut into a statement about read counts and a general lemma.
-- reads: in a formula of at most 27 gates for the incidence function, at every incident pair the
-- point or the line is read by at most one gate. This is the combinatorial core.
-- degree: an input read by at most one gate of a formula has line-degree at most 1.
theorem PEqualNP.Outside.R_meta_2225_1
    (reads : ∀ (C : Circuit) (p l : Fin 7), (C.size ≤ 27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup →
      (p = l ∨ p = l + 1 ∨ p = l + 3) →
      (C.gates.flatMap Gate.inputs).count p.val ≤ 1 ∨ (C.gates.flatMap Gate.inputs).count (7 + l.val) ≤ 1)
    (degree : ∀ (C : Circuit) (v : ℕ), v < 14 → (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) →
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup →
      (C.gates.flatMap Gate.inputs).count v ≤ 1 → HasLineDegree 14 {v} C 1)
    : have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x3 x4 → x1 x5 x6 → PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {↑x5} x4 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {(7 : ℕ) + ↑x6} x4 (1 : ℕ) := by
  intro inc valid tree C p l hvalid htree hinc
  rcases reads C p l hvalid htree hinc with h | h
  · exact Or.inl (degree C p.val (by omega) hvalid.2.1 htree h)
  · exact Or.inr (degree C (7 + l.val) (by omega) hvalid.2.1 htree h)
