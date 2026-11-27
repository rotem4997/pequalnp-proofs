import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The positive tests are single incident pairs.
-- In a negative test, each vertex is selected exactly when it avoids the selected vertices.
theorem PEqualNP.Outside.R_meta_1894_2 :
  (let E := fun (u v : Fin 42) =>
      u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
    let Closed := fun (x : Fin 42 → Bool) =>
      ∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)
    ∀ x, Closed x ↔ (∀ u v, x u = true → x v = true → ¬ E u v) ∧ (∀ u, x u = false → ∃ v, x v = true ∧ (E u v ∨ E v u))) →
  (let E := fun (u v : Fin 42) =>
      u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
    let Closed := fun (x : Fin 42 → Bool) =>
      ∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)
    ∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
    (∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      (C.wires (List.ofFn fun w : Fin 42 =>
        decide (w.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)))).getD (42 + j) false = true) →
    (∀ u v, E u v → C.eval (List.ofFn (fun w : Fin 42 => decide (w = u ∨ w = v))) = true) →
    (∀ x, Closed x → C.eval (List.ofFn x) = false) → False) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  intro negatives testBound C hmono hsize active
  by_contra h
  let E := fun (u v : Fin 42) =>
      u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  have agrees (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by
    by_contra bad
    exact h ⟨x, bad⟩
  refine testBound C hmono hsize active (fun u v e => ?_) (fun x hx => ?_)
  · exact (agrees (fun w : Fin 42 => decide (w = u ∨ w = v))).mpr ⟨u, v, e, by simp, by simp⟩
  · apply Bool.eq_false_of_not_eq_true
    rintro yes
    obtain ⟨u, v, e, hu, hv⟩ := (agrees x).mp yes
    exact ((negatives x).mp hx).1 u v hu hv e
