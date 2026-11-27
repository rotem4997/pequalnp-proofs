import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Before the first true AND, a true operand traces through OR gates to a true input bit.
-- An AND with no operands needs no true input bits.
-- The sparse bound therefore only needs the empty set, the singletons and the pairs
-- from the ten designated input positions.
theorem PEqualNP.Outside.R_meta_1894_1
    (smallSupport : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      let active := fun (X : Finset (Fin n)) => ∃ j g,
        C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun i => decide (i ∈ X))).getD (n + j) false = true
      ∀ X : Finset (Fin n), active X → ∃ Y ⊆ X, Y.card ≤ 2 ∧ active Y)
    (boundSparse : ∀ (C : Circuit) (Y : Finset (Fin 42)), Monotone2 C → C.size ≤ 124 →
      Y.card ≤ 2 → (∀ v ∈ Y, v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) →
      (∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        (C.wires (List.ofFn fun i => decide (i ∈ Y))).getD (42 + j) false = true) →
      ∃ x : Fin 42 → Bool, ¬ (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42,
        (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x u = true ∧ x v = true)) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  intro C hmono hsize hactive
  let X : Finset (Fin 42) := Finset.univ.filter
    (fun v => v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))
  have he : (fun i : Fin 42 => decide (i ∈ X)) =
      (fun i : Fin 42 => decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))) := by
    funext i
    simp [X]
  have hx : ∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      (C.wires (List.ofFn fun i => decide (i ∈ X))).getD (42 + j) false = true := by
    rw [he]
    exact hactive
  obtain ⟨Y, hYX, hCard, hY⟩ := smallSupport 42 C hmono X hx
  exact boundSparse C Y hmono hsize hCard (fun v hv => (Finset.mem_filter.mp (hYX hv)).2) hY
