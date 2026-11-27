import Mathlib
import PEqualNP.Defs

private lemma edgeCons587 (x : Fin 10 → Bool) (a b : ℕ) (ha : a < 10) (hb : b < 10) (es : List (ℕ × ℕ)) :
    (∃ u v : Fin 10, (u.val, v.val) ∈ (a, b) :: es ∧ x u = true ∧ x v = true) ↔
    (x ⟨a, ha⟩ = true ∧ x ⟨b, hb⟩ = true) ∨
      ∃ u v : Fin 10, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a, ha⟩ from Fin.ext h1) ▸ hu, (show v = ⟨b, hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u, v, h, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, h, hu, hv⟩)
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, List.mem_cons_self, h1, h2⟩
    · exact ⟨u, v, List.mem_cons_of_mem _ h, hu, hv⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_587 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], output := 29 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 20 ∧ (∃ A : Finset ℕ, A.card = 14 ∧ ∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · refine ⟨{0, 1, 2, 3, 4, 5, 6, 8, 9, 14, 16, 17, 18, 19}, by decide, ?_⟩
    intro j
    by_cases hj : j < 20
    · interval_cases j <;> simp
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)]
      simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_and,
        exists_false, iff_false]
      omega
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons587 x 0 1 (by decide) (by decide)]
    rw [edgeCons587 x 1 2 (by decide) (by decide)]
    rw [edgeCons587 x 2 3 (by decide) (by decide)]
    rw [edgeCons587 x 3 4 (by decide) (by decide)]
    rw [edgeCons587 x 4 0 (by decide) (by decide)]
    rw [edgeCons587 x 0 5 (by decide) (by decide)]
    rw [edgeCons587 x 1 6 (by decide) (by decide)]
    rw [edgeCons587 x 2 7 (by decide) (by decide)]
    rw [edgeCons587 x 3 8 (by decide) (by decide)]
    rw [edgeCons587 x 4 9 (by decide) (by decide)]
    rw [edgeCons587 x 5 7 (by decide) (by decide)]
    rw [edgeCons587 x 6 8 (by decide) (by decide)]
    rw [edgeCons587 x 7 9 (by decide) (by decide)]
    rw [edgeCons587 x 8 5 (by decide) (by decide)]
    rw [edgeCons587 x 9 6 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    simp only [and_or_left, or_and_right]
    apply Iff.of_eq
    ac_rfl
