import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_584 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 1]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 16]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 21]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 17]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 23]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 15]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 8]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 26]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], output := 29 } :
      PEqualNP.CircuitLowerBounds.Circuit) →
    PEqualNP.MetaComplexity.Monotone2 C ∧
    C.size = 20 ∧
    (∃ A : Finset ℕ, A.card = 13 ∧
      ∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
        C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 10, (u.val, v.val) ∈
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (4, 9), (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true)) := by
  intro C hC
  subst C
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · refine ⟨{0, 1, 2, 3, 5, 6, 7, 8, 12, 14, 15, 18, 19}, by decide, ?_⟩
    intro j
    by_cases h : j < 20
    · interval_cases j <;> simp
    · rw [List.getElem?_eq_none (by change 20 ≤ j; omega)]
      simp
      omega
  · intro x
    let edges : List (Fin 10 × Fin 10) :=
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
        (3, 8), (4, 9), (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)]
    have edges_spec :
        edges.any (fun p => x p.1 && x p.2) = true ↔
          ∃ u v : Fin 10, (u.val, v.val) ∈ edges.map (fun p => (p.1.val, p.2.val)) ∧
            x u = true ∧ x v = true := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨⟨u, v⟩, huv, hbits⟩
        exact ⟨u, v, List.mem_map_of_mem huv, Bool.and_eq_true_iff.mp hbits⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp huv
        have ha : a = u := Fin.ext (congrArg Prod.fst heq)
        have hb : b = v := Fin.ext (congrArg Prod.snd heq)
        subst a
        subst b
        exact ⟨(u, v), hab, Bool.and_eq_true_iff.mpr ⟨hu, hv⟩⟩
    change _ ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ edges.map (fun p => (p.1.val, p.2.val)) ∧
      x u = true ∧ x v = true
    rw [← edges_spec]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false, edges,
      Bool.and_eq_true, Bool.or_eq_true]
    grind
