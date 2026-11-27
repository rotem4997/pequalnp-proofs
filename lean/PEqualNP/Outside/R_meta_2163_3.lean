import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2163_3
    (floor_bound : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      15 ≤ D.size)
    (sparse_tail : ∀ C : Circuit, FanInTwo C → C.size = 15 →
      (∀ D : Circuit, FanInTwo D → circuitFun 9 D = circuitFun 9 C → 15 ≤ D.size) →
      C.gates.countP (fun g => g.op.eval [false]) = 2 →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      ∃ (D : Circuit), FanInTwo D ∧ D.size = 14 ∧
        D.gates.countP (fun g => g.op.eval [false]) = 2 ∧
        (∀ j ∈ [0,1,2,4,7,8], D.gates.countP (fun g => g.inputs.contains j) ≤ 1) ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = circuitFun 9 C x)
    (separating_input : ∀ D : Circuit, FanInTwo D → D.size = 14 →
      D.gates.countP (fun g => g.op.eval [false]) = 2 →
      (∀ j ∈ [0,1,2,4,7,8], D.gates.countP (fun g => g.inputs.contains j) ≤ 1) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 ≠ x4 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan nots first computes
  by_contra small
  have same : circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) := by
    funext x
    simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using congrFun computes x
  have size := floor_bound C fan same
  obtain ⟨a,b,diff,ha,hb,rest⟩ := nots
  let isNot := fun g : Gate => g.op.eval [false]
  have test (i : Fin C.gates.length) :
      isNot (C.gates.get i) = true ↔ (C.gates.get i).op = .not := by
    have legal : (C.gates.get i).op = .and ∨ (C.gates.get i).op = .or ∨ (C.gates.get i).op = .not :=
      (fan _ (List.get_mem C.gates i)).1
    change (C.gates.get i).op.eval [false] = true ↔ _
    rcases legal with h | h | h <;> rw [h]
    · change (false = true ↔ GateOp.and = GateOp.not)
      constructor <;> intro impossible <;> cases impossible
    · change (false = true ↔ GateOp.or = GateOp.not)
      constructor <;> intro impossible <;> cases impossible
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
  have indices : Finset.univ.filter (fun i : Fin C.gates.length => isNot (C.gates.get i) = true) = {a,b} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, test]
    exact ⟨rest i, fun h => h.elim (fun e => e ▸ ha) (fun e => e ▸ hb)⟩
  have count := List.countP_ofFn C.gates.get isNot
  rw [List.ofFn_get, indices] at count
  obtain ⟨D,hf,hs,hn,hr,he⟩ := sparse_tail C fan (by omega)
    (fun D hd hD => floor_bound D hd (hD.trans same)) (by simpa [diff] using count) first same
  obtain ⟨x,hx⟩ := separating_input D hf hs hn hr
  exact hx ((he x).trans (congrFun same x))
