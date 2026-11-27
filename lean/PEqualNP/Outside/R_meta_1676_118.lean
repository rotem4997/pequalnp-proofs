import PEqualNP.Defs

-- The tens and units digits of each edge code are its two vertex labels.
-- Fixing vertices 0 and 4 to false leaves seven inputs. In each slice with
-- one of them true, selected uses of at most two wires may be set to true.
theorem PEqualNP.Outside.R_meta_1676_118
    (structure_or_smaller : let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) →
    PEqualNP.MetaComplexity.circuitFun 9 C = f → C.size ≤ 15 → PEqualNP.MetaComplexity.HasCircuitSize 9 f 14 ∨ ∃ B : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo B ∧ B.size ≤ 11 ∧ PEqualNP.MetaComplexity.circuitFun 7 B = (fun y : Fin 7 → Bool => f ((0 : Fin 9).insertNth false ((3 : Fin 8).insertNth false y))) ∧
      ∀ t : Bool, ∃ (u v : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit),
      D.output = B.output + 1 ∧
      List.Forall₂ (fun g h => g.op = h.op ∧
        List.Forall₂ (fun j k => k = j + 1 ∨ k = 0 ∧ (j = u ∨ j = v))
          g.inputs h.inputs) B.gates D.gates ∧
      ∀ y : Fin 7 → Bool, D.eval (true :: List.ofFn y) = f ((0 : Fin 9).insertNth t ((3 : Fin 8).insertNth (!t) y)))
    (unrestricted : let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 f 14)
    (theta_lower : let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun y : Fin 7 → Bool => f ((0 : Fin 9).insertNth false ((3 : Fin 8).insertNth false y))) s → 11 ≤ s)
    (no_three_slices : let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ¬ (∃ B : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo B ∧ B.size = 11 ∧ PEqualNP.MetaComplexity.circuitFun 7 B = (fun y : Fin 7 → Bool => f ((0 : Fin 9).insertNth false ((3 : Fin 8).insertNth false y))) ∧
      ∀ t : Bool, ∃ (u v : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit),
      D.output = B.output + 1 ∧
      List.Forall₂ (fun g h => g.op = h.op ∧
        List.Forall₂ (fun j k => k = j + 1 ∨ k = 0 ∧ (j = u ∨ j = v))
          g.inputs h.inputs) B.gates D.gates ∧
      ∀ y : Fin 7 → Bool, D.eval (true :: List.ofFn y) = f ((0 : Fin 9).insertNth t ((3 : Fin 8).insertNth (!t) y)))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let graph := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have same : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = graph := by decide +kernel
  intro C fan first computes
  by_contra! small
  rcases structure_or_smaller C fan first (computes.trans same) (by omega) with dead | ⟨B,hB,limit,base,lifts⟩
  · exact unrestricted dead
  · have lower := theta_lower B.size ⟨B,hB,le_rfl,congrFun base⟩
    exact no_three_slices ⟨B,hB,by omega,base,lifts⟩
