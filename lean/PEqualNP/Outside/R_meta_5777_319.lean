import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.EdgeOwnership

-- At the minimum size, neither input of a gate can substitute for the gate on all extremal tests.
-- The remaining synthesis therefore has private positive tests at OR gates and private vetoes at AND gates.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5777_319
    (irreducible : let w (C : Circuit) (i : ℕ) (x : Fin 14 → Bool) :=
        (C.wires (List.ofFn x)).getD i false
      let rigid (C : Circuit) := ∀ (j : ℕ) (g : Gate) (a b : ℕ),
        C.gates[j]? = some g → (g.inputs = [a,b] ∨ g.inputs = [b,a]) →
        (g.op = .or → ∃ p l : Fin 7, p ∈ fanoLines l ∧
          let x := pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l)
          w C a x = false ∧ w C b x = true) ∧
        (g.op = .and → ∃ x : Fin 14 → Bool,
          Maximal (fun y : Fin 14 → Bool => C.eval (List.ofFn y) = false) x ∧
          w C a x = true ∧ w C b x = false)
      ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
        ComputesIncidence fanoLines C → rigid C)
    (search : let w (C : Circuit) (i : ℕ) (x : Fin 14 → Bool) :=
        (C.wires (List.ofFn x)).getD i false
      let rigid (C : Circuit) := ∀ (j : ℕ) (g : Gate) (a b : ℕ),
        C.gates[j]? = some g → (g.inputs = [a,b] ∨ g.inputs = [b,a]) →
        (g.op = .or → ∃ p l : Fin 7, p ∈ fanoLines l ∧
          let x := pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l)
          w C a x = false ∧ w C b x = true) ∧
        (g.op = .and → ∃ x : Fin 14 → Bool,
          Maximal (fun y : Fin 14 → Bool => C.eval (List.ofFn y) = false) x ∧
          w C a x = true ∧ w C b x = false)
      ∀ (C : Circuit) (p l : Fin 7), C.size ≤ 27 → IsAO2 14 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) → ComputesIncidence fanoLines C → rigid C →
        p ∈ fanoLines l → 2 ≤ C.lineDeg 14 {p.val} → 2 ≤ C.lineDeg 14 {7+l.val} → False) :
    (have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x4.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 → (∀ x9 ∈ x4.gates, x9.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x4 → x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x14 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x14 ∧ x14.leaves ≤ (28 : ℕ) ∧ (∀ (x15 : Fin (14 : ℕ) → Bool), x14.eval x15 = x4.eval (List.ofFn x15)) ∧ (2 : ℕ) ≤ x3 (↑x5) x14 ∧ (2 : ℕ) ≤ x3 ((7 : ℕ) + ↑x6) x14) := by
  dsimp only
  intro C p l small ao nd correct flag pd ld
  exact (search C p l small ao nd correct (irreducible C small ao correct) flag pd ld).elim
