import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.LowMerge

-- Trace the output through OR gates to a fixed family of AND gates.
-- Every member rejects every quadrangle, and together they cover all 52 incidences.
theorem PEqualNP.Outside.R_meta_2588_1
    (sparse : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 26 C →
    (∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l → C.eval
      (List.ofFn (fun k : Fin 13 => decide (k = p)) ++ List.ofFn (fun k : Fin 13 => decide (k = l))) = true) →
    (∀ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
      C.eval (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q))) = false) →
    38 ≤ C.size)
    (typeCounts : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 26 C →
    (∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l → C.eval
      (List.ofFn (fun k : Fin 13 => decide (k = p)) ++ List.ofFn (fun k : Fin 13 => decide (k = l))) = true) →
    (∀ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
      C.eval (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q))) = false) →
    8 ≤ PEqualNP.ReadTwo.nAnd C ∧ 18 ≤ PEqualNP.ReadTwo.nOr C)
    (frontier :
      let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q));
      ∀ C : Circuit, IsAO2 26 C →
        (∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) →
        (∃ x : List Bool, x.length = 26 ∧ C.eval x = true) →
        ∃ J : Finset ℕ, (∀ j ∈ J, j < C.size ∧ (gateAt C j).op = .and ∧
          ∀ Q ∈ quadrangles singerLines3, (C.wires (N Q)).getD (26+j) false = false) ∧
          2 * J.card ≤ C.size + 1 ∧ ∀ x : List Bool, x.length = 26 →
            (C.eval x = true ↔ ∃ j ∈ J, (C.wires x).getD (26+j) false = true))
    (obstruction :
      let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q));
      let S := quadrangles singerLines3;
      ∀ (C : Circuit) (J : Finset ℕ),
        let G := gateAt C;
        let W := wireVal C;
        IsAO2 26 C → 38 ≤ C.size → C.size < 64 →
        (8 ≤ PEqualNP.ReadTwo.nAnd C ∧ 18 ≤ PEqualNP.ReadTwo.nOr C) →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        2 ≤ andPairs 26 C →
        (∀ j < C.size, (G j).op = .and → ∀ i ∈ (G j).inputs,
          ∃ Q ∈ S, W (N Q) (26+j) ≠ W (N Q) i) →
        (∀ j ∈ J, j < C.size ∧ (G j).op = .and ∧ ∀ Q ∈ S, W (N Q) (26+j) = false) →
        2 * J.card ≤ C.size + 1 →
        (∀ x : List Bool, x.length = 26 → (C.eval x = true ↔ ∃ j ∈ J, W x (26+j) = true)) →
        (∀ p l : Fin 13, p ∈ singerLines3 l → ∃ j ∈ J, W (pointLineInput 13 13 p l) (26+j) = true) →
        False) :
    let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        2 ≤ andPairs 26 C →
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
          (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) →
        (∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) →
        (∀ j < C.size, (gateAt C j).op = GateOp.and →
          ∀ p ∈ (gateAt C j).inputs, ∃ Q ∈ quadrangles singerLines3,
            (C.wires (N Q)).getD (26+j) false ≠ (C.wires (N Q)).getD p false) →
        64 ≤ C.size := by
  intro N C ao distinct nested pos neg strict
  by_contra! small
  have lengthPair (p l : Fin 13) : (pointLineInput 13 13 p l).length = 26 := by
    change (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))).length = 26
    simp only [List.length_append, List.length_ofFn]
  obtain ⟨J, clean, budget, cover⟩ := frontier C ao neg
    ⟨pointLineInput 13 13 0 0, lengthPair 0 0, pos 0 0 (by decide)⟩
  apply obstruction C J ao (sparse C ao pos neg) small (typeCounts C ao pos neg) distinct nested strict clean budget cover
  intro p l edge
  exact (cover (pointLineInput 13 13 p l) (lengthPair p l)).mp (pos p l edge)
