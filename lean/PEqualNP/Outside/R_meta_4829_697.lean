import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_4829_697
    (move : let edge := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ (C : Circuit) (j : Fin C.size), FanInTwo C →
        (C.gates.get j).op = .not →
        (∀ k : Fin C.size, 4 ∈ (C.gates.get k).inputs → k = j) →
        circuitFun 9 C = edge →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = !(x 4)) ∧
          circuitFun 9 D = edge)
    (first : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (andCase : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin x1.size), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x6 : Fin x1.size), (4 : ℕ) ∈ (x1.gates.get x6).inputs ↔ x6 = x2) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin x1.size), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (x1.gates.get x2).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x6 : Fin x1.size), (4 : ℕ) ∈ (x1.gates.get x6).inputs ↔ x6 = x2) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) := by
  intro C j fan size nonOr unique
  have kind : (C.gates.get j).op = .and ∨ (C.gates.get j).op = .or ∨
      (C.gates.get j).op = .not := by
    simpa using (fan (C.gates.get j) (List.get_mem _ _)).1
  rcases kind with hand | hor | hnot
  · exact andCase C j fan size hand unique
  · exact (nonOr hor).elim
  · intro good
    have same : (fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) = (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) := by
      funext x
      simp only [List.any_cons,List.any_nil,Prod.fst,Prod.snd,Bool.or_false,Bool.or_assoc]
    obtain ⟨D,df,ds,seed,computes⟩ := move C j fan hnot
      (fun k => (unique k).mp) (good.trans same)
    have bound := first D df seed (computes.trans same.symm)
    omega
