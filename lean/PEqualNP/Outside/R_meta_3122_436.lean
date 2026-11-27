import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- A suffix that succeeded would give a genuine unsigned pair, then an orbit
-- representative with at most one paid NOT. Pair codes are 9*i+j.
theorem PEqualNP.Outside.R_meta_3122_436
  (genuine : let F := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
    let P := fun (i j : Fin 9) (C : Circuit) => ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x i || x j]) = F x
    ∀ (s : List Nat) (C : Circuit), s.length ≤ 2 → FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [!x 0]; C.eval (w ++ [GateOp.or.eval (s.map (fun i => w.getD i false))]) = F x) →
      ∃ i j, i < j ∧ P i j C)
  (orbit : let F := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
    let P := fun (i j : Fin 9) (C : Circuit) => ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x i || x j]) = F x
    ∀ i j C, i < j → FanInTwo C → C.size ≤ 13 → P i j C → ∃ (i j : Fin 9) (D : Circuit), 9*i.val+j.val ∈ ([1,2,3,4,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61] : List Nat) ∧ FanInTwo D ∧ D.size ≤ 13 ∧ P i j D)
  (notBudget : let F := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
    let P := fun (i j : Fin 9) (C : Circuit) => ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x i || x j]) = F x
    ∀ i j C, FanInTwo C → C.size ≤ 13 → P i j C → (C.gates.filter (fun g => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)).length ≤ 1)
  (lower : let F := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
    let P := fun (i j : Fin 9) (C : Circuit) => ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x i || x j]) = F x
    ∀ (i j : Fin 9) (C : Circuit), 9*i.val+j.val ∈ ([1,2,3,4,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61] : List Nat) → FanInTwo C → C.size ≤ 13 → (C.gates.filter (fun g => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)).length ≤ 1 → ¬P i j C) :
  ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro s len C hf hs _
  by_contra! e
  let F := fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  have same (x : Fin 9 → Bool) : F x = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
    simp only [F,List.any_cons,List.any_nil,Bool.or_false]; ac_rfl
  obtain ⟨i,j,ij,ok⟩ := genuine s C len hf hs (fun x => (not_ne_iff.mp (e x)).trans (same x).symm)
  obtain ⟨a,b,D,rep,df,ds,ok'⟩ := orbit i j C ij hf hs ok
  exact lower a b D rep df ds (notBudget a b D df ds ok') ok'
