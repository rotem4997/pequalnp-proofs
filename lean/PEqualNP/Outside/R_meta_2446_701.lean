import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2446_701
    (canonical : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 → ∃ (t : Fin 16) (ops : Fin t → Fin 3) (src : Fin t → Option (Fin 25) × Option (Fin 25)) (out : Fin 25), let D := ({ gates := List.ofFn (fun i : Fin t => { op := if ops i = 0 then PEqualNP.CircuitLowerBounds.GateOp.and else if ops i = 1 then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ((src i).1.toList ++ (src i).2.toList).map Fin.val }), output := out.val } : PEqualNP.CircuitLowerBounds.Circuit); (∀ x : Fin 9 → Bool, D.wires (List.ofFn x) = C.wires (List.ofFn x)) ∧ PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.circuitFun 9 C)
    (finite_search : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∀ (t : Fin 16) (ops : Fin t → Fin 3) (src : Fin t → Option (Fin 25) × Option (Fin 25)) (out : Fin 25), let D := ({ gates := List.ofFn (fun i : Fin t => { op := if ops i = 0 then PEqualNP.CircuitLowerBounds.GateOp.and else if ops i = 1 then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ((src i).1.toList ++ (src i).2.toList).map Fin.val }), output := out.val } : PEqualNP.CircuitLowerBounds.Circuit); (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x p.1 || x p.2)) → (PEqualNP.MetaComplexity.circuitFun 9 D = fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 x1.1 || x5 x1.2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x3.size := by
  intro p hp C hC hfirst hfun
  by_contra hsmall
  have hsize : C.size ≤ 15 := by omega
  obtain ⟨t, ops, src, out, hwires, hsem⟩ := canonical C hC hsize
  apply finite_search p hp t ops src out
  · intro x
    rw [hwires x]
    exact hfirst x
  · rw [hsem, hfun]
    funext x
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
