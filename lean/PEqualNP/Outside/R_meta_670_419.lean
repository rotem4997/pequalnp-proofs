import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_670_419
    (normal : let f : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ∀ C : Circuit, FanInTwo C → circuitFun 9 C = f →
    ∃ (D : Circuit) (k : GateOp) (a b : Fin 9), FanInTwo D ∧ D.size+1 ≤ C.size ∧
      ((k = .not ∧ a ∈ ([0,4] : List (Fin 9))) ∨
       ((k = .and ∨ k = .or) ∧ (a,b) ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)))) ∧
      (∀ g∈D.gates, (∀ j∈g.inputs, j < 9) → (k = .and ∨ g.op ≠ .and) ∧ (k ≠ .or ∨ g.op ≠ .not)) ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [k.eval [x a,x b]]) = f x)
    (conjunction : ∀ p∈([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
    ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x p.1 && x p.2]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x)
    (negation : ∀ a∈([0,4] : List (Fin 9)), ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
    (∀ g∈D.gates, (∀ j∈g.inputs, j < 9) → g.op ≠ .and) →
    ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!(x a)]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x)
    (disjunction : ∀ p∈([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
    (∀ g∈D.gates, (∀ j∈g.inputs, j < 9) → g.op ≠ .and ∧ g.op ≠ .not) →
    ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C,hf,small,eq⟩
  obtain ⟨D,k,a,b,df,ds,shape,ops,ev⟩ := normal C hf (funext eq)
  have bound : D.size ≤ 14 := by omega
  rcases shape with ⟨rfl,mem⟩ | ⟨rfl|rfl,mem⟩
  · obtain ⟨x,ne⟩ := negation a mem D df bound (fun g h p => ((ops g h p).1).resolve_left (by intro e; cases e))
    exact ne (ev x)
  · obtain ⟨x,ne⟩ := conjunction (a,b) mem D df bound
    have ex := ev x
    change D.eval (List.ofFn x ++ [x a && (x b && true)]) = _ at ex
    exact ne (by simpa only [Bool.and_true] using ex)
  · obtain ⟨x,ne⟩ := disjunction (a,b) mem D df bound (fun g h p =>
      ⟨((ops g h p).1).resolve_left (by intro e; cases e),((ops g h p).2).resolve_left (by simp)⟩)
    have ex := ev x
    change D.eval (List.ofFn x ++ [x a || (x b || false)]) = _ at ex
    exact ne (by simpa only [Bool.or_false] using ex)
