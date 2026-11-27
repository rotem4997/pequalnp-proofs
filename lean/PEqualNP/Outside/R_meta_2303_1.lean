import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2303_1
    (budget : ∀ (n : ℕ) (C : Circuit), FanInTwo C →
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      (D.output :: D.gates.flatMap Gate.inputs).countP (fun i => decide (i<n)) ≤ D.size+1 ∧
      ∀ xs : List Bool, xs.length=n → D.eval xs=C.eval xs)
    (single : let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
    let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
    ∀ (D : Circuit), (∀ x, D.eval (row x) = f x) →
      (D.output :: D.gates.flatMap Gate.inputs).countP (fun i => decide (i<10)) ≤ 15 →
      ∃ v : Fin 9, v ≠ 0 ∧ v ≠ 6 ∧ D.output ≠ v.val ∧ (D.gates.flatMap Gate.inputs).count v.val = 1)
    (extract : ∀ (n v : ℕ) (C : Circuit), v<n → FanInTwo C → C.output ≠ v →
    (C.gates.flatMap Gate.inputs).count v=1 →
    ∃ (D : Circuit) (cut : ℕ) (g : Gate), FanInTwo D ∧ D.size+1=C.size ∧
      n ≤ cut ∧ cut ≤ n+D.size ∧ (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 ∧ v ∈ g.inputs ∧
      (∀ h ∈ D.gates.take (cut-n), v ∉ h.inputs) ∧
      ∀ xs : List Bool, xs.length=n → C.eval xs = D.eval (xs.set v (g.op.eval (g.inputs.map (fun i => if i < cut then (D.wires xs).getD i false else false)))))
    (core : let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
    let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
    ∀ (v : Fin 9) (D : Circuit) (cut : ℕ) (g : Gate),
      v ≠ 0 → v ≠ 6 → FanInTwo D → D.size ≤ 13 → 10 ≤ cut → cut ≤ 10+D.size →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) → g.inputs.length ≤ 2 → v.val ∈ g.inputs →
      (∀ h ∈ D.gates.take (cut-10), v.val ∉ h.inputs) →
      ∃ x : Fin 9 → Bool, let xs := row x
        D.eval (xs.set v.val (g.op.eval (g.inputs.map (fun i => if i < cut then (D.wires xs).getD i false else false)))) ≠ f x)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x4 (0 : Fin (9 : ℕ)) = Bool.true ∨ x4 (6 : Fin (9 : ℕ)) = Bool.false → x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → (∀ (x7 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))]) = x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))])) → (14 : ℕ) ≤ x5.size) → ∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.false ∧ x6 (6 : Fin (9 : ℕ)) = Bool.true ∧ x1.eval (List.ofFn x6 ++ [Bool.true]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C fan size good _minimal
  by_contra! no
  let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
  let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have full (x : Fin 9 → Bool) : C.eval (row x) = f x := by
    cases h0 : x 0 <;> cases h6 : x 6
    · simpa [row,h0,h6,f] using good x (Or.inr h6)
    · simpa [row,h0,h6,f] using no x h0 h6
    · simpa [row,h0,h6,f] using good x (Or.inl h0)
    · simpa [row,h0,h6,f] using good x (Or.inl h0)
  obtain ⟨A,fanA,szA,reads,evalA⟩ := budget 10 C fan
  have len (x : Fin 9 → Bool) : (row x).length = 10 := by simp [row]
  have eqA (x : Fin 9 → Bool) : A.eval (row x) = f x := (evalA _ (len x)).trans (full x)
  obtain ⟨v,nz,ns,out,cnt⟩ := single A eqA (reads.trans (by omega))
  obtain ⟨D,cut,g,fd,sd,lo,hi,op,arity,mem,prior,eq⟩ :=
    extract 10 v.val A (by have := v.isLt; omega) fanA out cnt
  obtain ⟨x,fail⟩ := core v D cut g nz ns fd (by omega) lo hi op arity mem prior
  exact fail ((eq _ (len x)).symm.trans (eqA x))
