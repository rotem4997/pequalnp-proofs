import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2303_2
    (front : ∀ (n : Nat) (C : Circuit), FanInTwo C → 0 < C.size →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
        ((∃ (i : Fin (n+1)) (flip : Bool), ∀ xs : List Bool, xs.length = n →
          C.eval xs = D.eval (xs ++ [flip != xs.getD i.val false])) ∨
        (∃ (i j : Fin n) (disj : Bool), i < j ∧ ∀ xs : List Bool, xs.length = n →
          C.eval xs = D.eval (xs ++ [if disj then xs.getD i.val false || xs.getD j.val false
            else xs.getD i.val false && xs.getD j.val false]))))
    (unary : let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
     let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
     ∀ (D : Circuit), FanInTwo D → D.size = 13 → ∀ (i : Fin 11) (flip : Bool),
       ∃ x : Fin 9 → Bool, D.eval (row x ++ [flip != (row x).getD i.val false]) ≠ f x)
    (binary : let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
     let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
     ∀ (D : Circuit), FanInTwo D → D.size = 13 → ∀ (i j : Fin 10) (disj : Bool), i < j →
       ∃ x : Fin 9 → Bool, D.eval (row x ++ [if disj then (row x).getD i.val false || (row x).getD j.val false
         else (row x).getD i.val false && (row x).getD j.val false]) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x4 (0 : Fin (9 : ℕ)) = Bool.true ∨ x4 (6 : Fin (9 : ℕ)) = Bool.false → x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → (∀ (x7 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))]) = x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))])) → (14 : ℕ) ≤ x5.size) → ∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.false ∧ x6 (6 : Fin (9 : ℕ)) = Bool.true ∧ x1.eval (List.ofFn x6 ++ [Bool.true]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C fan size good _
  by_contra! no
  let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
  let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have allRows (x : Fin 9 → Bool) : C.eval (row x) = f x := by
    cases h0 : x 0 <;> cases h6 : x 6
    · simpa [row,h0,h6,f] using good x (Or.inr h6)
    · simpa [row,h0,h6,f] using no x h0 h6
    · simpa [row,h0,h6,f] using good x (Or.inl h0)
    · simpa [row,h0,h6,f] using good x (Or.inl h0)
  obtain ⟨D,hd,hs,hfront⟩ := front 10 C fan (by omega)
  have hdsize : D.size = 13 := by omega
  rcases hfront with ⟨i,b,rep⟩ | ⟨i,j,b,hij,rep⟩
  · obtain ⟨x,hx⟩ := unary D hd hdsize i b
    exact hx ((rep (row x) (by simp [row])).symm.trans (allRows x))
  · obtain ⟨x,hx⟩ := binary D hd hdsize i j b hij
    exact hx ((rep (row x) (by simp [row])).symm.trans (allRows x))
