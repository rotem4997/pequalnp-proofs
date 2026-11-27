import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2551_24
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 14 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4]) = ([(0,1),(1,2),(2,3),(0,4),(3,4),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      C.eval (List.ofFn (fun i : Fin 9 => (24 : Nat).testBit i.val) ++ [false]) = false ∧
      (C.eval (List.ofFn (fun i : Fin 9 => (3 : Nat).testBit i.val) ++ [false]) = false ∨ C.eval (List.ofFn (fun i : Fin 9 => (33 : Nat).testBit i.val) ++ [false]) = false))
    (h2 : ∀ (rows : List Nat) (g : Nat → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ r ∈ rows, r < 1024) → PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 14 →
      (∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin 10 => r.testBit i.val)) = g r) →
      PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc 10 14 g rows))
    (h3 : ∀ k ∈ ([3,33] : List Nat), ¬ PEqualNP.Defs.LratEncoding.FormulaSat
      (PEqualNP.Defs.LratEncoding.enc 10 14 (fun r : Nat => [515,6,12,529,536,545,66,132,160,264,288,320].contains r) (24 :: k :: [515,6,12,529,536,545,42,562,66,581,104,628,132,138,160,713,720,773,264,788,288,320,897,914]))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ))]) = (fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) x3) → (15 : ℕ) ≤ x1.size := by
  intro C hm he
  by_contra hlt
  have hs : C.size ≤ 14 := by omega
  obtain ⟨h24, hor⟩ := h1 C hm hs he
  let b : List Nat := [515,6,12,529,536,545,42,562,66,581,104,628,132,138,160,713,720,773,264,788,288,320,897,914]
  let p := (fun r : Nat => [515,6,12,529,536,545,66,132,160,264,288,320].contains r)
  have good : ∀ r ∈ b,
      (List.ofFn (fun i : Fin 10 => r.testBit i.val)) =
        (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 4]) ∧
      (let x := fun i : Fin 9 => r.testBit i.val; ([(0,1),(1,2),(2,3),(0,4),(3,4),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) = p r := by
    decide +kernel
  have hbase : ∀ r ∈ b, C.eval (List.ofFn (fun i : Fin 10 => r.testBit i.val)) = p r := by
    intro r hr
    obtain ⟨hw, hv⟩ := good r hr
    rw [hw]
    exact (he _).trans hv
  have fin (k : Nat) (hk : k ∈ ([3,33] : List Nat))
      (hv : C.eval (List.ofFn (fun i : Fin 9 => (k : Nat).testBit i.val) ++ [false]) = false) : False := by
    apply h3 k hk
    apply h2 _ _ C _ hm hs
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h24
      rcases List.mem_cons.mp hr with rfl | hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> exact hv
      exact hbase _ hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> decide +kernel
  rcases hor with ha | ha
  · exact fin 3 (by decide) ha
  · exact fin 33 (by decide) ha
