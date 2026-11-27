import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fix the appended wire to false and bypass its OR reader. The resulting
-- ordinary circuit agrees on both cubes where the appended AND is false.
-- Vertex four remains essential on these cubes; setting it false costs
-- a second gate and leaves the ten-edge subgraph with eight active inputs.
theorem PEqualNP.Outside.R_meta_2022_2
    (bypass : ∀ (n : ℕ) (a b : List Gate) (ins : List ℕ) (o : ℕ),
      n ∈ ins → let C : Circuit := ⟨a ++ ⟨GateOp.or,ins⟩ :: b,o⟩
      FanInTwo C → HasCircuitSize n (fun x => C.eval (List.ofFn x ++ [false])) (a.length + b.length))
    (restrict : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (v : Fin n),
      HasCircuitSize n F s →
      (∃ x, F (Function.update x v false) ≠ F (Function.update x v true)) →
      (∃ x y, F (Function.update x v false) ≠ F (Function.update y v false)) →
      HasCircuitSize n (fun x => F (Function.update x v false)) (s-1))
    (lower : ∀ s : ℕ, HasCircuitSize 9 (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) s → 13 ≤ s) :
    ∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List ℕ) (x4 : ℕ),   x1.length + x2.length ≤ (13 : ℕ) →     (∀ x6 ∈ x1, (9 : ℕ) ∉ x6.inputs) →       (9 : ℕ) ∈ x3 →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.MetaComplexity.FanInTwo x8 → x4 ≤ (24 : ℕ) → x4 ≠ (9 : ℕ) → (∀ x12 ∈ x8.gates, ∀ x14 ∈ x12.inputs, x14 ≤ (24 : ℕ)) → ∃ (x13 : Fin (9 : ℕ) → Bool), x8.eval (List.ofFn x13 ++ [x13 (4 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ))]) ≠ (x13 (0 : Fin (9 : ℕ)) && x13 (1 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (2 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (3 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (4 : Fin (9 : ℕ)) || x13 (4 : Fin (9 : ℕ)) && x13 (0 : Fin (9 : ℕ)) || x13 (0 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (5 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (6 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (8 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ))) := by
  intro a b ins o budget _ reads
  let C : Circuit := ⟨a ++ ⟨GateOp.or,ins⟩ :: b,o⟩
  change FanInTwo C → _
  intro fan _ _ _
  by_contra! exactEval
  let F (x : Fin 9 → Bool) := C.eval (List.ofFn x ++ [false])
  let G (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have agree (x : Fin 9 → Bool) (h : (x 4 && x 6) = false) : F x = G x := by
    have h' := exactEval x
    change C.eval (List.ofFn x ++ [x 4 && x 6]) = G x at h'
    simpa only [h] using h'
  have small : HasCircuitSize 9 F (a.length + b.length) := bypass 9 a b ins o reads fan
  have sensitive : ∃ x, F (Function.update x 4 false) ≠ F (Function.update x 4 true) := by
    let x : Fin 9 → Bool := fun i => decide (i = 0)
    refine ⟨x, ?_⟩
    rw [agree _ (by decide +revert), agree _ (by decide +revert)]
    dsimp only [G,x]
    decide
  have nonconstant : ∃ x y, F (Function.update x 4 false) ≠ F (Function.update y 4 false) := by
    let y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    refine ⟨fun _ => false, y, ?_⟩
    rw [agree _ (by simp), agree _ (by simp)]
    dsimp only [G,y]
    decide
  have cofactor : (fun x => F (Function.update x 4 false)) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    funext x
    rw [agree _ (by simp)]
    simp [G,Function.update_of_ne]
  have reduced := restrict _ _ F 4 small sensitive nonconstant
  rw [cofactor] at reduced
  have needed := lower _ reduced
  omega
