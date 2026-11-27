import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2303_317
    (cofactor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (split : let input (b : Bool) (x : Fin 8 → Bool) := [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      ∀ (D : Circuit) (f g : (Fin 8 → Bool) → Bool), FanInTwo D → D.size ≤ 14 →
      (∀ (b : Bool) x, D.eval (input b x) = if b then g x else f x) →
      (∃ x, x 1 = true ∧ f x = false ∧ g x = true) →
      HasCircuitSize 8 f 12 ∨ ∃ (A B : Circuit) (k : ℕ), FanInTwo A ∧ FanInTwo B ∧ A.size + B.size ≤ 13 ∧
      let w (b : Bool) (x : Fin 8 → Bool) := A.wires (List.ofFn x ++ [x 1 || b])
      (∀ x, B.eval (w false x ++ [(w false x).getD k false]) = f x) ∧
      ∀ x, B.eval (w true x ++ [true]) = g x)
    (marked : let f (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (A B : Circuit) (k : ℕ), FanInTwo A → FanInTwo B → A.size + B.size ≤ 13 →
      let w (b : Bool) (x : Fin 8 → Bool) := A.wires (List.ofFn x ++ [x 1 || b])
      (∀ x, B.eval (w false x ++ [(w false x).getD k false]) = f x) →
      ∃ x, B.eval (w true x ++ [true]) ≠ (f x || x 0 || x 3)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x4 (0 : Fin (9 : ℕ)) = Bool.true ∨ x4 (6 : Fin (9 : ℕ)) = Bool.false → x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → (∀ (x7 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))]) = x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))])) → (14 : ℕ) ≤ x5.size) → ∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.false ∧ x6 (6 : Fin (9 : ℕ)) = Bool.true ∧ x1.eval (List.ofFn x6 ++ [Bool.true]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro D fan size agree _minimum
  by_contra! remaining
  let f (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let g (x : Fin 8 → Bool) := f x || x 0 || x 3
  let input (b : Bool) (x : Fin 8 → Bool) := [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
  let lift (b : Bool) (x : Fin 8 → Bool) : Fin 9 → Bool := ![x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3]
  let target (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have truth : ∀ (b : Bool) (x : Fin 8 → Bool), target (lift b x) = if b then g x else f x := by decide +kernel
  have wires : ∀ (b : Bool) (x : Fin 8 → Bool),
      List.ofFn (lift b x) ++ [lift b x 0 || lift b x 6] = input b x := by decide +kernel
  have allrows (t : Fin 9 → Bool) : D.eval (List.ofFn t ++ [t 0 || t 6]) = target t := by
    cases h0 : t 0 <;> cases h6 : t 6
    · simpa only [target,h0,h6,Bool.false_or] using agree t (Or.inr h6)
    · simpa only [target,h0,h6,Bool.false_or] using remaining t h0 h6
    · simpa only [target,h0,h6,Bool.true_or] using agree t (Or.inl h0)
    · simpa only [target,h0,h6,Bool.true_or] using agree t (Or.inl h0)
  have both (b : Bool) (x : Fin 8 → Bool) : D.eval (input b x) = if b then g x else f x := by
    rw [← wires b x]
    exact (allrows (lift b x)).trans (truth b x)
  have sens : ∃ x : Fin 8 → Bool, x 1 = true ∧ f x = false ∧ g x = true := by
    exact ⟨![false,true,false,true,false,false,false,false], by decide +kernel⟩
  rcases split D f g fan (by omega) both sens with low | ⟨A,B,k,ha,hb,hsize,base,upper⟩
  · exact cofactor low
  · obtain ⟨x,hx⟩ := marked A B k ha hb hsize base
    exact hx (upper x)
