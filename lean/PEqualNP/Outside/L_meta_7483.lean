import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7483 : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; have x2 : List (BitVec (58 : ℕ)) → Bool × ℕ × ℕ → List (BitVec (58 : ℕ)) := fun (x2 : List (BitVec (58 : ℕ))) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : BitVec (58 : ℕ)) &&& x2.getD x3.2.2 (0 : BitVec (58 : ℕ)) else x2.getD x3.2.1 (0 : BitVec (58 : ℕ)) ||| x2.getD x3.2.2 (0 : BitVec (58 : ℕ))]; ∃ (x3 : List (Bool × ℕ × ℕ)),   x3.length = (12 : ℕ) ∧     (∀ (x4 : Fin x3.length),         have x5 : Bool × ℕ × ℕ := x3.getD ↑x4 (Bool.false, (0 : ℕ), (0 : ℕ));         x5.2.1 < x5.2.2 ∧ x5.2.2 < (15 : ℕ) + ↑x4) ∧       (List.foldl x2 (x1 ++ [(953051 : BitVec (58 : ℕ))]) x3).getD (26 : ℕ) (0 : BitVec (58 : ℕ)) = (2097151 : BitVec (58 : ℕ)) := by
  intro x1 x2
  refine ⟨[(false, 0, 4), (false, 5, 15), (true, 10, 16), (false, 3, 4), (false, 6, 18), (true, 11, 19), (false, 1, 2), (false, 4, 21), (true, 13, 22), (false, 14, 17), (false, 20, 24), (false, 23, 25)], rfl, ?_, ?_⟩
  · intro x4
    fin_cases x4 <;> simp
  · decide
