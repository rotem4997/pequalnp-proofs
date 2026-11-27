import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6854

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6854

theorem PEqualNP.Outside.L_meta_6854 : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; ∀ x2 ∈ [(95274182876594239 : BitVec (58 : ℕ)), (284526031944024591 : BitVec (58 : ℕ)), (241600541374316567 : BitVec (58 : ℕ)), (1 : BitVec (58 : ℕ))], ∃ (x4 : Bool × ℕ × ℕ), x4.2.1 < x4.2.2 ∧ x4.2.2 < (14 : ℕ) ∧ (if x4.1 = Bool.true then x1.getD x4.2.1 (0 : BitVec (58 : ℕ)) &&& x1.getD x4.2.2 (0 : BitVec (58 : ℕ)) else x1.getD x4.2.1 (0 : BitVec (58 : ℕ)) ||| x1.getD x4.2.2 (0 : BitVec (58 : ℕ))) = x2 := by
  intro L t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨(false, 0, 1), by decide +kernel⟩
  · exact ⟨(false, 0, 7), by decide +kernel⟩
  · exact ⟨(false, 0, 9), by decide +kernel⟩
  · exact ⟨(true, 0, 7), by decide +kernel⟩
