import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_582_704
    (generate : have seed : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      ∃ L : List ℕ, L.length ≤ 26 ∧ L.Nodup ∧ (∀ w ∈ L, w ∉ seed) ∧ 2097151 ∈ L ∧
        ∀ i : Fin L.length, ∃ a ∈ seed ++ L.take i.val, ∃ b ∈ seed ++ L.take i.val,
          L.get i = (a &&& b) ∨ L.get i = (a ||| b))
    (compile : ∀ (seed L : List ℕ) (z : ℕ),
      (∀ i : Fin L.length, ∃ a ∈ seed ++ L.take i.val, ∃ b ∈ seed ++ L.take i.val,
        L.get i = (a &&& b) ∨ L.get i = (a ||| b)) → z ∈ L →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ L.length ∧
        ∀ j : ℕ, C.eval (seed.map (fun m => m.testBit j)) = z.testBit j)
    (interpolate : ∀ C : Circuit, Monotone2 C →
      (∀ j : ℕ, C.eval (([95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752] : List ℕ).map (fun m => m.testBit j)) = (2097151 : ℕ).testBit j) →
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨L, hsize, _, _, htarget, hbuild⟩ := generate
  obtain ⟨C, hmono, hcost, hrows⟩ := compile _ L 2097151 hbuild htarget
  exact ⟨C, hmono, hcost.trans hsize, interpolate C hmono hrows⟩
