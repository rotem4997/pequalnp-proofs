import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4387_184
    (compress : ∀ (base xs : List (BitVec 58)) (t : BitVec 58),
    let start := (0 : BitVec 58) :: BitVec.allOnes 58 :: base
    (∀ (j : Fin xs.length), let pool := start ++ xs.take j
        ∃ a ∈ pool, ∃ b ∈ pool, xs.get j = a &&& b ∨ xs.get j = a ||| b) → t ∈ start ++ xs → t ≠ 0 → t ≠ BitVec.allOnes 58 → t ∉ base →
    ∃ ys : List (BitVec 58), ys.length ≤ xs.length ∧ ys.getLast? = some t ∧
      (∀ j : Fin ys.length, let pool := base ++ ys.take j
        ys.get j ∉ pool ∧ ys.get j ≠ 0 ∧ ys.get j ≠ BitVec.allOnes 58 ∧
          ∃ a ∈ pool, ∃ b ∈ pool, ys.get j = a &&& b ∨ ys.get j = a ||| b))
    (physical : let base := List.map (BitVec.ofNat 58) ([95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat)
  ∀ xs : List (BitVec 58), xs.length ≤ 25 →
    (∀ j : Fin xs.length, let w := base ++ xs.take j.val
      ∃ a ∈ w, ∃ b ∈ w, xs.get j = a &&& b ∨ xs.get j = a ||| b) →
    (2097151 : BitVec 58) ∈ xs →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : PEqualNP.CircuitLowerBounds.Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) ∧
    (∃ i j, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = .and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧ PEqualNP.EdgeOwnership.InCone 14 C i j) ∧
    (∃ k, k < C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = .and ∧ ∃ u v : Fin 14,
      PEqualNP.EdgeOwnership.gateVal 14 C k (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = false))
    (remaining : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : PEqualNP.CircuitLowerBounds.Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) ∧
    (∃ i j, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = .and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧ PEqualNP.EdgeOwnership.InCone 14 C i j) ∧
    (∃ k, k < C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = .and ∧ ∃ u v : Fin 14,
      PEqualNP.EdgeOwnership.gateVal 14 C k (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = false))) :
    have x1 : List (BitVec (58 : ℕ)) := [(0 : BitVec (58 : ℕ)), BitVec.allOnes (58 : ℕ), (95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ)), (95274182876594239 : BitVec (58 : ℕ))]; ∀ (x2 : List (BitVec (58 : ℕ))),   x2.length ≤ (25 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List (BitVec (58 : ℕ)) := x1 ++ List.take (↑x4) x2;         ∃ x6 ∈ x5, ∃ x7 ∈ x5, x2.get x4 = x6 &&& x7 ∨ x2.get x4 = x6 ||| x7) →       (2097151 : BitVec (58 : ℕ)) ∉ x1 ++ x2 := by
  let base : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239]
  let target : BitVec 58 := 2097151
  dsimp only
  intro xs size legal hit
  obtain ⟨ys, limit, last, clean⟩ := compress base xs target legal hit
    (by decide) (by decide) (by decide)
  have occurs : target ∈ ys := List.mem_of_getLast? last
  apply remaining
  apply physical ys (limit.trans size)
  · intro j
    exact (clean j).2.2.2
  · exact occurs
