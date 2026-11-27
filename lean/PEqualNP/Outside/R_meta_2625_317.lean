import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete the line through points 0, 1, 3, 9 and its four points.
-- The nine remaining points and twelve remaining lines form the affine part.
-- A four-star circuit for the boundary uses nineteen gates, and one OR joins it to the residual.
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_2625_317
    (complete :
     let D : Finset (Fin 13) := {0,1,3,9}
     let inp := (List.finRange 26).filter (fun i => i.val ∉ ([0,1,3,9,13] : List ℕ))
     let hit := fun (x : Fin 26 → Bool) => decide (∃ p ∈ D, ∃ w : Fin 13,
       p - w ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)
     ∀ B : Circuit, Monotone2 B → B.output < 21 + B.size →
       ∃ C : Circuit, Monotone2 C ∧ C.size ≤ B.size + 20 ∧
         ∀ x : Fin 26 → Bool, circuitFun 26 C x = (B.eval (inp.map x) || hit x))
    (affine :
     let D : Finset (Fin 13) := {0, 1, 3, 9}
     let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
     let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
       let bit := fun (a b : ℕ) (i : Fin 13) =>
         if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
       Fin.append (bit z.1 z.2) (bit z.2 z.1)
     let inp := (List.finRange 26).filter (fun i => i.val ∉ ([0,1,3,9,13] : List ℕ))
     ∃ B : Circuit, Monotone2 B ∧ B.output < 21 + B.size ∧ B.size ≤ 43 ∧
       (∀ p w : Fin 13, p ∉ D → p - w ∈ D →
         B.eval (inp.map (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w))) = true) ∧
       (∀ z ∈ reps, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t dual,
          B.eval (inp.map (row z m t dual)) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false := by
  intro D reps row
  let inp := (List.finRange 26).filter (fun i => i.val ∉ ([0,1,3,9,13] : List ℕ))
  let hit := fun (x : Fin 26 → Bool) => decide (∃ p ∈ D, ∃ w : Fin 13,
    p - w ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)
  obtain ⟨B, hm, ho, hs, pos, neg⟩ := affine
  obtain ⟨C, hc, hsize, hsem⟩ := complete B hm ho
  refine ⟨C, hc, by omega, ?_, ?_⟩
  · intro p w hp
    rcases hp with ⟨d, hd, heq⟩
    have hdiff : p - w ∈ D := by simpa [heq, add_comm] using hd
    rw [hsem, Bool.or_eq_true]
    by_cases hin : p ∈ D
    · right
      apply decide_eq_true
      exact ⟨p, hin, w, hdiff, by simp, by simp⟩
    · exact Or.inl (pos p w hin hdiff)
  · intro z hz m hmult t dual
    have safe : ∀ z ∈ reps, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t dual, hit (row z m t dual) = false := by
      decide +kernel
    change circuitFun 26 C (row z m t dual) = false
    rw [hsem]
    change (B.eval (inp.map (row z m t dual)) || hit (row z m t dual)) = false
    rw [neg z hz m hmult t dual, safe z hz m hmult t dual]
    rfl
