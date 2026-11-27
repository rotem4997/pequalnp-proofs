import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Second cut of L-meta-4143, parallel to R_meta_4143_1 (which removed the
-- three-point affine boundary on line 1, points 2, 4, 10). This one removes
-- the three-point affine boundary on line 2: points 2, 5, 11. Line 2 has
-- points {2, 3, 5, 11}; after the original exclusions {0, 1, 3, 9} exactly
-- the points 2, 5, 11 remain on it, so deleting them also deletes line 2's
-- wire (15). The completion child adds the three deleted point stars back
-- (15 gates) and restores their twelve incidences.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4143_2
    (completion : ∀ (C : Circuit), Monotone2 C → C.output < 17+C.size → ∃ B : Circuit, Monotone2 B ∧ B.output < 21+B.size ∧ B.size ≤ C.size+15 ∧ ∀ x : Fin 26 → Bool, B.eval ((List.filter (fun i : Fin 26 => decide (i.val ∉ ([0,1,3,9,13] : List ℕ))) (List.finRange 26)).map x) = (C.eval ((List.filter (fun i : Fin 26 => decide (i.val ∉ ([0,1,2,3,5,9,11,13,15] : List ℕ))) (List.finRange 26)).map x) || (((x 2 && ((x 14 || x 15) || (x 19 || x 25))) || (x 5 && ((x 15 || x 17) || (x 18 || x 22)))) || (x 11 && ((x 15 || x 21) || (x 23 || x 24))))))
    (small : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); have x4 : List (Fin (26 : ℕ)) := List.filter (fun (x4 : Fin (26 : ℕ)) => Decidable.decide (↑x4 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (11 : ℕ), (13 : ℕ), (15 : ℕ)])) (List.finRange (26 : ℕ)); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.output < (17 : ℕ) + x5.size ∧ x5.size ≤ (28 : ℕ) ∧ (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∉ x1 ∪ {2,5,11} → x6 - x7 ∈ x1 → x5.eval (List.map (fun (x10 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) x4) = Bool.true) ∧ ∀ x6 ∈ x2, ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool), x5.eval (List.map (x3 x6 x8 x10 x11) x4) = Bool.false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); have x4 : List (Fin (26 : ℕ)) := List.filter (fun (x4 : Fin (26 : ℕ)) => Decidable.decide (↑x4 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.output < (21 : ℕ) + x5.size ∧ x5.size ≤ (43 : ℕ) ∧ (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∉ x1 → x6 - x7 ∈ x1 → x5.eval (List.map (fun (x10 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) x4) = Bool.true) ∧ ∀ x6 ∈ x2, ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool), x5.eval (List.map (x3 x6 x8 x10 x11) x4) = Bool.false := by
  intro D reps row inp
  obtain ⟨C,hC,hout,hsize,hpos,hneg⟩ := small
  obtain ⟨B,hB,hBout,hBsize,hsem⟩ := completion C hC hout
  refine ⟨B,hB,hBout,by omega,?_,?_⟩
  · intro p l hp hl
    change B.eval ((List.filter (fun i : Fin 26 => decide (i.val ∉ ([0,1,3,9,13] : List ℕ))) (List.finRange 26)).map (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l))) = true
    rw [hsem]
    by_cases hdel : p ∈ ({2,5,11} : Finset (Fin 13))
    · have checked : ∀ p l : Fin 13, p ∈ ({2,5,11} : Finset (Fin 13)) → p-l ∈ D →
          (let x : Fin 26 → Bool := fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l); (((x 2 && ((x 14 || x 15) || (x 19 || x 25))) || (x 5 && ((x 15 || x 17) || (x 18 || x 22)))) || (x 11 && ((x 15 || x 21) || (x 23 || x 24))))) = true := by decide +kernel
      have hc := checked p l hdel hl
      dsimp only at hc
      simp only [hc, Bool.or_true]
    · have hp' : p ∉ D ∪ ({2,5,11} : Finset (Fin 13)) := by simpa only [Finset.mem_union, not_or] using And.intro hp hdel
      rw [hpos p l hp' hl]
      rfl
  · intro z hz m hm t dual
    change B.eval ((List.filter (fun i : Fin 26 => decide (i.val ∉ ([0,1,3,9,13] : List ℕ))) (List.finRange 26)).map (row z m t dual)) = false
    rw [hsem,hneg z hz m hm t dual]
    have checked : ∀ z ∈ reps, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t dual,
        (let x : Fin 26 → Bool := row z m t dual; (((x 2 && ((x 14 || x 15) || (x 19 || x 25))) || (x 5 && ((x 15 || x 17) || (x 18 || x 22)))) || (x 11 && ((x 15 || x 21) || (x 23 || x 24))))) = false := by decide +kernel
    exact checked z hz m hm t dual
