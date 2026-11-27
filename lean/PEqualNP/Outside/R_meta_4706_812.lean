import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Reject the rows through the incidence relation and the absence of collinear triples.
-- This lets the synthesis hypothesis use the geometry directly.
theorem PEqualNP.Outside.R_meta_4706_812
    (samples : let D : Finset (Fin 13) := {0,1,3,9}
     let I := fun p l : Fin 13 => ∃ d ∈ D, p = l+d
     let reps : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
     let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
       let bit := fun (a b : ℕ) (i : Fin 13) =>
         if dual then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
       Fin.append (bit z.1 z.2) (bit z.2 z.1)
     ∀ z ∈ reps, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t : Fin 13, ∀ dual : Bool,
       let x := row z m t dual
       (¬ ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
       ∀ (dual : Bool) (t : Fin 13),
         let on := fun a : Fin 13 =>
           (if dual then I t a else I a t) ∧ x (if dual then Fin.natAdd 13 a else Fin.castAdd 13 a) = true
         ∀ a b c : Fin 13, on a → on b → on c → a = b ∨ a = c ∨ b = c)
    (construct : let D : Finset (Fin 13) := {0,1,3,9}
     let I := fun p l : Fin 13 => ∃ d ∈ D, p = l+d
     ∃ (k : Fin 4) (C : Circuit), Monotone2 C ∧ ReadsBack 27 C ∧ C.size ≤ 62 ∧
       let j : Fin 26 := if k.val = 1 then 1 else if k.val = 3 then 14 else 13
       let aug := fun (x : Fin 26 → Bool) =>
         Fin.lastCases (if k.val = 0 then x 0 && x j else x 0 || x j) x
       (∀ p l : Fin 13, I p l → circuitFun 27 C
         (aug (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) ∧
       ∀ x : Fin 26 → Bool,
       ((¬ ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
        ∀ (dual : Bool) (t : Fin 13),
          let on := fun a : Fin 13 =>
            (if dual then I t a else I a t) ∧ x (if dual then Fin.natAdd 13 a else Fin.castAdd 13 a) = true
          ∀ a b c : Fin 13, on a → on b → on c → a = b ∨ a = c ∨ b = c) → circuitFun 27 C (aug x) = false) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (4 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x5 ∧       x5.size ≤ (62 : ℕ) ∧         have x6 : Fin (26 : ℕ) := if ↑x4 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x4 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x7 : Bool := Decidable.decide (↑x4 = (0 : ℕ));         have x8 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x8 : Fin (26 : ℕ) → Bool) (x9 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x7 = Bool.true then x8 (0 : Fin (26 : ℕ)) && x8 x6 else x8 (0 : Fin (26 : ℕ)) || x8 x6) x8 x9;         (∀ (x9 x10 : Fin (13 : ℕ)), (∃ x11 ∈ x1, x9 = x10 + x11) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) ∧ ∀ x9 ∈ x2, ∀ x11 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x13 : Fin (13 : ℕ)) (x14 : Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 (x3 x9 x11 x13 x14)) = Bool.false := by
  obtain ⟨k,C,mono,back,budget,positive,negative⟩ := construct
  refine ⟨k,C,mono,back,budget,?_,?_⟩
  · simpa only [decide_eq_true_eq] using positive
  · intro z hz m hm t dual
    simpa only [decide_eq_true_eq] using negative _ (samples z hz m hm t dual)
