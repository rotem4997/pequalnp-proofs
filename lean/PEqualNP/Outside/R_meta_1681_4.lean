import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each pair of masks lists the points and lines of a triangle and its four disjoint lines.
-- For example, bits 0, 1, 2 of 7 are the points, and bits 3, 7, 8, 9 of 904 are the lines.
-- Translation, multiplication by a power of three, and point-line duality generate the rows.
-- The circuit is tested on every image. It need not respect any of these symmetries.
theorem PEqualNP.Outside.R_meta_1681_4 :
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     let I := fun (p w : Fin 13) => ∃ d ∈ D, p = w + d
     let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
     let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
       let bit := fun (a b : ℕ) (i : Fin 13) =>
         if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
       Fin.append (bit z.1 z.2) (bit z.2 z.1)
     ∀ P : Finset (Fin 13),
       let W := fun w : Fin 13 => ∀ p ∈ P, ¬ I p w
       (∀ v ∉ P, ∃ w, W w ∧ I v w) →
       (¬ (∃ w, ∀ p ∈ P, I p w) ∧ ¬ (∃ p, ∀ w, W w → I p w)) →
       ∃ z ∈ reps, ∃ m ∈ ([1, 3, 9] : List (Fin 13)), ∃ t : Fin 13, ∃ dual : Bool,
         (fun k : Fin (13 + 13) => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
           (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ W w))) = row z m t dual) →
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
     let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
       let bit := fun (a b : ℕ) (i : Fin 13) =>
         if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
       Fin.append (bit z.1 z.2) (bit z.2 z.1)
     ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
       (∀ p w : Fin 13, (∃ d ∈ D, p = w + d) →
         circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
       (∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t : Fin 13, ∀ dual : Bool,
         circuitFun (13 + 13) C (row z m t dual) = false)) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  intro classify synthesize
  obtain ⟨C, hmono, hsize, hpos, hneg⟩ := synthesize
  refine ⟨C, hmono, hsize, hpos, ?_⟩
  intro P closed generic
  obtain ⟨z, hz, m, hm, t, dual, hrow⟩ := classify P closed generic
  rw [hrow]
  exact hneg z hz m hm t dual
