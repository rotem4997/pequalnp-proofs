import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Among the five selected points, inputs 10 and 15 are incident only to point 1.
-- On the remaining sixteen inputs only four assignments are free.
-- Their masks are 6291, 12551, 25102 and 51226 in cyclic order.
-- Up to square symmetry a subset is a cyclic interval or an opposite pair.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2097_2
    (search : let edges : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528,
        1026, 2052, 4104, 8208, 16385, 32769, 32772]
      let holes : List ℕ := [6291, 12551, 25102, 51226]
      ∃ (D : Circuit) (s : Fin 6), Monotone2 D ∧ NestedCover.ReadsBack 16 D ∧ D.size ≤ 22 ∧
        ∀ x : Fin 16 → Bool, circuitFun 16 D x =
          decide (∃ m ∈ edges ++ (if s.val = 5 then [6291, 25102] else holes.take s.val),
            ∀ i : Fin 16, m.testBit i.val = true → x i = true))
    (liftTwin : ∀ D : Circuit, Monotone2 D → NestedCover.ReadsBack 16 D →
      ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack 17 C ∧ C.size ≤ D.size + 1 ∧
        ∀ x : Fin 17 → Bool, circuitFun 17 C x = circuitFun 16 D (fun i =>
          if i.val = 10 then x 10 || x 15 else if i.val = 15 then x 16 else x i.castSucc)) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 17 D ∧ D.size ≤ 23 ∧
      (let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let pick := fun k : Fin 17 =>
        Fin.ofNat 26 (if k.val < 5 then k.val else if k.val < 14 then k.val + 8 else k.val + 9)
      ∀ p w : Fin 13, p.val < 5 → (∃ d ∈ offsets, p = w + d) → circuitFun 17 D
        (fun k => decide (pick k = Fin.castAdd 13 p ∨ pick k = Fin.natAdd 13 w)) = true) ∧
      (∀ m ∈ ([31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455,
        8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590,
        29446, 33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324,
        58892, 63268, 67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040] : List ℕ), ∀ x : Fin 17 → Bool,
        (∀ k, x k = true → m.testBit k.val = true) → circuitFun 17 D x = false) := by
  let edges : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528,
    1026, 2052, 4104, 8208, 16385, 32769, 32772]
  let holes : List ℕ := [6291, 12551, 25102, 51226]
  let extra (s : Fin 6) : List ℕ := if s.val = 5 then [6291, 25102] else holes.take s.val
  let proj (x : Fin 17 → Bool) (i : Fin 16) :=
    if i.val = 10 then x 10 || x 15 else if i.val = 15 then x 16 else x i.castSucc
  let oldMasks : List ℕ := [31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455,
    8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590, 29446,
    33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324, 58892, 63268, 67610,
    81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040]
  let offsets : Finset (Fin 13) := {0, 1, 3, 9}
  let embed (i : Fin 17) : Fin 26 :=
    Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val + 8 else i.val + 9)
  let pair (p l : Fin 13) (i : Fin 17) :=
    decide (embed i = Fin.castAdd 13 p ∨ embed i = Fin.natAdd 13 l)
  have positive : ∀ p l : Fin 13, p.val < 5 → (∃ d ∈ offsets, p = l + d) →
      ∃ e ∈ edges, ∀ i : Fin 16, e.testBit i.val = true → proj (pair p l) i = true := by
    decide +revert
  have negative : ∀ m ∈ oldMasks, ∀ e ∈ edges ++ holes,
      ∃ i : Fin 16, e.testBit i.val = true ∧ proj (fun k => m.testBit k.val) i = false := by
    decide +revert
  have selected : ∀ s : Fin 6, ∀ m ∈ extra s, m ∈ holes := by decide +revert
  obtain ⟨D, s, hD, backD, sizeD, specD⟩ := search
  change ∀ x : Fin 16 → Bool, circuitFun 16 D x =
    decide (∃ m ∈ edges ++ extra s, ∀ i : Fin 16, m.testBit i.val = true → x i = true) at specD
  obtain ⟨C, hC, backC, sizeC, specC⟩ := liftTwin D hD backD
  change ∀ x : Fin 17 → Bool, circuitFun 17 C x = circuitFun 16 D (proj x) at specC
  refine ⟨C, hC, backC, by omega, ?_, ?_⟩
  · dsimp only
    intro p l hp hpl
    change circuitFun 17 C (pair p l) = true
    rw [specC, specD, decide_eq_true_eq]
    obtain ⟨e, he, bits⟩ := positive p l hp hpl
    exact ⟨e, List.mem_append_left _ he, bits⟩
  · intro m hm x hx
    rw [specC, specD, decide_eq_false_iff_not]
    rintro ⟨e, he, bits⟩
    have he' : e ∈ edges ++ holes := by
      rcases List.mem_append.mp he with ha | hb
      · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ (selected s e hb)
    obtain ⟨i, hi, off⟩ := negative m hm e he'
    have monoProj : proj x i = true → proj (fun k => m.testBit k.val) i = true := by
      dsimp only [proj]
      split
      · simp only [Bool.or_eq_true]
        exact Or.imp (hx 10) (hx 15)
      · split <;> exact hx _
    exact Bool.noConfusion ((monoProj (bits i hi)).symm.trans off)
