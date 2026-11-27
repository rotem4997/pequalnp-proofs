import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Precompute one binary gate on a representative raw pair.
-- An AND uses an incident pair. An OR uses a same-side, incident, or nonincident pair.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1681_3 :
    (∃ (q : Fin 4) (D : Circuit),
      Monotone2 D ∧ NestedCover.ReadsBack 27 D ∧ D.size ≤ 62 ∧
      let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let I := fun (p w : Fin 13) => ∃ d ∈ offsets, p = w + d
      let j : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
      let useAnd := decide (q.val = 0)
      let aug := fun (x : Fin 26 → Bool) =>
        Fin.lastCases (if useAnd then x 0 && x j else x 0 || x j) x
      (∀ p w : Fin 13, I p w → circuitFun 27 D
        (aug (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w))) = true) ∧
      (∀ P : Finset (Fin 13),
        let miss := fun w : Fin 13 => ∀ p ∈ P, ¬ I p w
        (∀ v ∉ P, ∃ w, miss w ∧ I v w) →
        (¬ (∃ w, ∀ p ∈ P, I p w) ∧ ¬ (∃ v, ∀ w, miss w → I v w)) →
        ∀ x : Fin 26 → Bool,
          (∀ k, x k = true ↔ (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ miss w)) →
          circuitFun 27 D (aug x) = false)) →
    (∀ (j : Fin 26) (useAnd : Bool) (D : Circuit),
      Monotone2 D → NestedCover.ReadsBack 27 D →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 1 ∧
        ∀ x : Fin 26 → Bool, circuitFun 26 C x =
          circuitFun 27 D (Fin.lastCases (if useAnd then x 0 && x j else x 0 || x j) x)) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  intro search materialize
  obtain ⟨q, D, hMon, hBack, hSize, hPos, hNeg⟩ := search
  let j : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
  let useAnd := decide (q.val = 0)
  obtain ⟨C, cMon, cSize, eval⟩ := materialize j useAnd D hMon hBack
  refine ⟨C, cMon, cSize.trans (Nat.succ_le_succ hSize), ?_, ?_⟩
  · intro p w hw
    rw [eval]
    exact hPos p w hw
  · intro P closed generic
    refine (eval _).trans ?_
    refine hNeg P closed generic _ ?_
    intro k
    exact decide_eq_true_iff
