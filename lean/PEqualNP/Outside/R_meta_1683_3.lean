import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1683_3
    (search : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        ∀ x : Fin 26 → Bool, circuitFun 26 C x =
          decide (∃ p w : Fin 13,
            (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true))
    (independent : ∀ (C : Circuit),
        (∀ x : Fin 26 → Bool, circuitFun 26 C x =
          decide (∃ p w : Fin 13,
            (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)) →
        ∀ x : Fin 26 → Bool,
          (∀ p w : Fin 13, x (Fin.castAdd 13 p) = true →
            x (Fin.natAdd 13 w) = true →
            ¬ (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d)) →
          circuitFun 26 C x = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  let I := fun p w : Fin 13 =>
    ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d
  have incidence : ∀ p w : Fin 13, I p w ↔
      (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d) := by
    intro p w
    simp [I]
  obtain ⟨C, hmono, hsize, hspec⟩ := search
  refine ⟨C, hmono, hsize, ?_, ?_⟩
  · intro p w hi
    rw [hspec]
    apply decide_eq_true
    exact ⟨p, w, (incidence p w).mp hi, by simp, by simp⟩
  · intro P _ _
    let x : Fin 26 → Bool := fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
      (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ I p w))
    change circuitFun 26 C x = false
    apply independent C hspec x
    intro p w hp hw hi
    have pointLine (q r : Fin 13) : Fin.castAdd 13 q ≠ Fin.natAdd 13 r := by
      intro h
      have hv := congrArg Fin.val h
      change q.val = 13 + r.val at hv
      omega
    have hpP : p ∈ P := by
      rcases of_decide_eq_true hp with ⟨q, hq, heq⟩ | ⟨q, heq, _⟩
      · have hv := congrArg Fin.val heq
        exact (Fin.ext hv : p = q) ▸ hq
      · exact (pointLine p q heq).elim
    rcases of_decide_eq_true hw with ⟨q, _, heq⟩ | ⟨q, heq, hmiss⟩
    · exact pointLine q w heq.symm
    · have hv := congrArg Fin.val heq
      change 13 + w.val = 13 + q.val at hv
      have hwq : w = q := Fin.ext (by omega)
      exact hmiss p hpP ((incidence p q).mpr (hwq ▸ hi))
