import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reuse line disjunctions computed by the ten fixed point stars.
-- The remaining three points use thirteen gates, twelve raw inputs and fourteen existing unions.
theorem PEqualNP.Outside.R_meta_1683_2
    (core : let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let taps : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25], [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24], [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 13 ∧ ∀ x : Fin 26 → Bool,
      circuitFun 26 D (fun i : Fin 26 => (taps.getD i.val []).any (fun j => x (Fin.ofNat 26 j))) =
        decide (∃ p w : Fin 13, p.val < 3 ∧ (∃ d ∈ offsets, p = w + d) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true))
    (base : let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let taps : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25], [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24], [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]
    ∃ A : Circuit, ∃ pick : Fin 26 → Fin (26 + A.size), Monotone2 A ∧ A.size ≤ 49 ∧
      A.output < 26 + A.size ∧ (∀ x : Fin 26 → Bool, circuitFun 26 A x =
        decide (∃ p w : Fin 13, 3 ≤ p.val ∧ (∃ d ∈ offsets, p = w + d) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)) ∧
      ∀ (x : Fin 26 → Bool) (i : Fin 26), (A.wires (List.ofFn x)).getD (pick i).val false =
        (taps.getD i.val []).any (fun j => x (Fin.ofNat 26 j)))
    (glue : ∀ (n m : ℕ) (A D : Circuit) (pick : Fin m → Fin (n + A.size)),
    A.output < n + A.size → Monotone2 A → Monotone2 D →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ A.size + D.size + 1 ∧
      ∀ x : Fin n → Bool, circuitFun n C x =
        (circuitFun n A x || circuitFun m D (fun i => (A.wires (List.ofFn x)).getD (pick i).val false))) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  obtain ⟨D, hmD, hsD, specD⟩ := core
  obtain ⟨A, pick, hmA, hsA, hoA, specA, tapsA⟩ := base
  obtain ⟨C, hmC, hsC, specC⟩ := glue 26 26 A D pick hoA hmA hmD
  let I := fun p w : Fin 13 => (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d)
  have allEdges (x : Fin 26 → Bool) : circuitFun 26 C x = true ↔
      ∃ p w : Fin 13, I p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true := by
    rw [specC, specA]
    have hx := funext (tapsA x)
    rw [hx, specD]
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    constructor
    · rintro (⟨p,w,_,h⟩ | ⟨p,w,_,h⟩) <;> exact ⟨p,w,h⟩
    · rintro ⟨p,w,e,hp,hw⟩
      rcases le_or_gt (3 : ℕ) p.val with ge | lt
      · exact Or.inl ⟨p,w,ge,e,hp,hw⟩
      · exact Or.inr ⟨p,w,lt,e,hp,hw⟩
  refine ⟨C, hmC, by omega, ?_, ?_⟩
  · intro p w e
    apply (allEdges _).2
    exact ⟨p,w,e,by simp,by simp⟩
  · intro P _ _
    apply Bool.eq_false_iff.mpr
    intro on
    obtain ⟨p,w,e,hp,hw⟩ := (allEdges _).1 on
    have cross (i j : Fin 13) : Fin.castAdd 13 i ≠ Fin.natAdd 13 j := by
      intro h
      have d := congrArg (fun k : Fin 26 => k.val) h
      change i.val = 13+j.val at d
      omega
    have pP : p ∈ P := by
      rcases of_decide_eq_true hp with ⟨j,hj,eq⟩ | ⟨j,eq,_⟩
      · have d := congrArg (fun k : Fin 26 => k.val) eq
        exact (Fin.ext d : p = j) ▸ hj
      · exact (cross p j eq).elim
    rcases of_decide_eq_true hw with ⟨j,_,eq⟩ | ⟨j,eq,miss⟩
    · exact cross j w eq.symm
    · have d := congrArg (fun k : Fin 26 => k.val) eq
      change 13+w.val = 13+j.val at d
      have same : w=j := Fin.ext (by omega)
      exact miss p pP (same ▸ e)
