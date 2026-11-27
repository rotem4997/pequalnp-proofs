import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5306_114
    (h_seed :
      let inc : Fin 13 → Fin 13 → Prop :=
        fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ 63 →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 →
        (∀ p l : Fin 13, inc p l →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        ∃ P W : Finset (Fin 13),
          (∀ p ∈ P, ∀ l ∈ W, ¬inc p l) ∧
          (∀ l : Fin 13, (P.filter fun p => inc p l).card ≤ 2) ∧
          (∀ p : Fin 13, (W.filter fun l => inc p l).card ≤ 2) ∧
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => Fin.addCases (fun p => decide (p ∈ P))
              (fun l => decide (l ∈ W)) i) = true)
    (h_mono :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        ∀ z x : Fin 26 → Bool,
          (∀ i : Fin 26, z i = true → x i = true) →
          PEqualNP.MetaComplexity.circuitFun 26 C z = true →
          PEqualNP.MetaComplexity.circuitFun 26 C x = true) :
    let x1 : Fin 13 → Fin 13 → Prop :=
      fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ 63 →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 →
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 →
      (∀ p l : Fin 13, x1 p l →
        PEqualNP.MetaComplexity.circuitFun 26 C
          (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
      ∃ P W : Finset (Fin 13),
        (∀ p ∈ P, ∀ l ∈ W, ¬x1 p l) ∧
        (∀ l : Fin 13, (P.filter fun p => x1 p l).card ≤ 2) ∧
        (∀ p : Fin 13, (W.filter fun l => x1 p l).card ≤ 2) ∧
        ∀ x : Fin 26 → Bool,
          (∀ p ∈ P, x (Fin.castAdd 13 p) = true) →
          (∀ l ∈ W, x (Fin.natAdd 13 l) = true) →
          PEqualNP.MetaComplexity.circuitFun 26 C x = true := by
  intro x1 C hmono hsize hlineL hlineP hincident
  dsimp only at h_seed
  obtain ⟨P, W, hdisjoint, hdegreeP, hdegreeW, hseed⟩ :=
    h_seed C hmono hsize hlineL hlineP hincident
  refine ⟨P, W, hdisjoint, hdegreeP, hdegreeW, ?_⟩
  intro x hP hW
  let z : Fin 26 → Bool :=
    fun i => Fin.addCases (fun p => decide (p ∈ P))
      (fun l => decide (l ∈ W)) i
  have hle : ∀ i : Fin 26, z i = true → x i = true := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro p hp
      simp only [z, Fin.addCases_left] at hp
      exact hP p (of_decide_eq_true hp)
    · intro l hl
      simp only [z, Fin.addCases_right] at hl
      exact hW l (of_decide_eq_true hl)
  exact h_mono C hmono z x hle hseed
