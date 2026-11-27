import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_8205_1 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      Monotone (PEqualNP.MetaComplexity.circuitFun 27 C)) →
    (have D : Finset (Fin 13) := {0, 1, 3, 9}
    have adj : Fin 13 → Fin 13 → Prop := fun p l => ∃ d ∈ D, p = l + d
    have lift : (Fin 26 → Bool) → Fin 27 → Bool :=
      fun x => Fin.lastCases (x 0 || x 1) x
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 C ∧
      C.size ≤ 32 ∧ C.output < 27 + C.size ∧
      (∀ p l : Fin 13, l.val < 7 → adj p l →
        PEqualNP.MetaComplexity.circuitFun 27 C
          (lift (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) ∧
      ∀ P : Finset (Fin 13),
        (¬∃ l : Fin 13, ∀ p ∈ P, adj p l) →
        (¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ adj q l) → adj p l) →
        PEqualNP.MetaComplexity.circuitFun 27 C
          (lift (fun i => Fin.addCases (m := 13) (n := 13) (motive := fun _ => Bool)
            (fun p => decide (p ∈ P))
            (fun l => decide (Disjoint P (D.image (fun d => l + d)))) i)) = false) →
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 ∧ x4.size ≤ (32 : ℕ) ∧ x4.output < (27 : ℕ) + x4.size ∧ (∀ (x5 x6 : Fin (13 : ℕ)), ↑x6 < (7 : ℕ) → x2 x5 x6 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x5 ∨ x9 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true → x5 (Fin.natAdd (13 : ℕ) x7) ≠ Bool.true) → (¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x5 (Fin.castAdd (13 : ℕ) x8) = Bool.true → x2 x8 x7) → (¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x9) = Bool.true → x2 x8 x9) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 x5) = Bool.false) := by
  intro hMono hBoundary
  obtain ⟨C, hC, hBack, hSize, hOut, hYes, hNo⟩ := hBoundary
  refine ⟨C, hC, hBack, hSize, hOut, hYes, ?_⟩
  intro x hIndependent hPoint hLine
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let adj : Fin 13 → Fin 13 → Prop := fun p l => ∃ d ∈ D, p = l + d
  let P : Finset (Fin 13) :=
    Finset.univ.filter (fun p => x (Fin.castAdd 13 p) = true)
  let y : Fin 26 → Bool := fun i =>
    Fin.addCases (m := 13) (n := 13) (motive := fun _ => Bool)
      (fun p => decide (p ∈ P))
      (fun l => decide (Disjoint P (D.image (fun d => l + d)))) i
  let lift (u : Fin 26 → Bool) : Fin 27 → Bool :=
    Fin.lastCases (u 0 || u 1) u
  have hMem (p : Fin 13) : p ∈ P ↔ x (Fin.castAdd 13 p) = true := by
    simp [P]
  have available (l : Fin 13) (hl : x (Fin.natAdd 13 l) = true) :
      ∀ p ∈ P, ¬ adj p l := by
    intro p hp he
    exact hIndependent p l he ((hMem p).mp hp) hl
  have leftCondition : ¬∃ l : Fin 13, ∀ p ∈ P, adj p l := by
    rintro ⟨l, hl⟩
    exact hPoint ⟨l, fun p hp => hl p ((hMem p).mpr hp)⟩
  have rightCondition : ¬∃ p : Fin 13, ∀ l : Fin 13,
      (∀ q ∈ P, ¬ adj q l) → adj p l := by
    rintro ⟨p, hp⟩
    exact hLine ⟨p, fun l hl => hp l (available l hl)⟩
  have hxy : x ≤ y := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) (motive := fun j => x j ≤ y j) ?_ ?_ i
    · intro p
      cases hh : x (Fin.castAdd 13 p) with
      | false => exact Bool.false_le _
      | true => simp [y, (hMem p).mpr hh]
    · intro l
      cases hh : x (Fin.natAdd 13 l) with
      | false => exact Bool.false_le _
      | true =>
        have ok : Disjoint P (D.image (fun d => l + d)) := by
          apply Finset.disjoint_left.mpr
          intro q hq hm
          obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
          exact available l hh q hq ⟨d, hd, he.symm⟩
        have on : y (Fin.natAdd 13 l) = true := by
          simp only [y, Fin.addCases_right, decide_eq_true_eq]
          exact ok
        exact Bool.le_iff_imp.mpr (fun _ => on)
  have hLift : lift x ≤ lift y := by
    intro i
    refine Fin.lastCases (n := 26) (motive := fun j => lift x j ≤ lift y j) ?_ ?_ i
    · simp only [lift, Fin.lastCases_last]
      apply Bool.le_iff_imp.mpr
      intro h
      exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp
        (Bool.le_iff_imp.mp (hxy 0)) (Bool.le_iff_imp.mp (hxy 1)))
    · intro i
      simpa only [lift, Fin.lastCases_castSucc] using hxy i
  have hBelow : PEqualNP.MetaComplexity.circuitFun 27 C (lift x) ≤
      PEqualNP.MetaComplexity.circuitFun 27 C (lift y) := hMono C hC hLift
  have hFalse : PEqualNP.MetaComplexity.circuitFun 27 C (lift y) = false :=
    hNo P leftCondition rightCondition
  rw [hFalse] at hBelow
  exact le_antisymm hBelow (Bool.false_le _)
