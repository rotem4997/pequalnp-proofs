import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2608_471
    (small : ∀ (P L : Finset (Fin 13)), (∀ p ∈ P, ∀ l ∈ L,
      ¬ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)) → P.card ≤ 3 ∨ L.card ≤ 3)
    (search :
      let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let row := fun (points : Bool) (S : Finset (Fin 13)) =>
        let bit := fun i : Fin 13 => decide (i ∈ S)
        let free := fun i : Fin 13 => decide (∀ j ∈ S, ¬ (if points then E j i else E i j))
        if points then Fin.append bit free else Fin.append free bit
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (j a b : ℕ),
        C.size ≤ 64 ∧ PEqualNP.TopForm.IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output = 26+j ∧
        C.gates[j]? = some ⟨.and, [a,b]⟩ ∧
        (∀ p l, E p l →
          let x := fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
          PEqualNP.BlindGate.wireValue C 26 x a = true ∧
          PEqualNP.BlindGate.wireValue C 26 x b = true) ∧
        ∀ side S, S.card ≤ 3 →
          PEqualNP.BlindGate.wireValue C 26 (row side S)
            (if row side S (13 : Fin 26) then a else b) = false) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  classical
  let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let row := fun (points : Bool) (S : Finset (Fin 13)) =>
    let bit := fun i : Fin 13 => decide (i ∈ S)
    let free := fun i : Fin 13 => decide (∀ j ∈ S, ¬ (if points then E j i else E i j))
    if points then Fin.append bit free else Fin.append free bit
  obtain ⟨C,j,a,b,hs,ha,hd,ho,hg,hy,hn⟩ := search
  refine ⟨C,j,a,b,hs,ha,hd,ho,hg,hy,?_⟩
  intro z hz
  let P : Finset (Fin 13) := Finset.univ.filter (fun p => z (Fin.castAdd 13 p) = true)
  let L : Finset (Fin 13) := Finset.univ.filter (fun l => z (Fin.natAdd 13 l) = true)
  have hp (p : Fin 13) : p ∈ P ↔ z (Fin.castAdd 13 p) = true := by simp [P]
  have hl (l : Fin 13) : l ∈ L ↔ z (Fin.natAdd 13 l) = true := by simp [L]
  have independent : ∀ p ∈ P, ∀ l ∈ L, ¬ E p l := by
    intro p pm l lm e
    exact hz.prop ⟨p,l,e,(hp p).mp pm,(hl l).mp lm⟩
  have rowOK (side : Bool) (S : Finset (Fin 13)) :
      ¬ ∃ p l, E p l ∧ row side S (Fin.castAdd 13 p) = true ∧
        row side S (Fin.natAdd 13 l) = true := by
    rintro ⟨p,l,e,yp,yl⟩
    cases side <;> simp only [row, Bool.false_eq_true, ↓reduceIte, Fin.append_left,
      Fin.append_right, decide_eq_true_eq] at yp yl
    · exact yp l yl e
    · exact yl p yp e
  have domP : z ≤ row true P := by
    intro i
    apply Bool.le_iff_imp.mpr
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro p yes
      simp only [row, ↓reduceIte, Fin.append_left, decide_eq_true_eq]
      exact (hp p).mpr yes
    · intro l yes
      simp only [row, ↓reduceIte, Fin.append_right, decide_eq_true_eq]
      exact fun p pm => independent p pm l ((hl l).mpr yes)
  have domL : z ≤ row false L := by
    intro i
    apply Bool.le_iff_imp.mpr
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro p yes
      simp only [row, Bool.false_eq_true, ↓reduceIte, Fin.append_left, decide_eq_true_eq]
      exact fun l lm => independent p ((hp p).mpr yes) l lm
    · intro l yes
      simp only [row, Bool.false_eq_true, ↓reduceIte, Fin.append_right, decide_eq_true_eq]
      exact (hl l).mpr yes
  rcases small P L independent with pc | lc
  · have eqrow := le_antisymm domP (hz.le_of_ge (rowOK true P) domP)
    rw [eqrow]
    exact hn true P pc
  · have eqrow := le_antisymm domL (hz.le_of_ge (rowOK false L) domL)
    rw [eqrow]
    exact hn false L lc
