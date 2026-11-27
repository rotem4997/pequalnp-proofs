import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

-- Redirecting an AND gate to an operand preserves acceptance.
-- Redirecting an OR gate to an operand preserves rejection.
-- On the opposite class of plane rows the redirection must be tested.
set_option maxHeartbeats 180000 in
theorem PEqualNP.Outside.R_meta_2718_236
    (erase : ∀ (n : ℕ) (C : Circuit) (j p : ℕ) (g : Gate),
      Monotone2 C → C.gates[j]? = some g → p ∈ g.inputs → p < n + j →
      let E := eraseGate n C j p
      Monotone2 E ∧ E.size < C.size ∧
        (g.op = GateOp.and → ∀ x, circuitFun n C x = true → circuitFun n E x = true) ∧
        (g.op = GateOp.or → ∀ x, circuitFun n C x = false → circuitFun n E x = false))
    (redirect :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let inc := fun p w : Fin 13 => ∃ d ∈ diff, p = w + d
      let avoids := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬ inc p w
      let pos := fun C : Circuit => ∀ p w : Fin 13, inc p w →
        circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true
      let neg := fun C : Circuit => ∀ P : Finset (Fin 13),
        (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
        ((∃ w, ∀ p ∈ P, inc p w) ∨ (∃ v, ∀ w, avoids P w → inc v w)) →
        circuitFun 26 C (fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
          ∃ w : Fin 13, k = Fin.natAdd 13 w ∧ avoids P w)) = false
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 → pos C → neg C →
        1 < min (C.lineDeg 26 (Finset.Ico 13 26)) (C.lineDeg 26 (Finset.range 13)) →
        ∃ (j p : ℕ) (g : Gate), C.gates[j]? = some g ∧ p ∈ g.inputs ∧ p < 26 + j ∧
          let E := eraseGate 26 C j p
          ((g.op = GateOp.and ∧ neg E) ∨ (g.op = GateOp.or ∧ pos E))) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (1 : ℕ)) := by
  intro diff Q C hC
  let low := fun D : Circuit =>
    HasLineDegree 26 (Finset.Ico 13 26) D 1 ∨ HasLineDegree 26 (Finset.range 13) D 1
  classical
  let atSize := fun k : ℕ => ∃ D : Circuit, Q D ∧ D.size = k
  have ex : ∃ k, atSize k := ⟨C.size, C, hC, rfl⟩
  obtain ⟨D, hD, hsize⟩ := Nat.find_spec ex
  by_cases hl : low D
  · exact ⟨D, hD, hl⟩
  have hlLines : ¬ HasLineDegree 26 (Finset.Ico 13 26) D 1 := fun h => hl (Or.inl h)
  have hlPoints : ¬ HasLineDegree 26 (Finset.range 13) D 1 := fun h => hl (Or.inr h)
  have high : 1 < min (D.lineDeg 26 (Finset.Ico 13 26)) (D.lineDeg 26 (Finset.range 13)) :=
    lt_min (Nat.lt_of_not_ge hlLines) (Nat.lt_of_not_ge hlPoints)
  obtain ⟨j, p, g, hg, hmem, hlt, hcase⟩ :=
    redirect D hD.1 hD.2.1 hD.2.2.1 (by
      intro P hp hd
      have off := hD.2.2.2 P hp hd
      refine Eq.mpr (congrArg (fun y => circuitFun 26 D y = false) ?_) off
      funext v
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rfl) high
  let E := eraseGate 26 D j p
  obtain ⟨hm, hs, hand, hor⟩ := erase 26 D j p g hD.1 hg hmem hlt
  have smaller : E.size < D.size := hs
  have hE : Q E := by
    refine ⟨hm, (Nat.le_of_lt smaller).trans hD.2.1, ?_⟩
    rcases hcase with ⟨ha, hneg⟩ | ⟨ho, hpos⟩
    · refine ⟨fun u w hu => hand ha _ (hD.2.2.1 u w hu), ?_⟩
      intro P hp hd
      have off := hneg P hp hd
      refine Eq.mpr (congrArg (fun y => circuitFun 26 E y = false) ?_) off
      funext v
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rfl
    · exact ⟨hpos, fun P hmax hdeg => hor ho _ (hD.2.2.2 P hmax hdeg)⟩
  have lower : Nat.find ex ≤ E.size := Nat.find_min' ex (show atSize E.size from ⟨E, hE, rfl⟩)
  exact False.elim ((Nat.not_le_of_gt smaller) (hsize.le.trans lower))
