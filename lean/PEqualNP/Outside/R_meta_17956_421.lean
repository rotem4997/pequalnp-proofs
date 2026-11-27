import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

/-- Delete the four incidences on line zero. The circuit can share gates
between the residual and the four-point star; two final ORs restore the
deleted rectangle, one using its point side and one using its line side. -/
theorem PEqualNP.Outside.R_meta_17956_421
    (residual : ∃ (C : Circuit) (r s : ℕ), C.size ≤ 61 ∧ IsAO2 26 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ r < 26 + C.size ∧ s < 26 + C.size ∧
      r ≠ s ∧ r ≠ 13 ∧ ∀ x : Fin 26 → Bool,
        (wireValue C 26 x r = true ↔ ∃ p l : Fin 13, l ≠ 0 ∧
          (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
        wireValue C 26 x s = (x 0 || x 1 || x 3 || x 9))
    (fork : ∀ (n : ℕ) (C : Circuit) (r s : ℕ) (t : Fin n), IsAO2 n C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → r < n + C.size → s < n + C.size →
      r ≠ s → r ≠ t.val →
      ∃ (D : Circuit) (a b : ℕ), D.size ≤ C.size + 2 ∧ IsAO2 n D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧ a ≠ b ∧ a < n + D.size ∧ b < n + D.size ∧
        ∀ x : Fin n → Bool,
          wireValue D n x a = (wireValue C n x r || wireValue C n x s) ∧
          wireValue D n x b = (wireValue C n x r || x t)) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), x3.size ≤ 63 ∧ PEqualNP.TopForm.IsAO2 26 x3 ∧ (∀ g ∈ x3.gates, g.inputs.Nodup) ∧ x5 ≠ x6 ∧ x5 < 26 + x3.size ∧ x6 < 26 + x3.size ∧ (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (13 : ℕ) → Bool), (∀ (x8 : Fin (13 : ℕ)), x7 x8 = Bool.false → ∃ (x10 : Fin (13 : ℕ)), x1 x8 x10 ∧ x2 x7 x10 = Bool.true) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (Fin.append x7 (x2 x7)) (if x2 x7 (0 : Fin (13 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  obtain ⟨C, r, s, hsize, hao, hnd, hr, hs, hrs, hrt, sem⟩ := residual
  obtain ⟨D, a, b, hsize', hao', hnd', hab, ha, hb, out⟩ :=
    fork 26 C r s 13 hao hnd hr hs hrs hrt
  dsimp only
  refine ⟨D, a, b, by omega, hao', hnd', hab, ha, hb, ?_, ?_⟩
  · intro p l hi
    let x (k : Fin 26) := decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)
    change wireValue D 26 x a = true ∧ wireValue D 26 x b = true
    rw [(out x).1, (out x).2]
    by_cases hl : l = 0
    · subst l
      have hline : x 13 = true := by simp [x, Fin.natAdd]
      have hstar : (x 0 || x 1 || x 3 || x 9) = true := by
        rcases hi with h | h | h | h <;> subst p <;> decide
      simp [(sem x).2, hline, hstar]
    · have hres := (sem x).1.mpr ⟨p, l, hl, hi, by simp [x], by simp [x]⟩
      simp [hres]
  · intro P _
    let miss (l : Fin 13) := !(P l || P (l+1) || P (l+3) || P (l+9))
    let x := Fin.append P miss
    change wireValue D 26 x (if miss 0 = true then a else b) = false
    have hres : wireValue C 26 x r = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, l, _, hi, hp, hl⟩ := (sem x).1.mp h
      rw [show x (Fin.castAdd 13 p) = P p from Fin.append_left ..] at hp
      rw [show x (Fin.natAdd 13 l) = miss l from Fin.append_right ..] at hl
      rcases hi with h | h | h | h <;> subst p <;> simp [miss, hp] at hl
    have hstar : (x 0 || x 1 || x 3 || x 9) = !miss 0 := by
      change (P 0 || P 1 || P 3 || P 9) = !(!(P 0 || P 1 || P 3 || P 9))
      simp
    have hline : x 13 = miss 0 := Fin.append_right P miss 0
    cases h : miss 0 <;> simp [h, (out x).1, (out x).2, hres, (sem x).2, hstar, hline]
