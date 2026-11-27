import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1979_529
    (core :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 23 ∧ C.output < 26 + C.size ∧
        (∀ p l : Fin 13, l.val < 5 → p - l ∈ diff →
          circuitFun 26 C (fun w => decide (w = Fin.castAdd 13 p ∨ w = Fin.natAdd 13 l)) = true) ∧
        ∀ P L : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ L, p - l ∉ diff) →
          (∀ l : Fin 13, (P.filter fun p => p - l ∈ diff).card ≤ 2) →
          (∀ p : Fin 13, (L.filter fun l => p - l ∈ diff).card ≤ 2) →
          circuitFun 26 C (fun w => decide ((∃ p ∈ P, w = Fin.castAdd 13 p) ∨
            ∃ l ∈ L, w = Fin.natAdd 13 l)) = false)
    (extend :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ C : Circuit, Monotone2 C → C.output < 26 + C.size →
        ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 40 ∧
          ∀ z : Fin 26 → Bool, circuitFun 26 D z = (circuitFun 26 C z ||
            decide (∃ p l : Fin 13, 5 ≤ l.val ∧ p - l ∈ diff ∧
              z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true))) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  obtain ⟨C, cm, cs, co, cHit, cMiss⟩ := core
  obtain ⟨D, dm, ds, dEval⟩ := extend C cm co
  refine ⟨D, dm, by omega, ?_, ?_⟩
  · intro p l hit
    rw [dEval]
    by_cases small : l.val < 5
    · rw [cHit p l small hit]
      rfl
    · have large : 5 ≤ l.val := Nat.le_of_not_gt small
      have yes : (∃ p' l' : Fin 13, 5 ≤ l'.val ∧ p' - l' ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          (decide (Fin.castAdd 13 p' = Fin.castAdd 13 p ∨
            Fin.castAdd 13 p' = Fin.natAdd 13 l) : Bool) = true ∧
          (decide (Fin.natAdd 13 l' = Fin.castAdd 13 p ∨
            Fin.natAdd 13 l' = Fin.natAdd 13 l) : Bool) = true) :=
        ⟨p, l, large, hit, by simp, by simp⟩
      simp only [decide_eq_true yes, Bool.or_true]
  · intro P L independent arcP arcL
    rw [dEval, cMiss P L independent arcP arcL]
    have distinct (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro h
      have eq := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at eq
      have plt := p.isLt
      omega
    have no : ¬ ∃ p l : Fin 13, 5 ≤ l.val ∧ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
        (decide ((∃ r ∈ P, Fin.castAdd 13 p = Fin.castAdd 13 r) ∨
          ∃ m ∈ L, Fin.castAdd 13 p = Fin.natAdd 13 m) : Bool) = true ∧
        (decide ((∃ r ∈ P, Fin.natAdd 13 l = Fin.castAdd 13 r) ∨
          ∃ m ∈ L, Fin.natAdd 13 l = Fin.natAdd 13 m) : Bool) = true := by
      rintro ⟨p, l, _, hit, hp, hl⟩
      have hp' : p ∈ P := by
        rcases decide_eq_true_eq.mp hp with ⟨r, hr, eq⟩ | ⟨m, _, eq⟩
        · have equal := Fin.castAdd_injective 13 13 eq
          simpa only [equal] using hr
        · exact (distinct p m eq).elim
      have hl' : l ∈ L := by
        rcases decide_eq_true_eq.mp hl with ⟨r, _, eq⟩ | ⟨m, hm, eq⟩
        · exact (distinct r l eq.symm).elim
        · have equal := Fin.natAdd_injective 13 13 eq
          simpa only [equal] using hm
      exact independent p hp' l hl' hit
    simp only [decide_eq_false no, Bool.false_or]
