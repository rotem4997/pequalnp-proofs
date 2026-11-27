import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2397_509
    (monotoneEval : ∀ (n : ℕ) (C : Circuit), Monotone2 C → Monotone (circuitFun n C))
    (finite :
      let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        (∀ p l : Fin 13, I p l →
          (circuitFun 26 C fun i : Fin 26 =>
            decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        ∃ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬ I p l) ∧
          (∀ l : Fin 13, (P.filter fun p => I p l).card ≤ 2) ∧
          (∀ p : Fin 13, (Q.filter fun l => I p l).card ≤ 2) ∧
          circuitFun 26 C
            (Fin.append (fun p : Fin 13 => decide (p ∈ P))
              (fun l : Fin 13 => decide (l ∈ Q))) = true) :
let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), (∀ x9 ∈ x6, x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true) → (∀ x10 ∈ x7, x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x8 = Bool.true := by
  intro I C hm hs hon
  obtain ⟨P, Q, hDisj, hP, hQ, htest⟩ := finite C hm hs hon
  refine ⟨P, Q, hDisj, hP, hQ, ?_⟩
  intro x hxP hxQ
  have hle : (Fin.append (fun p : Fin 13 => decide (p ∈ P))
      (fun l : Fin 13 => decide (l ∈ Q)) : Fin 26 → Bool) ≤ x := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      by_cases hp : p ∈ P
      · simp [hp, hxP p hp]
      · simp [hp]
    · intro l
      change Fin.append (fun p : Fin 13 => decide (p ∈ P))
        (fun l : Fin 13 => decide (l ∈ Q)) (Fin.natAdd 13 l) ≤ x (Fin.natAdd 13 l)
      rw [Fin.append_right]
      by_cases hl : l ∈ Q
      · rw [hxQ l hl]
        simp [hl]
      · simp [hl]
  have h := monotoneEval 26 C hm hle
  rw [htest] at h
  exact Bool.eq_true_of_true_le h
