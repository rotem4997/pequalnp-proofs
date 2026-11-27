import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8843_268
    (hNormalize : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ b : Bool, ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = b) ∨
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
        ∀ x : Fin n → Bool,
          PEqualNP.MetaComplexity.circuitFun n D x = PEqualNP.MetaComplexity.circuitFun n C x)
    (hLower : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 (Fin.append (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7)) = Bool.true) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 (Fin.append (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7)) = Bool.true) := by
  dsimp only at hLower ⊢
  intro C hm hs hp
  rcases hNormalize 26 C hm with ⟨b, hconst⟩ | ⟨D, hd, hsize, heval⟩
  · have hb : b = true := by
      have h := hp 0 0 (Or.inl rfl)
      rw [hconst] at h
      exact h
    refine ⟨∅, ∅, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · rw [hconst, hb]
  · obtain ⟨P, L, hdisjoint, hpoints, hlines, haccept⟩ :=
      hLower D hd (hsize.trans hs) (fun p l hi => by rw [heval]; exact hp p l hi)
    refine ⟨P, L, hdisjoint, hpoints, hlines, ?_⟩
    rw [← heval]
    exact haccept
