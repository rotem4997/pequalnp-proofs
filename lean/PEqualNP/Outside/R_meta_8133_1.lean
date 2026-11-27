import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8133_1
    (h1 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (15 : ℕ) → ∃ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x5) ≠ x1 x5)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (fun (x1 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ)), x1 x2 = Bool.true ∧ x1 x3 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true)) x) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 15 ∧ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = (fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))) y) :
    ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ)), x1 x2 = Bool.true ∧ x1 x3 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true)) (15 : ℕ) := by
  rintro ⟨C,hC,hs,hf⟩
  obtain ⟨D,hD,hDs,hDf⟩ := h2 C hC hs hf
  obtain ⟨y,hy⟩ := h1 D hD hDs
  exact hy (hDf y)
