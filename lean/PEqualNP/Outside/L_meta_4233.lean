import PEqualNP.Defs

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_4233 : have x1 : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ))); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∀ (x3 : Fin (26 : ℕ) → Bool), (∀ (x4 x5 : Fin (13 : ℕ)), x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true → x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true → ¬x2 x4 x5) → ((∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), x3 (Fin.castAdd (13 : ℕ) x6) = Bool.true → x2 x6 x5) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true → x2 x5 x6) → ∃ (x6 : Fin (44 : ℕ)), ∀ (x7 : Fin (20 : ℕ)), x1 x3 x7 = Bool.true → ([(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ), (730724029253162005 : ℕ), (866973350870287389 : ℕ), (875963053248350355 : ℕ), (884986756446568478 : ℕ), (903000063497490454 : ℕ), (954792603833647132 : ℕ), (1012212425860929682 : ℕ), (1041183516279060867 : ℕ), (1062218301194542225 : ℕ), (1078371242023506996 : ℕ), (1142983005070916482 : ℕ), (1099479117384 : ℕ)].getD (↑x6 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (↑x6 % (3 : ℕ)) + ↑x7) = Bool.true := by
  dsimp only
  intro x
  simp only [Fin.forall_fin_succ, Fin.exists_fin_succ, Fin.forall_fin_zero, Fin.exists_fin_zero]
  simp +decide
  grind (splits := 10000)
