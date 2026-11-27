import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_9175 : ∃ (x1 : SimpleGraph (Fin (6 : ℕ))) (x2 : PEqualNP.AndCount.AndCountCircuit (6 : ℕ)), x2.WellFormed ∧ ∀ (x3 : Finset (Fin (6 : ℕ))), (∀ x4 ∈ x3, ∀ x6 ∈ x3, ¬x1.Adj x4 x6) → (∀ x5 ∉ x3, ∃ x7 ∈ x3, x1.Adj x5 x7) → x2.eval x3 = Bool.false ∧ ∀ x6 ∉ x3, x2.eval (Insert.insert x6 x3) = Bool.true := by
  refine ⟨⊥, ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, ∅⟩, fun i => i.elim0, ?_⟩
  intro x3 _ hmax
  refine ⟨by simp [PEqualNP.AndCount.AndCountCircuit.eval], fun x6 hx6 => ?_⟩
  obtain ⟨_, _, hadj⟩ := hmax x6 hx6
  exact False.elim hadj
