import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18666 : ∀ (x1 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop) [x2 : DecidableRel x1],   have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x1 x5 x4 → x3 x5 = Bool.false);   have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x1 x5 x6 → x4 x6 = Bool.false);   ∀ (x5 : Fin ((12 : ℕ) + (12 : ℕ)) → Bool), (¬∃ (x6 : Fin (12 : ℕ)) (x7 : Fin (12 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (12 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (12 : ℕ) x7) = Bool.true) → ∃ (x7 : Fin (12 : ℕ) → Bool), x4 (x3 x7) = x7 ∧ ∀ (x8 : Fin ((12 : ℕ) + (12 : ℕ))), x5 x8 = Bool.true → Fin.addCases x7 (x3 x7) x8 = Bool.true := by
  intro E inst
  dsimp only
  intro x hn
  let l : Fin 12 → Bool := fun i => x (Fin.castAdd 12 i)
  let N := fun (s : Fin 12 → Bool) (j : Fin 12) => decide (∀ i, E i j → s i = false)
  let M := fun (t : Fin 12 → Bool) (i : Fin 12) => decide (∀ j, E i j → t j = false)
  let s := M (N l)
  have leL : ∀ i, l i = true → s i = true := by
    intro i on
    apply decide_eq_true
    intro j e
    cases h : N l j with
    | false => rfl
    | true => exact Bool.noConfusion (on.symm.trans ((of_decide_eq_true h) i e))
  have stable : N s = N l := by
    funext j
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      apply decide_eq_true
      intro i e
      cases a : l i with
      | false => rfl
      | true => exact Bool.noConfusion ((leL i a).symm.trans ((of_decide_eq_true h) i e))
    · intro h
      apply decide_eq_true
      intro i e
      cases a : s i with
      | false => rfl
      | true => exact Bool.noConfusion (h.symm.trans ((of_decide_eq_true a) j e))
  refine ⟨s, ?_, ?_⟩
  · change M (N s) = s
    rw [stable]
  · intro k
    refine Fin.addCases (motive := fun k => x k = true → Fin.addCases s (N s) k = true) ?_ ?_ k
    · intro i hi
      simpa using leL i hi
    · intro j hj
      simp only [Fin.addCases_right, stable]
      apply decide_eq_true
      intro i e
      cases h : l i with
      | false => rfl
      | true => exact (hn ⟨i, j, e, h, hj⟩).elim
