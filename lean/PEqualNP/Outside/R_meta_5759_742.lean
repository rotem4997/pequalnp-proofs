import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5759_742
    (incidence :
      let E : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun e =>
        e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3
      let M : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun e => e.1 = e.2
      M ⊆ E ∧
        (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
        (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) ∧
        (∀ (p q l t : Fin 7), p ≠ q → l ≠ t →
          ¬ ((p, l) ∈ E ∧ (p, t) ∈ E ∧ (q, l) ∈ E ∧ (q, t) ∈ E)) ∧
        E.card = 21 ∧ M.card = 7)
    (small :
      let E : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun e =>
        e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3
      ∃ C : Circuit, C.size ≤ 26 ∧ IsAO2 14 C ∧
        ∀ z : Fin 14 → Bool,
          circuitFun 14 C z = decide (∃ p l : Fin 7,
            (p, l) ∈ E ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true)) :
∃ (x1 : ℕ) (x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4 ⊆ x3 ∧ (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) ∧ (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.2 = x8.2 → x6 = x8) ∧ (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ (∀ (x6 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ x3 ∧ x6 (Fin.castAdd x2 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true)) ∧ x5.size + (1 : ℕ) < x3.card + x4.card := by
  obtain ⟨hsub, hleft, hright, hsquare, hedge, hmatch⟩ := incidence
  obtain ⟨C, hsize, hao, hfun⟩ := small
  refine ⟨7, 7, _, _, C, hsub, hleft, hright, hsquare, hao, hfun, ?_⟩
  omega
