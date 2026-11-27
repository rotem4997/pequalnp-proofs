import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7422

theorem aux (n : ℕ) [NeZero n] (x3 : Fin (n + 1) → Fin n × Fin n → Fin n)
    (h10 : (1 : Fin n) ≠ 0)
    (hb : ∀ a b : Fin (n + 1), a ≠ b → Function.Bijective fun p : Fin n × Fin n => (x3 a p, x3 b p))
    (hn : ∀ k : Fin (n + 1), k ≠ 0 → ∀ j : Fin n, x3 k (0, j) = j) :
    Function.Injective (fun i : Fin n => x3 i.succ (1, 0)) := by
  intro i j hij
  have hij' : x3 i.succ (1, 0) = x3 j.succ (1, 0) := hij
  by_contra hne
  have hs : i.succ ≠ j.succ := fun h => hne (Fin.succ_injective _ h)
  have h1 := (hb _ _ hs).1 (a₁ := ((1 : Fin n), (0 : Fin n)))
    (a₂ := ((0 : Fin n), x3 i.succ (1, 0))) (by
      show (x3 i.succ (1, 0), x3 j.succ (1, 0)) = (x3 i.succ (0, x3 i.succ (1, 0)), x3 j.succ (0, x3 i.succ (1, 0)))
      rw [hn i.succ (Fin.succ_ne_zero i), hn j.succ (Fin.succ_ne_zero j), ← hij'])
  exact h10 (congrArg Prod.fst h1)

end PEqualNP.Outside.L_meta_7422

theorem PEqualNP.Outside.L_meta_7422 : ∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : Fin (x1 + (1 : ℕ)) → Fin x1 × Fin x1 → Fin x1), (2 : ℕ) ≤ x1 → (∀ (x5 x6 : Fin (x1 + (1 : ℕ))), x5 ≠ x6 → Function.Bijective fun (x8 : Fin x1 × Fin x1) => (x3 x5 x8, x3 x6 x8)) → (∀ (x6 : Fin x1 × Fin x1), x3 (0 : Fin (x1 + (1 : ℕ))) x6 = x6.1 ∧ x3 (1 : Fin (x1 + (1 : ℕ))) x6 = x6.2) → (∀ (x7 : Fin (x1 + (1 : ℕ))), x7 ≠ (0 : Fin (x1 + (1 : ℕ))) → ∀ (x9 : Fin x1), x3 x7 ((0 : Fin x1), x9) = x9) → ∃ (x8 : Fin (x1 + (1 : ℕ)) ≃ Fin (x1 + (1 : ℕ))), x8 (0 : Fin (x1 + (1 : ℕ))) = (0 : Fin (x1 + (1 : ℕ))) ∧ x8 (1 : Fin (x1 + (1 : ℕ))) = (1 : Fin (x1 + (1 : ℕ))) ∧ ∀ (x9 : Fin x1), x3 (x8 x9.succ) ((1 : Fin x1), (0 : Fin x1)) = x9 := by
  intro x1 x2 x3 h2 hb hc hn
  have h10 : (1 : Fin x1) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_zero] at hv
    have h1v : ((1 : Fin x1) : ℕ) = 1 % x1 := Fin.val_one' x1
    rw [h1v, Nat.mod_eq_of_lt (by omega)] at hv
    exact absurd hv (by omega)
  have hinj := PEqualNP.Outside.L_meta_7422.aux x1 x3 h10 hb hn
  have hbij := Finite.injective_iff_bijective.mp hinj
  obtain ⟨h, hh⟩ : ∃ h : Fin x1 ≃ Fin x1, ∀ i, x3 (h i).succ (1, 0) = i :=
    ⟨(Equiv.ofBijective _ hbij).symm, fun i => (Equiv.ofBijective _ hbij).apply_symm_apply i⟩
  have f0 : x3 (0 : Fin x1).succ (1, 0) = 0 := by
    rw [Fin.succ_zero_eq_one', (hc _).2]
  have h0 : h 0 = 0 := hinj ((hh 0).trans f0.symm)
  have hσ : ∀ i : Fin x1, ((finSuccEquiv x1).trans ((Equiv.optionCongr h).trans (finSuccEquiv x1).symm)) i.succ = (h i).succ := by
    intro i
    simp [finSuccEquiv_succ, finSuccEquiv_symm_some]
  refine ⟨(finSuccEquiv x1).trans ((Equiv.optionCongr h).trans (finSuccEquiv x1).symm), ?_, ?_, ?_⟩
  · simp [finSuccEquiv_zero]
  · rw [← Fin.succ_zero_eq_one', hσ, h0]
  · intro i
    rw [hσ]
    exact hh i
