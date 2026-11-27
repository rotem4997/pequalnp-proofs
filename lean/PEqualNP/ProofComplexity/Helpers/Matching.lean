import PEqualNP.ProofComplexity.Helpers.WideClause

/-!
# Helpers: partial matchings of pigeons to holes

The empty matching is valid, a valid matching stays valid when a free pigeon is seated in a
free hole, and the wide clause lemma relative to a valid matching.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

theorem freeP_empty {n : ℕ} : freeP (∅ : Finset (PVar n)) = Finset.univ := by
  ext i; simp [freeP]

theorem freeH_empty {n : ℕ} : freeH (∅ : Finset (PVar n)) = Finset.univ := by
  ext j; simp [freeH]

theorem valid_empty {n : ℕ} : Valid (∅ : Finset (PVar n)) := by
  intro i _
  refine ⟨(Equiv.swap i 0).trans (finSuccEquiv n), ?_, ?_⟩
  · intro p hp; simp at hp
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]; exact finSuccEquiv_zero

theorem freeP_insert {n : ℕ} (ρ : Finset (PVar n)) (i : Fin (n + 1)) (j : Fin n) :
    freeP (insert (i, j) ρ) = (freeP ρ).erase i := by
  ext x
  simp only [mem_freeP, Finset.mem_erase, Finset.mem_insert, forall_eq_or_imp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩

theorem freeH_insert_subset {n : ℕ} (ρ : Finset (PVar n)) (p : PVar n) :
    freeH (insert p ρ) ⊆ freeH ρ := by
  intro x hx
  exact mem_freeH.mpr fun q hq => mem_freeH.mp hx q (Finset.mem_insert_of_mem hq)

theorem valid_insert {n : ℕ} {ρ : Finset (PVar n)} (hρ : Valid ρ) {i : Fin (n + 1)} {j : Fin n}
    (hi : i ∈ freeP ρ) (hj : j ∈ freeH ρ) : Valid (insert (i, j) ρ) := by
  intro i₀ hi₀
  rw [freeP_insert, Finset.mem_erase] at hi₀
  obtain ⟨hne, hi₀free⟩ := hi₀
  obtain ⟨e, he, hei₀⟩ := hρ i₀ hi₀free
  -- the pigeon currently in hole `j`
  have hk : e (e.symm (some j)) = some j := e.apply_symm_apply _
  have hkfree : ∀ p ∈ ρ, p.1 ≠ e.symm (some j) := by
    intro p hp hpk
    have h1 := he p hp
    rw [hpk, hk] at h1
    exact mem_freeH.mp hj p hp (Option.some.inj h1).symm
  have hk0 : i₀ ≠ e.symm (some j) := by
    intro h
    rw [← h, hei₀] at hk
    exact Option.some_ne_none j hk.symm
  refine ⟨(Equiv.swap i (e.symm (some j))).trans e, ?_, ?_⟩
  · intro p hp
    rw [Equiv.trans_apply]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rw [Equiv.swap_apply_left]; exact hk
    · rw [Equiv.swap_apply_of_ne_of_ne (mem_freeP.mp hi p hp) (hkfree p hp)]
      exact he p hp
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hne hk0]
    exact hei₀

/-- The wide clause lemma relative to a valid matching with at least two free pigeons. -/
theorem exists_wide {n : ℕ} {ρ : Finset (PVar n)} (hρ : Valid ρ) (hf : 2 ≤ (freeP ρ).card)
    {π : List (Clause (PVar n))} (hπ : IsRefutation (PHP (n + 1) n) π) :
    ∃ C ∈ π, (∀ p ∈ ρ, p ∉ mono C) ∧ 2 * (freeP ρ).card ^ 2 ≤ 9 * (monoFree ρ C).card := by
  obtain ⟨C, hC, hmed⟩ := exists_medium hρ hf hπ
  exact ⟨C, hC, medium_wide hmed⟩

end PEqualNP.ProofComplexity.Helpers
