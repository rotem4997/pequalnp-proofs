import PEqualNP.ProofComplexity.Helpers.Lin

/-!
# Helpers: the parity line of a set of pigeons

For a set `S` of pigeons, the linear equation "the sum of all variables of the pigeons of `S`
equals `|S|` modulo two" is implied by seating all of `S`, and every set of pigeons whose
seating implies it contains `S`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-- Under a critical assignment, the true variables among the pigeons of `S` are in bijection
with the seated pigeons of `S`. -/
theorem card_true_vars {n : ℕ} (e : Fin (n + 1) ≃ Option (Fin n)) (S : Finset (Fin (n + 1))) :
    ((S ×ˢ (Finset.univ : Finset (Fin n))).filter
      (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2) = true)).card =
      (S.filter (fun i => e i ≠ none)).card := by
  apply Finset.card_nbij (i := Prod.fst)
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, and_true,
      decide_eq_true_eq, Set.mem_ofPred_eq] at hp ⊢
    exact ⟨hp.1, by rw [hp.2]; exact Option.some_ne_none _⟩
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, and_true,
      decide_eq_true_eq, Set.mem_ofPred_eq] at hp hq
    have h := hp.2
    rw [hpq, hq.2] at h
    exact Prod.ext hpq (Option.some.inj h).symm
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hi.2
    refine ⟨(i, j), ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, and_true,
      decide_eq_true_eq, Set.mem_ofPred_eq]
    exact ⟨hi.1, hj⟩

/-- Seating all of `S` satisfies the parity line of `S`. -/
theorem parity_line_sat {n : ℕ} (S : Finset (Fin (n + 1))) (e : Fin (n + 1) ≃ Option (Fin n))
    (he : ∀ i ∈ S, e i ≠ none) :
    LinClauseSat (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2))
      {(S ×ˢ (Finset.univ : Finset (Fin n)), decide (S.card % 2 = 1))} := by
  refine ⟨_, Finset.mem_singleton_self _, ?_⟩
  change (Odd ((S ×ˢ (Finset.univ : Finset (Fin n))).filter
      (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2) = true)).card ↔
    decide (S.card % 2 = 1) = true)
  rw [card_true_vars, Finset.filter_true_of_mem he, decide_eq_true_eq, Nat.odd_iff]

/-- Every set of pigeons whose seating implies the parity line of `S` contains `S`. -/
theorem parity_line_min {n : ℕ} (S T : Finset (Fin (n + 1)))
    (hT : ∀ e : Fin (n + 1) ≃ Option (Fin n), (∀ i ∈ T, e i ≠ none) →
      LinClauseSat (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2))
        {(S ×ˢ (Finset.univ : Finset (Fin n)), decide (S.card % 2 = 1))}) : S ⊆ T := by
  intro i hiS
  by_contra hiT
  obtain ⟨e, -, hei⟩ := valid_empty (n := n) i (by rw [freeP_empty]; exact Finset.mem_univ i)
  have hsat := hT e (fun i' hi' h' => hiT (e.injective (hei.trans h'.symm) ▸ hi'))
  obtain ⟨q, hq, hsat⟩ := hsat
  rw [Finset.mem_singleton] at hq
  subst hq
  have hfilter : S.filter (fun i' => e i' ≠ none) = S.erase i := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hne⟩
      exact ⟨fun h => hne (h ▸ hei), hx⟩
    · rintro ⟨hne, hx⟩
      exact ⟨hx, fun h => hne (e.injective (h.trans hei.symm))⟩
  change (Odd ((S ×ˢ (Finset.univ : Finset (Fin n))).filter
      (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2) = true)).card ↔
    decide (S.card % 2 = 1) = true) at hsat
  rw [card_true_vars, hfilter, Finset.card_erase_of_mem hiS, decide_eq_true_eq,
    Nat.odd_iff] at hsat
  have := Finset.card_pos.mpr ⟨i, hiS⟩
  omega

end PEqualNP.ProofComplexity.Helpers
