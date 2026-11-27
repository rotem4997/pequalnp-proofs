import PEqualNP.ProofComplexity.Helpers.LiftClassPlan

/-!
# The counting piece of the plan for L-pcx-074

`stmtCount : LiftClass.StmtCount`. A choice misses an entry when its pair at every block of
the entry lies in the set of the entry. The choices missing one entry are at most a
`(4/5)^w` fraction of all choices, so a short list leaves a choice that misses no entry.
-/

namespace PEqualNP.ProofComplexity.LiftClass

open Finset

/-- The choices missing one entry, weighted by `5 ^ w`, are at most `4 ^ w` times all. -/
private theorem missed_card_le (V : Type) [Fintype V] [DecidableEq V]
    (e : Finset V × (V → Finset (Fin 10 × Fin 6))) (w : ℕ)
    (he : w ≤ e.1.card ∧ ∀ v ∈ e.1, (e.2 v).card ≤ 48) :
    (univ.filter (fun c : V → Fin 10 × Fin 6 => ∀ v ∈ e.1, c v ∈ e.2 v)).card * 5 ^ w
      ≤ 4 ^ w * 60 ^ Fintype.card V := by
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq he.1
  have hsub : (univ.filter (fun c : V → Fin 10 × Fin 6 => ∀ v ∈ e.1, c v ∈ e.2 v))
      ⊆ Fintype.piFinset (fun v => if v ∈ T then e.2 v else univ) := by
    intro c hc
    rw [mem_filter] at hc
    rw [Fintype.mem_piFinset]
    intro v
    by_cases hv : v ∈ T
    · simpa [hv] using hc.2 v (hT hv)
    · simp [hv]
  have h5 : (5 : ℕ) ^ w = ∏ v : V, (if v ∈ T then 5 else 1) := by
    rw [Finset.prod_ite_mem, univ_inter, prod_const, hTc]
  have h4 : (4 : ℕ) ^ w = ∏ v : V, (if v ∈ T then 4 else 1) := by
    rw [Finset.prod_ite_mem, univ_inter, prod_const, hTc]
  have h60 : (60 : ℕ) ^ Fintype.card V = ∏ _v : V, 60 := by
    rw [prod_const, card_univ]
  calc (univ.filter (fun c : V → Fin 10 × Fin 6 => ∀ v ∈ e.1, c v ∈ e.2 v)).card * 5 ^ w
      ≤ (Fintype.piFinset (fun v => if v ∈ T then e.2 v else univ)).card * 5 ^ w :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ = ∏ v : V, ((if v ∈ T then e.2 v else univ).card * (if v ∈ T then 5 else 1)) := by
        rw [Fintype.card_piFinset, h5, prod_mul_distrib]
    _ ≤ ∏ v : V, ((if v ∈ T then 4 else 1) * 60) := by
        refine Finset.prod_le_prod (fun v _ => ?_)
        by_cases hv : v ∈ T
        · have := he.2 v (hT hv)
          simp only [hv, ite_true]
          omega
        · simp [hv]
    _ = 4 ^ w * 60 ^ Fintype.card V := by
        rw [prod_mul_distrib, h4, h60]

/-- The choices missing some entry of the list, weighted by `5 ^ w`. -/
private theorem missed_list_card_le (V : Type) [Fintype V] [DecidableEq V] (w : ℕ)
    (ls : List (Finset V × (V → Finset (Fin 10 × Fin 6))))
    (h : ∀ e ∈ ls, w ≤ e.1.card ∧ ∀ v ∈ e.1, (e.2 v).card ≤ 48) :
    (univ.filter (fun c : V → Fin 10 × Fin 6 =>
        ∃ e ∈ ls, ∀ v ∈ e.1, c v ∈ e.2 v)).card * 5 ^ w
      ≤ ls.length * (4 ^ w * 60 ^ Fintype.card V) := by
  induction ls with
  | nil => simp
  | cons e ls ih =>
    have ih' := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := missed_card_le V e w (h e List.mem_cons_self)
    have hsub : (univ.filter (fun c : V → Fin 10 × Fin 6 =>
          ∃ e' ∈ e :: ls, ∀ v ∈ e'.1, c v ∈ e'.2 v))
        ⊆ (univ.filter (fun c : V → Fin 10 × Fin 6 => ∀ v ∈ e.1, c v ∈ e.2 v))
          ∪ (univ.filter (fun c : V → Fin 10 × Fin 6 =>
              ∃ e' ∈ ls, ∀ v ∈ e'.1, c v ∈ e'.2 v)) := by
      intro c hc
      simp only [mem_filter, mem_univ, true_and, List.mem_cons, mem_union] at hc ⊢
      obtain ⟨e', he' | he', hc'⟩ := hc
      · left; subst he'; exact hc'
      · right; exact ⟨e', he', hc'⟩
    have hcard := (card_le_card hsub).trans (card_union_le _ _)
    calc _ ≤ ((univ.filter (fun c : V → Fin 10 × Fin 6 => ∀ v ∈ e.1, c v ∈ e.2 v)).card
          + (univ.filter (fun c : V → Fin 10 × Fin 6 =>
              ∃ e' ∈ ls, ∀ v ∈ e'.1, c v ∈ e'.2 v)).card) * 5 ^ w :=
          Nat.mul_le_mul_right _ hcard
      _ ≤ (e :: ls).length * (4 ^ w * 60 ^ Fintype.card V) := by
          rw [List.length_cons, add_mul, add_mul, one_mul]
          omega

theorem stmtCount : StmtCount := by
  intro V _ _ ls w h hlen
  by_contra hno
  have hall : (univ.filter (fun c : V → Fin 10 × Fin 6 =>
      ∃ e ∈ ls, ∀ v ∈ e.1, c v ∈ e.2 v)) = univ := by
    apply filter_true_of_mem
    intro c _
    by_contra hc
    apply hno
    refine ⟨c, fun e he => ?_⟩
    by_contra hv
    apply hc
    refine ⟨e, he, fun v hve => ?_⟩
    by_contra hcv
    exact hv ⟨v, hve, hcv⟩
  have hb := missed_list_card_le V w ls h
  rw [hall, card_univ] at hb
  have hcard : Fintype.card (V → Fin 10 × Fin 6) = 60 ^ Fintype.card V := by
    simp
  rw [hcard] at hb
  have hpos : 0 < 60 ^ Fintype.card V := by positivity
  have : ls.length * (4 ^ w * 60 ^ Fintype.card V) < 60 ^ Fintype.card V * 5 ^ w := by
    calc ls.length * (4 ^ w * 60 ^ Fintype.card V)
        = (ls.length * 4 ^ w) * 60 ^ Fintype.card V := by ring
      _ < 5 ^ w * 60 ^ Fintype.card V := Nat.mul_lt_mul_of_pos_right hlen hpos
      _ = 60 ^ Fintype.card V * 5 ^ w := by ring
  omega

end PEqualNP.ProofComplexity.LiftClass
