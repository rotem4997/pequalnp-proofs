import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9198

open PEqualNP.ProofComplexity PEqualNP.Search

abbrev W := Fin 4 × Fin 3
def tb : Option (W × Bool) → W × Bool → Bool
  | none, _ => false
  | some l, x => decide (x = l) || (l.2 && !x.2 && decide (x.1.2 = l.1.2) && !decide (x.1.1 = l.1.1))

def OkC (D : Clause W) (o : Option (W × Bool)) : Prop :=
  (∀ a ∈ D, (∀ b ∈ D, b ≠ a → tb o (negLit b) = true) → tb o a = true) ∧ ∃ a ∈ D, tb o (negLit a) = false

theorem no_rup (Γ : Set (Clause W)) (o : Option (W × Bool)) (h : ∀ D ∈ Γ, OkC D o) (C : Clause W) (hC : ∀ l ∈ C, tb o (negLit l) = true) : ¬ IsRUP Γ C := by
  rintro ⟨D, hD, hf⟩
  have key : ∀ l, UPForces Γ (negLit '' (↑C : Set (Literal W))) l → tb o l = true := by
    intro l hl
    induction hl with
    | hyp h' =>
      obtain ⟨x, hx, rfl⟩ := h'
      exact hC x hx
    | unit hD hl _ ih => exact (h _ hD).1 _ hl ih
  obtain ⟨a, ha, hn⟩ := (h D hD).2
  rw [key _ (hf a ha)] at hn
  cases hn

theorem fP : ∀ (o : Option (W × Bool)) (i : Fin 4), (∀ a ∈ Finset.univ.image (fun j : Fin 3 => ((i, j), true)), (∀ b ∈ Finset.univ.image (fun j : Fin 3 => ((i, j), true)), b ≠ a → tb o (b.1, !b.2) = true) → tb o a = true) ∧
    ∃ a ∈ Finset.univ.image (fun j : Fin 3 => ((i, j), true)), tb o (a.1, !a.2) = false := by decide +kernel
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fH : ∀ (o : Option (W × Bool)) (i i' : Fin 4) (j : Fin 3), i ≠ i' → (∀ a ∈ ({((i, j), false), ((i', j), false)} : Finset (W × Bool)), (∀ b ∈ ({((i, j), false), ((i', j), false)} : Finset (W × Bool)), b ≠ a → tb o (b.1, !b.2) = true) → tb o a = true) ∧
    ∃ a ∈ ({((i, j), false), ((i', j), false)} : Finset (W × Bool)), tb o (a.1, !a.2) = false := by decide +kernel

theorem okF (o : Option (W × Bool)) : ∀ D ∈ PHP (3 + 1) 3, OkC D o := by
  rintro D (⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩)
  · exact fP o i
  · exact fH o i i' j hne

theorem selfT (l : W × Bool) : tb (some l) l = true := by simp [tb]
theorem negT (l : W × Bool) : tb (some l) (negLit l) = false := by
  obtain ⟨v, s⟩ := l
  cases s <;> simp [tb, negLit]
theorem nn (l : W × Bool) : negLit (negLit l) = l := by
  obtain ⟨v, s⟩ := l; simp [negLit]

theorem two (D : Clause W) (hD : 2 ≤ D.card) : OkC D none := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hD
  refine ⟨fun x hx h => ?_, a, ha, rfl⟩
  exfalso
  by_cases hxa : a = x
  · have := h b hb (by rw [← hxa]; exact hab.symm)
    cases this
  · have := h a ha hxa
    cases this

theorem sing (l : W × Bool) : OkC {l} (some l) := by
  refine ⟨fun a ha _ => ?_, l, by simp, negT l⟩
  rw [Finset.mem_singleton] at ha
  rw [ha]; exact selfT l

/-- A clause of at least two literals is quiet after `v` or after its negation. -/
theorem split (D : Clause W) (hD : 2 ≤ D.card) (v : W) : OkC D (some (v, true)) ∨ OkC D (some (v, false)) := by
  by_cases hv : ((v, true) : W × Bool) ∈ D
  · left
    refine ⟨fun a ha h => ?_, _, hv, negT _⟩
    by_cases e : a = (v, true)
    · rw [e]; exact selfT _
    · have := h _ hv (Ne.symm e)
      rw [negT] at this
      cases this
  · right
    have ne : ∀ b ∈ D, tb (some (v, false)) (negLit b) = false := by
      intro b hb
      by_contra hcon
      have hc : tb (some (v, false)) (negLit b) = true := by simpa using hcon
      simp only [tb, Bool.false_and, Bool.or_false, decide_eq_true_eq] at hc
      have : b = (v, true) := by rw [← nn b, hc]; rfl
      exact hv (this ▸ hb)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hD
    refine ⟨fun x hx h => ?_, a, ha, ne a ha⟩
    exfalso
    by_cases hxa : a = x
    · have := h b hb (by rw [← hxa]; exact hab.symm)
      rw [ne b hb] at this; cases this
    · have := h a ha hxa
      rw [ne a ha] at this; cases this

theorem split2 (D : Clause W) (hD : 2 ≤ D.card) (l : W × Bool) : OkC D (some l) ∨ OkC D (some (negLit l)) := by
  obtain ⟨v, s⟩ := l
  cases s
  · exact (split D hD v).symm
  · exact split D hD v

/-- The first learned clause has at least two literals. -/
theorem first (C : Clause W) (h : IsRUP (PHP (3 + 1) 3) C) : 2 ≤ C.card := by
  by_contra hcon
  have h1 : C.card = 0 ∨ C.card = 1 := by omega
  rcases h1 with h0 | h0
  · rw [Finset.card_eq_zero] at h0
    exact no_rup _ none (okF none) C (by rw [h0]; simp) h
  · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h0
    exact no_rup _ (some (negLit l)) (okF _) _ (fun x hx => by rw [Finset.mem_singleton] at hx; rw [hx]; exact selfT _) h

theorem main (σ : List (Clause W)) (hσ : IsRUPRun (PHP (3 + 1) 3) σ) (he : ∅ ∉ σ) (hl : σ.length ≤ 2) : ¬ IsRUP (PHP (3 + 1) 3 ∪ {D | D ∈ σ}) ∅ := by
  cases hσ with
  | nil => exact no_rup _ none (fun D hD => okF _ D (by simpa using hD)) _ (by simp)
  | @learn σ C hσ hC =>
    cases hσ with
    | nil =>
      have h2 := first C (by simpa using hC)
      refine no_rup _ none (fun D hD => ?_) _ (by simp)
      rcases hD with hD | hD
      · exact okF _ D hD
      · simp only [List.mem_singleton, Set.mem_setOf_eq] at hD
        rw [hD]; exact two C h2
    | @learn σ C1 hσ hC1 =>
      have hσ0 : σ = [] := by
        simp only [List.length_cons] at hl
        exact List.length_eq_zero_iff.1 (by omega)
      subst hσ0
      have h2 := first C1 (by simpa using hC1)
      have hCne : C ≠ ∅ := fun h => he (by rw [h]; simp)
      by_cases hc : 2 ≤ C.card
      · refine no_rup _ none (fun D hD => ?_) _ (by simp)
        rcases hD with hD | hD
        · exact okF _ D hD
        · simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hD
          rcases hD with rfl | rfl
          · exact two _ hc
          · exact two _ h2
      · have h1 : C.card = 1 := by
          have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hCne)
          omega
        obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h1
        rcases split2 C1 h2 l with ho | ho
        · refine no_rup _ (some l) (fun D hD => ?_) _ (by simp)
          rcases hD with hD | hD
          · exact okF _ D hD
          · simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hD
            rcases hD with rfl | rfl
            · exact sing l
            · exact ho
        · exfalso
          refine no_rup _ (some (negLit l)) (fun D hD => ?_) {l} (fun x hx => by rw [Finset.mem_singleton] at hx; rw [hx]; exact selfT _) hC
          rcases hD with hD | hD
          · exact okF _ D hD
          · simp only [List.mem_singleton, Set.mem_setOf_eq] at hD
            rw [hD]; exact ho

theorem fin (ρ : List (Clause W)) (hρ : IsRUPRun (PHP (3 + 1) 3) ρ) : ∅ ∈ ρ → 4 ≤ ρ.length := by
  induction hρ with
  | nil => intro h; simp at h
  | @learn ρ C hρ hC ih =>
    intro h
    by_cases hin : ∅ ∈ ρ
    · have := ih hin
      rw [List.length_cons]; omega
    rcases List.mem_cons.1 h with e | e
    · by_contra hcon
      rw [List.length_cons] at hcon
      exact main ρ hρ hin (by omega) (e ▸ hC)
    · exact absurd e hin

end PEqualNP.Outside.L_meta_9198

theorem PEqualNP.Outside.L_meta_9198 : ¬ (∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (3 + 1) 3) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)) ∈ ρ ∧ ρ.length ≤ 3) := by
  rintro ⟨ρ, h1, h2, h3⟩
  have := PEqualNP.Outside.L_meta_9198.fin ρ h1 h2
  omega
