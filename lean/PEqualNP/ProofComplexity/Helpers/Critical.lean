import PEqualNP.ProofComplexity.Helpers.Resolution
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Helpers: critical assignments of the pigeonhole formula and the wide clause lemma

The argument is the simplified proof of Haken's theorem by Beame and Pitassi (FOCS 1996),
arranged so that no refutation is ever restricted: everything is said about the one given
refutation, relative to a partial matching `ρ` of pigeons to holes.

* A critical assignment is an equivalence `e : Fin (n + 1) ≃ Option (Fin n)`: pigeon `i` sits
  in hole `j` when `e i = some j`, and the one pigeon with `e i = none` is left out.
* `Imp ρ S C`: every critical assignment extending `ρ` that seats all pigeons of `S`
  satisfies `C`.
* `mono C`: the monotone image of `C`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-- The variables of the pigeonhole formula. -/
abbrev PVar (n : ℕ) : Type := Fin (n + 1) × Fin n

/-- A critical assignment. -/
abbrev Crit (n : ℕ) : Type := Fin (n + 1) ≃ Option (Fin n)

/-- The truth assignment of a critical assignment. -/
def asg {n : ℕ} (e : Crit n) : PVar n → Bool := fun p => decide (e p.1 = some p.2)

/-- `e` extends the partial matching `ρ`. -/
def Ext {n : ℕ} (ρ : Finset (PVar n)) (e : Crit n) : Prop := ∀ p ∈ ρ, e p.1 = some p.2

/-- The pigeons not matched by `ρ`. -/
def freeP {n : ℕ} (ρ : Finset (PVar n)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => ∀ p ∈ ρ, p.1 ≠ i)

/-- The holes not used by `ρ`. -/
def freeH {n : ℕ} (ρ : Finset (PVar n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∀ p ∈ ρ, p.2 ≠ j)

/-- `ρ` is a partial matching in the sense needed: each free pigeon is left out by some
critical assignment extending `ρ`. -/
def Valid {n : ℕ} (ρ : Finset (PVar n)) : Prop := ∀ i ∈ freeP ρ, ∃ e : Crit n, Ext ρ e ∧ e i = none

/-- Every critical assignment extending `ρ` that seats all of `S` satisfies `C`. -/
def Imp {n : ℕ} (ρ : Finset (PVar n)) (S : Finset (Fin (n + 1))) (C : Clause (PVar n)) : Prop :=
  ∀ e : Crit n, Ext ρ e → (∀ i ∈ S, e i ≠ none) → ClauseSat (asg e) C

/-- The monotone image of a clause: `(i, j)` is in it when `C` holds the positive literal on
`(i, j)` or a negative literal on `(i', j)` for another pigeon `i'`. -/
def mono {n : ℕ} (C : Clause (PVar n)) : Finset (PVar n) :=
  Finset.univ.filter (fun p => (p, true) ∈ C ∨ ∃ i : Fin (n + 1), i ≠ p.1 ∧ ((i, p.2), false) ∈ C)

/-- The part of the monotone image on free pigeons and free holes. -/
def monoFree {n : ℕ} (ρ : Finset (PVar n)) (C : Clause (PVar n)) : Finset (PVar n) :=
  (mono C).filter (fun p => p.1 ∈ freeP ρ ∧ p.2 ∈ freeH ρ)

theorem mem_freeP {n : ℕ} {ρ : Finset (PVar n)} {i : Fin (n + 1)} :
    i ∈ freeP ρ ↔ ∀ p ∈ ρ, p.1 ≠ i := by simp [freeP]

theorem mem_freeH {n : ℕ} {ρ : Finset (PVar n)} {j : Fin n} :
    j ∈ freeH ρ ↔ ∀ p ∈ ρ, p.2 ≠ j := by simp [freeH]

theorem mem_mono {n : ℕ} {C : Clause (PVar n)} {p : PVar n} :
    p ∈ mono C ↔ ((p, true) ∈ C ∨ ∃ i : Fin (n + 1), i ≠ p.1 ∧ ((i, p.2), false) ∈ C) := by
  simp [mono]

/-- A critical assignment that seats pigeon `i` in hole `j` satisfies every clause whose
monotone image holds `(i, j)`. -/
theorem sat_of_mem_mono {n : ℕ} {C : Clause (PVar n)} {e : Crit n} {p : PVar n}
    (hp : p ∈ mono C) (he : e p.1 = some p.2) : ClauseSat (asg e) C := by
  rcases mem_mono.mp hp with h | ⟨i, hi, h⟩
  · exact ⟨(p, true), h, by simp [asg, he]⟩
  · refine ⟨((i, p.2), false), h, ?_⟩
    have : e i ≠ some p.2 := fun h' => hi (e.injective (h'.trans he.symm))
    simp [asg, this]

/-- Pigeon axioms have complexity at most one, hole axioms zero. -/
theorem imp_axiom {n : ℕ} (ρ : Finset (PVar n)) {C : Clause (PVar n)} (hC : C ∈ PHP (n + 1) n) :
    ∃ S : Finset (Fin (n + 1)), Imp ρ S C ∧ S.card ≤ 1 := by
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hii, rfl⟩
  · refine ⟨{i}, ?_, by simp⟩
    intro e _ hS
    have hi : e i ≠ none := hS i (Finset.mem_singleton_self i)
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hi
    exact ⟨((i, j), true), Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, by simp [asg, hj]⟩
  · refine ⟨∅, ?_, by simp⟩
    intro e _ _
    by_cases h : e i = some j
    · refine ⟨((i', j), false), by simp, ?_⟩
      have : e i' ≠ some j := fun h' => hii (e.injective (h.trans h'.symm))
      simp [asg, this]
    · exact ⟨((i, j), false), by simp, by simp [asg, h]⟩

/-- Complexity is subadditive under the resolution rule. -/
theorem imp_resolvent {n : ℕ} (ρ : Finset (PVar n)) {S T : Finset (Fin (n + 1))}
    {C D R : Clause (PVar n)} (hR : IsResolvent C D R) (hC : Imp ρ S C) (hD : Imp ρ T D) :
    Imp ρ (S ∪ T) R := by
  intro e he hST
  exact resolvent_sound _ hR
    (hC e he fun i hi => hST i (Finset.mem_union_left _ hi))
    (hD e he fun i hi => hST i (Finset.mem_union_right _ hi))

/-- Whatever implies the empty clause holds every free pigeon. -/
theorem freeP_subset_of_imp_empty {n : ℕ} {ρ : Finset (PVar n)} (hρ : Valid ρ)
    {S : Finset (Fin (n + 1))} (hS : Imp ρ S ∅) : freeP ρ ⊆ S := by
  intro i hi
  by_contra hiS
  obtain ⟨e, he, hei⟩ := hρ i hi
  have hsat : ClauseSat (asg e) ∅ := by
    apply hS e he
    intro i' hi' h'
    exact hiS (e.injective (hei.trans h'.symm) ▸ hi')
  obtain ⟨l, hl, -⟩ := hsat
  simp at hl

/-- A least set implying `C`, below any given one. -/
theorem exists_min_imp {n : ℕ} (ρ : Finset (PVar n)) {S : Finset (Fin (n + 1))}
    {C : Clause (PVar n)} (hS : Imp ρ S C) :
    ∃ S₀ : Finset (Fin (n + 1)), Imp ρ S₀ C ∧ S₀.card ≤ S.card ∧
      ∀ S' : Finset (Fin (n + 1)), Imp ρ S' C → S₀.card ≤ S'.card := by
  classical
  have hex : ∃ k, ∃ S' : Finset (Fin (n + 1)), Imp ρ S' C ∧ S'.card = k := ⟨_, S, hS, rfl⟩
  obtain ⟨S₀, hS₀, hcard⟩ := Nat.find_spec hex
  refine ⟨S₀, hS₀, ?_, ?_⟩
  · rw [hcard]; exact Nat.find_min' hex ⟨S, hS, rfl⟩
  · intro S' hS'
    rw [hcard]; exact Nat.find_min' hex ⟨S', hS', rfl⟩

/-- A clause is medium: its least implying set has size in `(f/3, 2f/3]`. -/
def Medium {n : ℕ} (ρ : Finset (PVar n)) (C : Clause (PVar n)) : Prop :=
  ∃ S : Finset (Fin (n + 1)), Imp ρ S C ∧
    (∀ S' : Finset (Fin (n + 1)), Imp ρ S' C → S.card ≤ S'.card) ∧
    (freeP ρ).card < 3 * S.card ∧ 3 * S.card ≤ 2 * (freeP ρ).card

/-- In a derivation from the pigeonhole formula, either some clause is medium or every clause
is implied by at most a third of the free pigeons. -/
theorem medium_or_small {n : ℕ} (ρ : Finset (PVar n)) (hf : 2 ≤ (freeP ρ).card)
    {π : List (Clause (PVar n))} (hπ : IsDerivation (PHP (n + 1) n) π) :
    (∃ C ∈ π, Medium ρ C) ∨
      ∀ C ∈ π, ∃ S : Finset (Fin (n + 1)), Imp ρ S C ∧ 3 * S.card ≤ (freeP ρ).card := by
  have step : ∀ (C : Clause (PVar n)) (S : Finset (Fin (n + 1))), Imp ρ S C →
      3 * S.card ≤ 2 * (freeP ρ).card →
      Medium ρ C ∨ ∃ S : Finset (Fin (n + 1)), Imp ρ S C ∧ 3 * S.card ≤ (freeP ρ).card := by
    intro C S hS hcard
    obtain ⟨S₀, hS₀, hle, hmin⟩ := exists_min_imp ρ hS
    by_cases h : 3 * S₀.card ≤ (freeP ρ).card
    · exact Or.inr ⟨S₀, hS₀, h⟩
    · exact Or.inl ⟨S₀, hS₀, hmin, by omega, by omega⟩
  induction hπ with
  | nil => exact Or.inr (by simp)
  | @ax π C _ hC ih =>
    rcases ih with ⟨E, hE, hmed⟩ | hsmall
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hmed⟩
    · obtain ⟨S, hS, hcard⟩ := imp_axiom ρ hC
      rcases step C S hS (by omega) with hmed | hsm
      · exact Or.inl ⟨C, List.mem_cons_self, hmed⟩
      · refine Or.inr fun E hE => ?_
        rcases List.mem_cons.mp hE with rfl | hE
        · exact hsm
        · exact hsmall E hE
  | @res π C D R _ hC hD hR ih =>
    rcases ih with ⟨E, hE, hmed⟩ | hsmall
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hmed⟩
    · obtain ⟨S, hS, hScard⟩ := hsmall C hC
      obtain ⟨T, hT, hTcard⟩ := hsmall D hD
      have hU := imp_resolvent ρ hR hS hT
      have hUcard : (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le S T
      rcases step R (S ∪ T) hU (by omega) with hmed | hsm
      · exact Or.inl ⟨R, List.mem_cons_self, hmed⟩
      · refine Or.inr fun E hE => ?_
        rcases List.mem_cons.mp hE with rfl | hE
        · exact hsm
        · exact hsmall E hE

/-- A refutation of the pigeonhole formula holds a medium clause. -/
theorem exists_medium {n : ℕ} {ρ : Finset (PVar n)} (hρ : Valid ρ) (hf : 2 ≤ (freeP ρ).card)
    {π : List (Clause (PVar n))} (hπ : IsRefutation (PHP (n + 1) n) π) :
    ∃ C ∈ π, Medium ρ C := by
  rcases medium_or_small ρ hf hπ.1 with h | h
  · exact h
  · obtain ⟨S, hS, hcard⟩ := h ∅ hπ.2
    have := Finset.card_le_card (freeP_subset_of_imp_empty hρ hS)
    omega

end PEqualNP.ProofComplexity.Helpers
