import Mathlib
import PEqualNP.Defs

/-!
# Index description of Res(⊕) derivations

`IsLinDerivation A π` is equivalent to a statement about the lines of `π` by index: every line
is an axiom, a resolvent of two later lines, or a weakening of one later line.
-/

namespace PEqualNP.ProofComplexity.RefIndex

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- The line at index `i` of `π` is justified: an axiom, a resolvent of two lines at larger
indices, or implied by one line at a larger index. -/
def Step (A : Set (LinClause V)) (π : List (LinClause V)) (i : ℕ) : Prop :=
  π.getD i ∅ ∈ A ∨
  (∃ (j k : ℕ) (f : Finset V), i < j ∧ j < π.length ∧ i < k ∧ k < π.length ∧
    (f, false) ∈ π.getD j ∅ ∧ (f, true) ∈ π.getD k ∅ ∧
    π.getD i ∅ = (π.getD j ∅).erase (f, false) ∪ (π.getD k ∅).erase (f, true)) ∨
  (∃ j : ℕ, i < j ∧ j < π.length ∧ ∀ a : V → Bool,
    (∃ q ∈ π.getD j ∅, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true)) →
    ∃ q ∈ π.getD i ∅, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true))

omit [DecidableEq V] in
theorem mem_iff_getD (l : List (LinClause V)) (x : LinClause V) :
    x ∈ l ↔ ∃ j, j < l.length ∧ l.getD j ∅ = x := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
    exact ⟨j, hj, by simp [hj]⟩
  · rintro ⟨j, hj, rfl⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj

theorem cons_iff (A : Set (LinClause V)) (C : LinClause V) (π : List (LinClause V)) :
    IsLinDerivation A (C :: π) ↔ IsLinDerivation A π ∧
      (C ∈ A ∨ (∃ D E, D ∈ π ∧ E ∈ π ∧ IsLinResolvent D E C) ∨
        ∃ D, D ∈ π ∧ ∀ a : V → Bool, LinClauseSat a D → LinClauseSat a C) := by
  constructor
  · intro h
    cases h with
    | ax h1 h2 => exact ⟨h1, Or.inl h2⟩
    | res h1 h2 h3 h4 => exact ⟨h1, Or.inr (Or.inl ⟨_, _, h2, h3, h4⟩)⟩
    | weak h1 h2 h3 => exact ⟨h1, Or.inr (Or.inr ⟨_, h2, h3⟩)⟩
  · rintro ⟨h1, h2 | ⟨D, E, h2, h3, h4⟩ | ⟨D, h2, h3⟩⟩
    · exact IsLinDerivation.ax h1 h2
    · exact IsLinDerivation.res h1 h2 h3 h4
    · exact IsLinDerivation.weak h1 h2 h3

theorem step_succ (A : Set (LinClause V)) (C : LinClause V) (π : List (LinClause V)) (i : ℕ) :
    Step A (C :: π) (i + 1) ↔ Step A π i := by
  unfold Step
  simp only [List.getD_cons_succ, List.length_cons]
  refine or_congr Iff.rfl (or_congr ?_ ?_)
  · constructor
    · rintro ⟨j, k, f, h1, h2, h3, h4, h5, h6, h7⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [List.getD_cons_succ] at h5 h6 h7
      exact ⟨j, k, f, by omega, by omega, by omega, by omega, h5, h6, h7⟩
    · rintro ⟨j, k, f, h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨j + 1, k + 1, f, by omega, by omega, by omega, by omega,
        by simpa only [List.getD_cons_succ] using h5,
        by simpa only [List.getD_cons_succ] using h6,
        by simpa only [List.getD_cons_succ] using h7⟩
  · constructor
    · rintro ⟨j, h1, h2, h3⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.getD_cons_succ] at h3
      exact ⟨j, by omega, by omega, h3⟩
    · rintro ⟨j, h1, h2, h3⟩
      exact ⟨j + 1, by omega, by omega, by simpa only [List.getD_cons_succ] using h3⟩

theorem step_zero (A : Set (LinClause V)) (C : LinClause V) (π : List (LinClause V)) :
    Step A (C :: π) 0 ↔
      (C ∈ A ∨ (∃ D E, D ∈ π ∧ E ∈ π ∧ IsLinResolvent D E C) ∨
        ∃ D, D ∈ π ∧ ∀ a : V → Bool, LinClauseSat a D → LinClauseSat a C) := by
  unfold Step
  simp only [List.getD_cons_zero, List.length_cons]
  refine or_congr Iff.rfl (or_congr ?_ ?_)
  · constructor
    · rintro ⟨j, k, f, h1, h2, h3, h4, h5, h6, h7⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [List.getD_cons_succ] at h5 h6 h7
      exact ⟨π.getD j ∅, π.getD k ∅, (mem_iff_getD _ _).mpr ⟨j, by omega, rfl⟩,
        (mem_iff_getD _ _).mpr ⟨k, by omega, rfl⟩, f, h5, h6, h7⟩
    · rintro ⟨D, E, hD, hE, f, h5, h6, h7⟩
      obtain ⟨j, hj, rfl⟩ := (mem_iff_getD _ _).mp hD
      obtain ⟨k, hk, rfl⟩ := (mem_iff_getD _ _).mp hE
      exact ⟨j + 1, k + 1, f, by omega, by omega, by omega, by omega,
        by simpa only [List.getD_cons_succ] using h5,
        by simpa only [List.getD_cons_succ] using h6,
        by simpa only [List.getD_cons_succ] using h7⟩
  · constructor
    · rintro ⟨j, h1, h2, h3⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.getD_cons_succ] at h3
      exact ⟨π.getD j ∅, (mem_iff_getD _ _).mpr ⟨j, by omega, rfl⟩, h3⟩
    · rintro ⟨D, hD, h3⟩
      obtain ⟨j, hj, rfl⟩ := (mem_iff_getD _ _).mp hD
      exact ⟨j + 1, by omega, by omega, fun a => h3 a⟩

/-- The index description of a Res(⊕) derivation. -/
theorem derivation_iff (A : Set (LinClause V)) (π : List (LinClause V)) :
    IsLinDerivation A π ↔ ∀ i, i < π.length → Step A π i := by
  induction π with
  | nil => exact ⟨fun _ i hi => absurd hi (by simp), fun _ => IsLinDerivation.nil⟩
  | cons C π ih =>
    rw [cons_iff, ih, ← step_zero]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => exact h2
      | succ i => exact (step_succ A C π i).mpr (h1 i (by simpa using hi))
    · intro h
      exact ⟨fun i hi => (step_succ A C π i).mp (h (i + 1) (by simpa using hi)),
        h 0 (by simp)⟩

/-- Membership in the linear image of the pigeonhole formula, written out. -/
theorem mem_php_iff (n : ℕ) (L : LinClause (Fin (n + 1) × Fin n)) :
    L ∈ (fun C => linOfClause C) '' PHP (n + 1) n ↔
      ∃ C : Finset ((Fin (n + 1) × Fin n) × Bool),
        ((∃ g : Fin (n + 1), C = Finset.univ.image (fun h : Fin n => ((g, h), true))) ∨
          (∃ (g g' : Fin (n + 1)) (h : Fin n), g ≠ g' ∧ C = {((g, h), false), ((g', h), false)})) ∧
        L = C.image (fun l => (({l.1} : Finset (Fin (n + 1) × Fin n)), l.2)) := by
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩

/-- The index description of a Res(⊕) refutation of the pigeonhole formula. -/
theorem refutation_php_iff (n : ℕ) (π : List (LinClause (Fin (n + 1) × Fin n))) :
    IsLinRefutation (PHP (n + 1) n) π ↔
      ((∀ i : ℕ, i < π.length → ((∃ C : Finset ((Fin (n + 1) × Fin n) × Bool), ((∃ g : Fin (n + 1), C = Finset.univ.image (fun h : Fin n => ((g, h), true))) ∨ (∃ (g g' : Fin (n + 1)) (h : Fin n), g ≠ g' ∧ C = {((g, h), false), ((g', h), false)})) ∧ π.getD i ∅ = C.image (fun l => (({l.1} : Finset (Fin (n + 1) × Fin n)), l.2))) ∨ (∃ (j k : ℕ) (f : Finset (Fin (n + 1) × Fin n)), i < j ∧ j < π.length ∧ i < k ∧ k < π.length ∧ (f, false) ∈ π.getD j ∅ ∧ (f, true) ∈ π.getD k ∅ ∧ π.getD i ∅ = (π.getD j ∅).erase (f, false) ∪ (π.getD k ∅).erase (f, true)) ∨ (∃ j : ℕ, i < j ∧ j < π.length ∧ ∀ a : Fin (n + 1) × Fin n → Bool, (∃ q ∈ π.getD j ∅, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true)) → ∃ q ∈ π.getD i ∅, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true)))) ∧ (∅ : Finset (Finset (Fin (n + 1) × Fin n) × Bool)) ∈ π) := by
  unfold IsLinRefutation
  rw [derivation_iff]
  refine and_congr (forall_congr' fun i => imp_congr Iff.rfl ?_) Iff.rfl
  unfold Step
  exact or_congr (mem_php_iff n _) Iff.rfl

end PEqualNP.ProofComplexity.RefIndex
