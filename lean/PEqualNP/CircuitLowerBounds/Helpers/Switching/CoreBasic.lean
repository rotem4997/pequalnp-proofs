import Mathlib

/-!
# Switching lemma: definitions and basic facts

DNFs over the variables `Fin n` as ordered lists of terms, restrictions, the canonical decision
tree depth, and the count of restrictions with a given number of stars. Our own formalization of
standard notions (Hastad's switching lemma in the counting form due to Razborov).
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Core

variable {n : ℕ}

/-- A literal: a variable and the value it requires. -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- A term: a conjunction of literals. -/
abbrev Term (n : ℕ) := List (Lit n)

/-- A DNF: an ordered disjunction of terms. -/
abbrev DNF (n : ℕ) := List (Term n)

/-- A restriction: `none` is a star (the variable stays free). -/
abbrev Restr (n : ℕ) := Fin n → Option Bool

/-- The number of stars of a restriction. -/
def stars (ρ : Restr n) : ℕ := (Finset.univ.filter fun v => ρ v = none).card

/-- The restrictions with exactly `l` stars. -/
def R (n l : ℕ) : Finset (Restr n) := Finset.univ.filter fun ρ => stars ρ = l

/-- The value of a term on an assignment. -/
def Term.eval (T : Term n) (x : Fin n → Bool) : Bool := T.all fun p => x p.1 == p.2

/-- The value of a DNF on an assignment. -/
def DNF.eval (F : DNF n) (x : Fin n → Bool) : Bool := F.any fun T => T.eval x

/-- The assignment `x` agrees with the fixed values of `ρ`. -/
def Compat (ρ : Restr n) (x : Fin n → Bool) : Prop := ∀ v b, ρ v = some b → x v = b

/-- A term is dead under `ρ`: one of its literals is falsified by `ρ`, or the term contains a
literal and its negation (so it is false everywhere). -/
def Term.Dead (T : Term n) (ρ : Restr n) : Prop :=
  ∃ p ∈ T, ρ p.1 = some (!p.2) ∨ (p.1, !p.2) ∈ T

instance (T : Term n) (ρ : Restr n) : Decidable (T.Dead ρ) := by
  unfold Term.Dead; infer_instance

/-- The starred variables of a term, without repetition, in order of first occurrence. -/
def Term.free (T : Term n) (ρ : Restr n) : List (Fin n) :=
  ((T.map Prod.fst).dedup).filter fun v => ρ v = none

/-- The first term of `F` that is not dead under `ρ`. -/
def firstLive (F : DNF n) (ρ : Restr n) : Option (Term n) :=
  F.find? fun T => decide (¬ T.Dead ρ)

/-- Fix the variables of the list `V` to the values given by `f`. -/
def ext (ρ : Restr n) (V : List (Fin n)) (f : Fin n → Bool) : Restr n :=
  fun v => if v ∈ V then some (f v) else ρ v

/-- The canonical decision tree depth, with fuel: query all starred variables of the first live
term, then continue on every answer. -/
def cdtAux : ℕ → DNF n → Restr n → ℕ
  | 0, _, _ => 0
  | k + 1, F, ρ =>
    match firstLive F ρ with
    | none => 0
    | some T =>
      if T.free ρ = [] then 0
      else (T.free ρ).length +
        Finset.univ.sup fun π : Fin n → Bool => cdtAux k F (ext ρ (T.free ρ) π)

/-- The canonical decision tree depth of `F` under `ρ`. -/
def cdt (F : DNF n) (ρ : Restr n) : ℕ := cdtAux n F ρ

/-- The restrictions with `l` stars under which the canonical tree has depth at least `t`. -/
def bad (F : DNF n) (l t : ℕ) : Finset (Restr n) := (R n l).filter fun ρ => t ≤ cdt F ρ

/-! ## Unfolding -/

theorem cdtAux_zero (F : DNF n) (ρ : Restr n) : cdtAux 0 F ρ = 0 := rfl

theorem cdtAux_succ_none {k : ℕ} {F : DNF n} {ρ : Restr n} (h : firstLive F ρ = none) :
    cdtAux (k + 1) F ρ = 0 := by
  simp only [cdtAux, h]

theorem cdtAux_succ_some {k : ℕ} {F : DNF n} {ρ : Restr n} {T : Term n}
    (h : firstLive F ρ = some T) :
    cdtAux (k + 1) F ρ = if T.free ρ = [] then 0
      else (T.free ρ).length +
        Finset.univ.sup fun π : Fin n → Bool => cdtAux k F (ext ρ (T.free ρ) π) := by
  simp only [cdtAux, h]

/-! ## Terms, liveness, free variables -/

theorem firstLive_mem {F : DNF n} {ρ : Restr n} {T : Term n} (h : firstLive F ρ = some T) :
    T ∈ F := List.mem_of_find?_eq_some h

theorem firstLive_not_dead {F : DNF n} {ρ : Restr n} {T : Term n}
    (h : firstLive F ρ = some T) : ¬ T.Dead ρ := by
  have := List.find?_some h
  simpa using this

theorem mem_free {T : Term n} {ρ : Restr n} {v : Fin n} :
    v ∈ T.free ρ ↔ (∃ b, (v, b) ∈ T) ∧ ρ v = none := by
  simp [Term.free, List.mem_filter]

theorem free_nodup (T : Term n) (ρ : Restr n) : (T.free ρ).Nodup :=
  (List.nodup_dedup _).filter _

theorem free_star {T : Term n} {ρ : Restr n} {v : Fin n} (h : v ∈ T.free ρ) : ρ v = none :=
  (mem_free.1 h).2

theorem ext_of_mem {ρ : Restr n} {V : List (Fin n)} {f : Fin n → Bool} {v : Fin n}
    (h : v ∈ V) : ext ρ V f v = some (f v) := by simp [ext, h]

theorem ext_of_not_mem {ρ : Restr n} {V : List (Fin n)} {f : Fin n → Bool} {v : Fin n}
    (h : v ∉ V) : ext ρ V f v = ρ v := by simp [ext, h]

theorem ext_nil (ρ : Restr n) (f : Fin n → Bool) : ext ρ [] f = ρ := by
  funext v; simp [ext]

/-- `ext` depends on `f` only through its values on `V`. -/
theorem ext_congr {ρ : Restr n} {V : List (Fin n)} {f g : Fin n → Bool}
    (h : ∀ v ∈ V, f v = g v) : ext ρ V f = ext ρ V g := by
  funext v
  by_cases hv : v ∈ V
  · simp [ext, hv, h v hv]
  · simp [ext, hv]

/-- Fixing a list of distinct starred variables lowers the number of stars by its length. -/
theorem stars_ext {ρ : Restr n} {V : List (Fin n)} (f : Fin n → Bool) (hV : V.Nodup)
    (hs : ∀ v ∈ V, ρ v = none) : stars (ext ρ V f) + V.length = stars ρ := by
  classical
  unfold stars
  have h1 : (Finset.univ.filter fun v => ext ρ V f v = none)
      = (Finset.univ.filter fun v => ρ v = none) \ V.toFinset := by
    ext v
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, List.mem_toFinset]
    by_cases hv : v ∈ V
    · simp [ext, hv]
    · simp [ext, hv]
  have h2 : V.toFinset ⊆ Finset.univ.filter fun v => ρ v = none := by
    intro v hv
    simp only [List.mem_toFinset] at hv
    simp [hs v hv]
  rw [h1, Finset.card_sdiff_of_subset h2, List.toFinset_card_of_nodup hV]
  have := Finset.card_le_card h2
  rw [List.toFinset_card_of_nodup hV] at this
  omega

/-- Overwriting variables that are already fixed keeps the number of stars. -/
theorem stars_ext_fixed {ρ : Restr n} {V : List (Fin n)} (f : Fin n → Bool)
    (hs : ∀ v ∈ V, ρ v ≠ none) : stars (ext ρ V f) = stars ρ := by
  unfold stars
  congr 1
  ext v
  rw [Finset.mem_filter, Finset.mem_filter]
  by_cases hv : v ∈ V
  · simp [ext, hv, hs v hv]
  · simp [ext, hv]

theorem stars_le (ρ : Restr n) : stars ρ ≤ n := by
  unfold stars
  calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Deadness is monotone under extension of the restriction. -/
theorem dead_mono {T : Term n} {ρ θ : Restr n} (h : ∀ v b, ρ v = some b → θ v = some b)
    (hd : T.Dead ρ) : T.Dead θ := by
  obtain ⟨p, hp, h1 | h2⟩ := hd
  · exact ⟨p, hp, Or.inl (h _ _ h1)⟩
  · exact ⟨p, hp, Or.inr h2⟩

/-- If liveness can only be lost, and the first live term stays live, it stays the first. -/
theorem firstLive_of_mono {F : DNF n} {ρ θ : Restr n} {T : Term n}
    (h : firstLive F ρ = some T) (hm : ∀ T' : Term n, T'.Dead ρ → T'.Dead θ)
    (hT : ¬ T.Dead θ) : firstLive F θ = some T := by
  unfold firstLive at h ⊢
  induction F with
  | nil => simp at h
  | cons A F ih =>
    rw [List.find?_cons] at h ⊢
    by_cases hA : A.Dead ρ
    · have hA' : A.Dead θ := hm A hA
      simp only [hA, not_true_eq_false, decide_false] at h
      simp only [hA', not_true_eq_false, decide_false]
      exact ih h
    · simp only [hA, not_false_eq_true, decide_true, Option.some.injEq] at h
      subst h
      simp [hT]

end PEqualNP.CircuitLowerBounds.Switching.Core
