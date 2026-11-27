import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Helpers: the shared interface for the Beame-Whitmeyer rectangle-dag bound (L-lib-090)

Bit pigeonhole with `n + 1` pigeons. Each player holds `t` bits of every pigeon's hole label: a
`Half n t` is `Fin (n + 1) → Fin t → Bool`. An edge is an ordered pair of pigeons. Edge lists are
written NEWEST FIRST: adding an edge is `e :: E`.
-/

namespace PEqualNP.Search.Helpers.BW

open Classical

/-- One player's part of a point: `t` bits for each of the `n + 1` pigeons. -/
abbrev Half (n t : ℕ) : Type := Fin (n + 1) → Fin t → Bool

/-- An edge: an ordered pair of pigeons. -/
abbrev Edge (n : ℕ) : Type := Fin (n + 1) × Fin (n + 1)

variable {n t : ℕ}

/-- The colliding pairs of `x`: different pigeons with the same `t` bits. -/
noncomputable def Coll (x : Half n t) : Finset (Edge n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ x p.1 = x p.2

/-- `x` covers `B` with at most `d` of its colliding pairs: some set `S` of at most `d`
colliding pairs of `x` such that every `y ∈ B` collides on some pair of `S`. -/
def CovLE (B : Set (Half n t)) (x : Half n t) (d : ℕ) : Prop :=
  ∃ S ⊆ Coll x, S.card ≤ d ∧ ∀ y ∈ B, ∃ p ∈ S, y p.1 = y p.2

/-- `x` collides on every edge of `E`. -/
def Sat (E : List (Edge n)) (x : Half n t) : Prop :=
  ∀ p ∈ E, x p.1 = x p.2

/-- The edge `p` is implied by `E`: its ends are joined by a path of edges of `E`. -/
def Implied (E : List (Edge n)) (p : Edge n) : Prop :=
  Relation.EqvGen (fun a b => (a, b) ∈ E) p.1 p.2

/-- The rank of `E` (newest first): the number of edges not implied by the older ones. -/
noncomputable def rank : List (Edge n) → ℕ
  | [] => 0
  | e :: E => rank E + if Implied E e then 0 else 1

/-- An abstract rectangle dag for bit pigeonhole, newest first. A node is a pair `(A, B)`
standing for the rectangle `A × B`. A sink is a rectangle on which two different pigeons
collide in both halves; a split node is covered by two earlier nodes. -/
inductive ADag (n t : ℕ) : List (Set (Half n t) × Set (Half n t)) → Prop
  | nil : ADag n t []
  | sink {ρ} {A B : Set (Half n t)} (i j : Fin (n + 1)) :
      ADag n t ρ → i ≠ j → (∀ x ∈ A, x i = x j) → (∀ y ∈ B, y i = y j) →
      ADag n t ((A, B) :: ρ)
  | split {ρ} {A B A₁ B₁ A₂ B₂ : Set (Half n t)} :
      ADag n t ρ → (A₁, B₁) ∈ ρ → (A₂, B₂) ∈ ρ → A ×ˢ B ⊆ A₁ ×ˢ B₁ ∪ A₂ ×ˢ B₂ →
      ADag n t ((A, B) :: ρ)

/-- An abstract rectangle dag that has the whole space as a node. -/
def ADagFor (n t : ℕ) (σ : List (Set (Half n t) × Set (Half n t))) : Prop :=
  ADag n t σ ∧ ((Set.univ : Set (Half n t)), (Set.univ : Set (Half n t))) ∈ σ

end PEqualNP.Search.Helpers.BW
