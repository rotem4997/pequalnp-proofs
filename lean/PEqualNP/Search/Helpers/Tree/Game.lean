import PEqualNP.Defs
import PEqualNP.Search.Helpers.ResLinQ
import Mathlib.Tactic

/-!
# Helpers: the Prover-Delayer game for tree-like Res(lin) over the integers

A Delayer is a predicate `Good c S` on a coin count `c` and a set `S` of points. Reading a
tree from the root toward the leaves, the Delayer keeps a set `S` of points falsifying the
current line. At a resolution node every point of `S` falsifies one of the two first
equations of the premises, and the Delayer either keeps `c` coins on one side or keeps `c - 1`
coins on both sides; at a weakening node `S` stays as it is; a Good set with a coin is never
inside the falsified set of an axiom line. Then the tree has at least `2 ^ c` nodes.
-/

namespace PEqualNP.Search.Helpers.Tree

open PEqualNP.Search

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The points falsifying every equation of the line `L`. -/
def FalsSet (L : QLine V) : Set (V → Bool) := {a | ∀ e ∈ L, ¬ QEq.Holds a e}

/-- The points falsifying the equation `e`. -/
def FalsEq (e : QEq V) : Set (V → Bool) := {a | ¬ QEq.Holds a e}

theorem size_pos {F : Set (PEqualNP.ProofComplexity.Clause V)} {L : QLine V}
    (t : ResLinQTree F L) : 1 ≤ t.size := by
  cases t <;> simp [ResLinQTree.size]

/-- The game on lines: an invariant `P c L` on coin counts and lines that excludes axiom
lines while a coin is left, survives a resolution node with `c` coins on one side or `c - 1`
on both, and survives weakening. -/
theorem game_line {F : Set (PEqualNP.ProofComplexity.Clause V)} (P : ℕ → QLine V → Prop)
    (hax : ∀ c (L : QLine V) (C : PEqualNP.ProofComplexity.Clause V), 1 ≤ c → P c L →
      C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) → False)
    (hres : ∀ c (e e' : QEq V) (C D : QLine V) (α β : ℤ), 1 ≤ c →
      P c ((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) →
      P c (e :: C) ∨ P c (e' :: D) ∨ (P (c - 1) (e :: C) ∧ P (c - 1) (e' :: D)))
    (hweak : ∀ c (C D : QLine V), 1 ≤ c → P c D →
      (∀ a : V → Bool, QLine.Holds a C → QLine.Holds a D) → P c C) :
    ∀ {L : QLine V} (t : ResLinQTree F L) (c : ℕ), P c L → 2 ^ c ≤ t.size := by
  intro L t
  induction t with
  | ax C hC hL =>
    intro c hP
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [ResLinQTree.size]
    · exact (hax c _ C hc hP hC hL).elim
  | @res e e' C D α β t t' ih ih' =>
    intro c hP
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [ResLinQTree.size]
    · simp only [ResLinQTree.size]
      rcases hres c e e' C D α β hc hP with h | h | ⟨h1, h2⟩
      · have := ih c h; omega
      · have := ih' c h; omega
      · have a1 := ih (c - 1) h1
        have a2 := ih' (c - 1) h2
        have : 2 ^ c = 2 ^ (c - 1) + 2 ^ (c - 1) := by
          rw [← two_mul, ← pow_succ']; congr 1; omega
        omega
  | @weaken C D t himp ih =>
    intro c hP
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [ResLinQTree.size]
    · have := ih c (hweak c C D hc hP himp)
      simp only [ResLinQTree.size]; omega

/-- The game on sets of points. `Good c S` is the Delayer's state. Hypotheses: a Good set with
a coin is not inside the falsified set of an axiom line; at a resolution move on `e`, `e'`
(every point of `S` falsifies `e` or `e'`), the Delayer keeps `c` coins on a subset of one
side, or `c - 1` coins on subsets of both sides. Then every tree deriving a line `L` that all
of `S` falsifies has at least `2 ^ c` nodes. -/
theorem game {F : Set (PEqualNP.ProofComplexity.Clause V)}
    (Good : ℕ → Set (V → Bool) → Prop)
    (hax : ∀ c (S : Set (V → Bool)) (L : QLine V) (C : PEqualNP.ProofComplexity.Clause V),
      1 ≤ c → Good c S → S ⊆ FalsSet L → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) → False)
    (hres : ∀ c (S : Set (V → Bool)) (e e' : QEq V), 1 ≤ c → Good c S →
      S ⊆ FalsEq e ∪ FalsEq e' →
      (∃ S' ⊆ S ∩ FalsEq e, Good c S') ∨ (∃ S' ⊆ S ∩ FalsEq e', Good c S') ∨
      ((∃ S' ⊆ S ∩ FalsEq e, Good (c - 1) S') ∧ (∃ S' ⊆ S ∩ FalsEq e', Good (c - 1) S'))) :
    ∀ {L : QLine V} (t : ResLinQTree F L) (c : ℕ) (S : Set (V → Bool)),
      S ⊆ FalsSet L → Good c S → 2 ^ c ≤ t.size := by
  intro L t c S hS hG
  let P : ℕ → QLine V → Prop := fun c L => ∃ S, S ⊆ FalsSet L ∧ Good c S
  refine game_line P ?_ ?_ ?_ t c ⟨S, hS, hG⟩
  · rintro c L C hc ⟨S, hS, hG⟩ hC hL
    exact hax c S L C hc hG hS hC hL
  · rintro c e e' C D α β hc ⟨S, hS, hG⟩
    have hcov : S ⊆ FalsEq e ∪ FalsEq e' := by
      intro a ha
      by_contra hn
      simp only [Set.mem_union, FalsEq, Set.mem_ofPred_eq, not_or, not_not] at hn
      exact hS ha _ List.mem_cons_self (PEqualNP.Search.Helpers.combo_holds a e e' α β hn.1 hn.2)
    have side1 : ∀ S' ⊆ S ∩ FalsEq e, S' ⊆ FalsSet (e :: C) := by
      intro S' hS' a ha f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact (hS' ha).2
      · exact hS (hS' ha).1 f (List.mem_cons_of_mem _ (List.mem_append_left _ hf))
    have side2 : ∀ S' ⊆ S ∩ FalsEq e', S' ⊆ FalsSet (e' :: D) := by
      intro S' hS' a ha f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact (hS' ha).2
      · exact hS (hS' ha).1 f (List.mem_cons_of_mem _ (List.mem_append_right _ hf))
    rcases hres c S e e' hc hG hcov with ⟨S', h1, h2⟩ | ⟨S', h1, h2⟩ | ⟨⟨S1, h1, h2⟩, ⟨S2, h3, h4⟩⟩
    · exact Or.inl ⟨S', side1 S' h1, h2⟩
    · exact Or.inr (Or.inl ⟨S', side2 S' h1, h2⟩)
    · exact Or.inr (Or.inr ⟨⟨S1, side1 S1 h1, h2⟩, ⟨S2, side2 S2 h3, h4⟩⟩)
  · rintro c C D hc ⟨S, hS, hG⟩ himp
    refine ⟨S, fun a ha f hf hf' => ?_, hG⟩
    obtain ⟨g, hg, hg'⟩ := himp a ⟨f, hf, hf'⟩
    exact hS ha g hg hg'

/-- For a refutation (a tree deriving the empty line) any Good set works as the start. -/
theorem game_refutation {F : Set (PEqualNP.ProofComplexity.Clause V)}
    (Good : ℕ → Set (V → Bool) → Prop)
    (hax : ∀ c (S : Set (V → Bool)) (L : QLine V) (C : PEqualNP.ProofComplexity.Clause V),
      1 ≤ c → Good c S → S ⊆ FalsSet L → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) → False)
    (hres : ∀ c (S : Set (V → Bool)) (e e' : QEq V), 1 ≤ c → Good c S →
      S ⊆ FalsEq e ∪ FalsEq e' →
      (∃ S' ⊆ S ∩ FalsEq e, Good c S') ∨ (∃ S' ⊆ S ∩ FalsEq e', Good c S') ∨
      ((∃ S' ⊆ S ∩ FalsEq e, Good (c - 1) S') ∧ (∃ S' ⊆ S ∩ FalsEq e', Good (c - 1) S')))
    (T : ResLinQTree F []) (c : ℕ) (S : Set (V → Bool)) (hG : Good c S) :
    2 ^ c ≤ T.size :=
  game Good hax hres T c S (fun _ _ e he => by simp at he) hG

end PEqualNP.Search.Helpers.Tree
