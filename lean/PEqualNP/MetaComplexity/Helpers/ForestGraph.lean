import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# A good leaf in a finite forest

Helper for `L-meta-104` (proofs only, no statement may use it). A finite acyclic graph with an
edge has a leaf `l` with neighbour `p` such that either every neighbour of `p` is `l` or one
other vertex `q`, or `p` has a second leaf neighbour `l' ≠ l`. Proof: take a longest path
`l, p, ...`. Every neighbour of `l` lies on it, so it is `p`. A neighbour `w` of `p` off the
path is a leaf: a neighbour `u ≠ p` of `w` would give the longer path `u, w, p, ...`.
-/

namespace PEqualNP.MetaComplexity.Helpers.Forest

open SimpleGraph

theorem exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push_neg at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

theorem forest_good_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ l p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  haveI : Nonempty V := ⟨u0⟩
  obtain ⟨l, z, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨l, p, hlp, hleaf, ?_⟩
    -- a neighbour of `p` off the path is a leaf
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

end PEqualNP.MetaComplexity.Helpers.Forest
