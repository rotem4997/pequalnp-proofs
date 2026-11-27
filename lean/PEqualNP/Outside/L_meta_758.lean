import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_758_aux
open SimpleGraph
open PEqualNP.MetaComplexity

abbrev G : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun i j =>
  (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨ (i = 1 ∧ (j = 4 ∨ j = 5)))

abbrev ef := fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)

theorem firstEdge : G.Adj 0 1 := by decide

theorem connectedG : G.Connected := by
  have r : ∀ i : Fin 6, G.Reachable 0 i := by
    intro i
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact firstEdge.reachable
    · exact (show G.Adj 0 2 by decide).reachable
    · exact (show G.Adj 0 3 by decide).reachable
    · exact firstEdge.reachable.trans (show G.Adj 1 4 by decide).reachable
    · exact firstEdge.reachable.trans (show G.Adj 1 5 by decide).reachable
  exact ⟨fun a b => (r a).symm.trans (r b)⟩

set_option maxRecDepth 10000 in
theorem edgesG : G.edgeFinset.card = 5 := by decide

theorem forestG : G.IsAcyclic := by
  apply SimpleGraph.IsTree.isAcyclic
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connectedG, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edgesG, Nat.card_fin]

abbrev T : Finset (Fin 6) := {0, 1}

theorem coverG : ∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T := by decide

set_option maxRecDepth 20000 in
theorem lowerCover : ∀ S : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ S ∨ j ∈ S) → 2 ≤ S.card := by decide

set_option maxRecDepth 20000 in
theorem evalG : ∀ x : Fin 6 → Bool, ef x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) := by decide
end PEqualNP.Outside.L_meta_758_aux

open PEqualNP.Outside.L_meta_758_aux

theorem PEqualNP.Outside.L_meta_758 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [← funext evalG]
  constructor
  · intro h
    have hb := PEqualNP.MetaComplexity.L104 6 2 s G forestG ⟨0, 1, firstEdge⟩ lowerCover h
    rw [edgesG] at hb
    omega
  · intro hs
    have hu := PEqualNP.MetaComplexity.L105 6 G T ⟨0, 1, firstEdge⟩ coverG
    have ct : T.card = 2 := by decide
    rw [edgesG, ct] at hu
    obtain ⟨C, ho, hl, he⟩ := hu
    exact ⟨C, ho, hl.trans hs, he⟩
