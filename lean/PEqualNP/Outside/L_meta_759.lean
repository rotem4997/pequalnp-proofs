import Mathlib.Tactic.FinCases
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_759

private def edges : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)]

private def spider : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun i j => (i, j) ∈ edges)

private def adjDec (i j : Fin 6) : Decidable (spider.Adj i j) := by
  change Decidable (i ≠ j ∧ ((i, j) ∈ edges ∨ (j, i) ∈ edges))
  infer_instance

private lemma connected : spider.Connected := by
  let _ : DecidableRel spider.Adj := adjDec
  have h01 := (show spider.Adj 0 1 by decide).reachable
  have h14 := (show spider.Adj 1 4 by decide).reachable
  have h45 := (show spider.Adj 4 5 by decide).reachable
  apply (SimpleGraph.connected_iff_exists_forall_reachable spider).2
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact h01
  · exact (show spider.Adj 0 2 by decide).reachable
  · exact (show spider.Adj 0 3 by decide).reachable
  · exact h01.trans h14
  · exact (h01.trans h14).trans h45

end PEqualNP.Outside.L_meta_759

open PEqualNP.Outside.L_meta_759

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  let _ : DecidableRel spider.Adj := adjDec
  have hc : spider.edgeFinset.card = 5 := by decide
  have ht : spider.IsTree := SimpleGraph.isTree_iff_connected_and_card.mpr
    ⟨connected, by simp only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, hc, Fintype.card_fin]⟩
  have he : ∃ i j : Fin 6, spider.Adj i j := ⟨0, 1, by decide⟩
  let cover : Finset (Fin 6) := {0, 4}
  have hcov : ∀ i j : Fin 6, spider.Adj i j → i ∈ cover ∨ j ∈ cover := by decide
  have hmin : ∀ T : Finset (Fin 6),
      (∀ i j : Fin 6, spider.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by decide
  have hfun : (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, spider.Adj i j ∧
      x i = true ∧ x j = true)) = (fun x : Fin 6 → Bool => (x 0 && x 1) ||
      (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) := by
    apply funext
    decide
  intro s
  rw [← hfun]
  constructor
  · intro h
    have hbound := PEqualNP.MetaComplexity.L104 6 2 s spider ht.isAcyclic he hmin h
    omega
  · intro hs
    obtain ⟨C, hC, hsize, hval⟩ := PEqualNP.MetaComplexity.L105 6 spider cover he hcov
    have hcard : cover.card = 2 := by decide
    exact ⟨C, hC, by omega, hval⟩
