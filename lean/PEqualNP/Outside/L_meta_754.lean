import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_754

private def links754 (a b : Fin 5) : Prop :=
  (a = 0 ∧ (b = 1 ∨ b = 2 ∨ b = 3)) ∨ (a = 1 ∧ b = 4)

private def graph754 : SimpleGraph (Fin 5) where
  Adj a b := links754 a b ∨ links754 b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by unfold links754; decide⟩

private abbrev decAdj754 : DecidableRel graph754.Adj := by
  intro i j
  change Decidable (links754 i j ∨ links754 j i)
  unfold links754
  infer_instance

theorem lower754 {s : ℕ} (h : PEqualNP.MetaComplexity.HasCircuitSize 5
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s) : 5 ≤ s := by
  let _ : DecidableRel graph754.Adj := decAdj754
  have tree754 : graph754.IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    constructor
    · refine (graph754.connected_iff_exists_forall_reachable).mpr ⟨0, ?_⟩
      intro i
      fin_cases i
      · exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (show graph754.Adj 0 1 by decide)
      · exact SimpleGraph.Adj.reachable (show graph754.Adj 0 2 by decide)
      · exact SimpleGraph.Adj.reachable (show graph754.Adj 0 3 by decide)
      · exact (SimpleGraph.Adj.reachable (show graph754.Adj 0 1 by decide)).trans
          (SimpleGraph.Adj.reachable (show graph754.Adj 1 4 by decide))
    · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide

  have function754 :
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) =
      (fun x : Fin 5 → Bool => decide (∃ i j, graph754.Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    have h : ∀ y : Fin 5 → Bool,
        ((y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 1 && y 4)) =
        decide (∃ i j, graph754.Adj i j ∧ y i = true ∧ y j = true) := by decide
    exact h x

  have edges754 : graph754.edgeFinset.card = 4 := by decide

  have cover754 : ∀ T : Finset (Fin 5),
      (∀ i j, graph754.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by decide
  rw [function754] at h
  have covered := PEqualNP.MetaComplexity.L104 5 2 s graph754 tree754.isAcyclic
    ⟨0, 1, by decide⟩ cover754 h
  rw [edges754] at covered
  omega

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

theorem upper754 {s : ℕ} (hs : 5 ≤ s) :
    HasCircuitSize 5 (fun x : Fin 5 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩, ?_, hs, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel

end PEqualNP.Outside.L_meta_754

open PEqualNP.Outside.L_meta_754

theorem PEqualNP.Outside.L_meta_754 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  intro s
  exact ⟨lower754, upper754⟩
