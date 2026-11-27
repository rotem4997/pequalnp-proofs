import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_188 : ∀ (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj], (∀ u w : Fin 5, G.Adj u w ↔ (u ≠ w ∧ (u = 0 ∨ w = 0))) → ∃ (A : Fin 7 → Finset (Sym2 (Fin 5))) (B : Fin 7 → Finset (Finset (Fin 5))) (t : Fin 7 → Fin 5), (∀ i, ∀ e ∈ A i, e ∈ G.edgeFinset ∧ t i ∈ e) ∧ (∀ i, ∀ I ∈ B i, t i ∉ I) ∧ (∀ e ∈ G.edgeFinset, ∀ I : Finset (Fin 5), (∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) → ∃! i : Fin 7, e ∈ A i ∧ I ∈ B i) ∧ (Finset.univ.filter fun i : Fin 7 => t i = 0).card = 3 ∧ (∀ w w' : Fin 5, w ≠ 0 → w' ≠ 0 → w ≠ w' → Finset.univ.filter (fun i : Fin 7 => t i = 0 ∧ s((0 : Fin 5), w) ∈ A i) ≠ Finset.univ.filter (fun i : Fin 7 => t i = 0 ∧ s((0 : Fin 5), w') ∈ A i)) := by
  intro G _ hG
  have hE : ∀ e : Sym2 (Fin 5), e ∈ G.edgeFinset ↔
      e ∈ ({s((0 : Fin 5), 1), s((0 : Fin 5), 2), s((0 : Fin 5), 3), s((0 : Fin 5), 4)} :
        Finset (Sym2 (Fin 5))) := by
    intro e
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hG]
      revert u v
      decide
  refine ⟨![{s((0 : Fin 5), 1), s((0 : Fin 5), 2), s((0 : Fin 5), 3), s((0 : Fin 5), 4)},
      {s((0 : Fin 5), 2), s((0 : Fin 5), 4)}, {s((0 : Fin 5), 3), s((0 : Fin 5), 4)},
      {s((0 : Fin 5), 1)}, {s((0 : Fin 5), 2)}, {s((0 : Fin 5), 3)}, {s((0 : Fin 5), 4)}],
    fun i => Finset.univ.filter (fun I : Finset (Fin 5) =>
      (i.val = 0 ∧ (0 : Fin 5) ∉ I) ∨
      (3 ≤ i.val ∧ (0 : Fin 5) ∈ I ∧ (![0, 0, 0, 1, 2, 3, 4] : Fin 7 → Fin 5) i ∉ I)),
    ![0, 0, 0, 1, 2, 3, 4], ?_⟩
  simp only [hE, hG, Finset.mem_filter, Finset.mem_univ, true_and, ExistsUnique]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · decide
  · decide
  · decide
