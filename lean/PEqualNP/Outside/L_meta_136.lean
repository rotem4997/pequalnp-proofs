import Mathlib
import PEqualNP.Defs

set_option synthInstance.maxSize 1024 in
theorem PEqualNP.Outside.L_meta_136 :
    ∃ (A : Fin 4 → Finset (Sym2 (Fin 4))) (B : Fin 4 → Finset (Finset (Fin 4)))
      (t : Fin 4 → Fin 4),
      (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.cycleGraph 4).edgeFinset ∧ t i ∈ e) ∧
      (∀ i, ∀ I ∈ B i, t i ∉ I) ∧
      (∀ e ∈ (SimpleGraph.cycleGraph 4).edgeFinset, ∀ I : Finset (Fin 4),
        (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.cycleGraph 4).Adj u w) →
        ∃! i : Fin 4, e ∈ A i ∧ I ∈ B i) := by
  -- Choose the even endpoint when the independent set contains neither even vertex.
  -- Otherwise choose the odd endpoint.
  refine ⟨fun i => (SimpleGraph.cycleGraph 4).edgeFinset.filter (fun e => i ∈ e),
    fun i => Finset.univ.filter (fun I => i ∉ I ∧
      (i.val % 2 = 0 ↔ (0 : Fin 4) ∉ I ∧ (2 : Fin 4) ∉ I)), id, ?_, ?_, ?_⟩
  · intro i e h
    exact Finset.mem_filter.mp h
  · intro i I h
    exact (Finset.mem_filter.mp h).2.1
  · simp only [ExistsUnique, Finset.mem_filter, Finset.mem_univ, true_and]
    decide
