import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8287

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (h2 : ∀ v ∉ S, (G.neighborSet v).ncard = (3 : ℕ))
    (h3 : ∀ (a b : Fin n), G.Adj a b → a ∉ S)
    (C : Finset (Fin n)) (hC : ∀ (a b : Fin n), G.Adj a b → a ∈ C ∨ b ∈ C) :
    (Finset.univ \ S).card / (2 : ℕ) ≤ C.card := by
  haveI : DecidableRel G.Adj := Classical.decRel _
  have hdeg : ∀ v, (G.neighborSet v).ncard = G.degree v := by
    intro v
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have hS : ∀ v ∈ S, G.degree v = 0 := by
    intro v hv
    exact Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem
      fun w hw => h3 v w ((G.mem_neighborFinset v w).1 hw) hv)
  have hnS : ∀ v, v ∉ S → G.degree v = 3 := by
    intro v hv
    rw [← hdeg]
    exact h2 v hv
  have hsum : ∑ v, G.degree v = (Finset.univ \ S).card * 3 := by
    rw [← Finset.sum_const_nat (s := Finset.univ \ S) (f := fun v => G.degree v)
      (fun v hv => hnS v (Finset.mem_sdiff.1 hv).2)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    apply hS
    by_contra hvS
    exact hv (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hvS⟩)
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hsub : G.edgeFinset ⊆ C.biUnion (fun c => G.incidenceFinset c) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      rw [Finset.mem_biUnion]
      rcases hC a b hab with h | h
      · refine ⟨a, h, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
        exact ⟨hab, Or.inl rfl⟩
      · refine ⟨b, h, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
        exact ⟨hab, Or.inr rfl⟩
  have hd3 : ∀ c ∈ C, G.degree c ≤ 3 := by
    intro c _
    by_cases hc : c ∈ S
    · rw [hS c hc]
      omega
    · rw [hnS c hc]
  have hE : G.edgeFinset.card ≤ C.card * 3 := by
    calc G.edgeFinset.card ≤ (C.biUnion (fun c => G.incidenceFinset c)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ c ∈ C, (G.incidenceFinset c).card := Finset.card_biUnion_le
      _ = ∑ c ∈ C, G.degree c := by simp only [SimpleGraph.card_incidenceFinset_eq_degree]
      _ ≤ ∑ c ∈ C, 3 := Finset.sum_le_sum hd3
      _ = C.card * 3 := by rw [Finset.sum_const, smul_eq_mul]
  omega

end PEqualNP.Outside.L_meta_8287

theorem PEqualNP.Outside.L_meta_8287 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → x6 ∉ x3) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → ∀ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∈ x8 ∨ x10 ∈ x8) → (Finset.univ \ x3).card / (2 : ℕ) ≤ x8.card := by
  intro x1 x2 x3 _ h2 h3 _ x8 hC
  exact PEqualNP.Outside.L_meta_8287.main x1 x2 x3 h2 h3 x8 hC
