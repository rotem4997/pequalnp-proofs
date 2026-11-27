import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Fin

theorem PEqualNP.Outside.L_meta_157 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      ∀ u v : Fin n, G.Adj u v →
        (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
          ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
        (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
          ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
        (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
                Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
          ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
                Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G _ htri hc4 u v huv
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri v a b ⟨ha, hab, G.adj_symm hb⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri u a b ⟨ha, hab, G.adj_symm hb⟩
  · intro a ha b hb hab
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨hva, hau⟩ | ⟨hua, hav⟩
    · rcases hb with ⟨hvb, _⟩ | ⟨hub, hbv⟩
      · exact htri v a b ⟨hva, hab, G.adj_symm hvb⟩
      · exact hc4 u v a b hau.symm hbv.symm ⟨huv, hva, hab, G.adj_symm hub⟩
    · rcases hb with ⟨hvb, hbu⟩ | ⟨hub, _⟩
      · exact hc4 u v b a hbu.symm hav.symm ⟨huv, hvb, G.adj_symm hab, G.adj_symm hua⟩
      · exact htri u a b ⟨hua, hab, G.adj_symm hub⟩
