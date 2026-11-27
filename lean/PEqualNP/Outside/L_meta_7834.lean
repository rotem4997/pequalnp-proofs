import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7834_aux

theorem ncard_nbr {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n) :
    (H.incidenceSet v).ncard = (H.neighborSet v).ncard := by
  classical
  rw [SimpleGraph.ncard_incidenceSet, Set.ncard_eq_toFinset_card']
  rfl

theorem edges_del {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n) :
    (H.deleteIncidenceSet v).edgeSet.ncard + (H.neighborSet v).ncard = H.edgeSet.ncard := by
  rw [SimpleGraph.edgeSet_deleteIncidenceSet, ← ncard_nbr,
    Set.ncard_sdiff (H.incidenceSet_subset v) (Set.toFinite _)]
  have := Set.ncard_le_ncard (H.incidenceSet_subset v) (Set.toFinite _)
  omega

theorem key {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w : Fin n → ℕ)
    (hS : G.support ⊆ ↑S) : ∀ k : ℕ, ∀ H : SimpleGraph (Fin n), H ≤ G → H.edgeSet.ncard = k →
    G.edgeSet.ncard ≤ H.edgeSet.ncard +
      ∑ v ∈ S.filter (fun v => (H.neighborSet v).ncard = 0), w v →
    ∃ x6 ≤ G, (∀ x7 : Fin n, (x6.neighborSet x7).ncard = (0 : ℕ) ∨
      w x7 < (x6.neighborSet x7).ncard) ∧
      G.edgeSet.ncard ≤ x6.edgeSet.ncard + ∑ x7 ∈ S, w x7 := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro H hH hk hle
    by_cases hgood : ∀ x7 : Fin n, (H.neighborSet x7).ncard = (0 : ℕ) ∨
        w x7 < (H.neighborSet x7).ncard
    · refine ⟨H, hH, hgood, hle.trans ?_⟩
      exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) _
    · push_neg at hgood
      obtain ⟨v, hv0, hvw⟩ := hgood
      have hed := edges_del H v
      have hvS : v ∈ S := by
        have hne : (H.neighborSet v).Nonempty := by
          by_contra hc
          rw [Set.not_nonempty_iff_eq_empty] at hc
          rw [hc] at hv0
          simp at hv0
        obtain ⟨u, hu⟩ := hne
        have : v ∈ G.support := (SimpleGraph.mem_support G).2 ⟨u, hH hu⟩
        exact_mod_cast hS this
      have hsub : insert v (S.filter (fun x => (H.neighborSet x).ncard = 0)) ⊆
          S.filter (fun x => ((H.deleteIncidenceSet v).neighborSet x).ncard = 0) := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rw [Finset.mem_filter]
        rcases hx with rfl | hx
        · refine ⟨hvS, ?_⟩
          have : (H.deleteIncidenceSet x).neighborSet x = ∅ := by
            ext y
            simp [SimpleGraph.deleteIncidenceSet_adj]
          rw [this]
          simp
        · rw [Finset.mem_filter] at hx
          refine ⟨hx.1, ?_⟩
          have hss : (H.deleteIncidenceSet v).neighborSet x ⊆ H.neighborSet x := by
            intro y hy
            exact (SimpleGraph.deleteIncidenceSet_le H v) hy
          have := Set.ncard_le_ncard hss (Set.toFinite _)
          omega
      have hnot : v ∉ S.filter (fun x => (H.neighborSet x).ncard = 0) := by
        rw [Finset.mem_filter]
        exact fun hh => hv0 hh.2
      have hsum := Finset.sum_le_sum_of_subset (f := w) hsub
      rw [Finset.sum_insert hnot] at hsum
      exact ih (H.deleteIncidenceSet v).edgeSet.ncard (by omega) (H.deleteIncidenceSet v)
        ((SimpleGraph.deleteIncidenceSet_le H v).trans hH) rfl (by omega)

end PEqualNP.Outside.L_meta_7834_aux

theorem PEqualNP.Outside.L_meta_7834 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : Fin x1 → ℕ), x2.support ⊆ ↑x3 → ∃ x6 ≤ x2, (∀ (x7 : Fin x1), (x6.neighborSet x7).ncard = (0 : ℕ) ∨ x4 x7 < (x6.neighborSet x7).ncard) ∧ x2.edgeSet.ncard ≤ x6.edgeSet.ncard + ∑ x7 ∈ x3, x4 x7 := by
  intro x1 x2 x3 x4 h
  exact PEqualNP.Outside.L_meta_7834_aux.key x2 x3 x4 h _ x2 le_rfl rfl (Nat.le_add_right _ _)
