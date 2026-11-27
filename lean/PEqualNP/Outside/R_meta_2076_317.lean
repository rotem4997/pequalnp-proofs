import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped BigOperators

theorem PEqualNP.Outside.R_meta_2076_317
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (peel : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w : Fin n → ℕ),
      H.support ⊆ (S : Set (Fin n)) →
      ∃ K : SimpleGraph (Fin n), K ≤ H ∧
        (∀ v : Fin n, (K.neighborSet v).ncard = 0 ∨ w v < (K.neighborSet v).ncard) ∧
        H.edgeSet.ncard ≤ K.edgeSet.ncard + ∑ v ∈ S, w v)
    (dense : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (H : SimpleGraph (Fin n)),
      IsLeastAO G C → TopForm G C → H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨
        2 + 4 * (C.gates.flatMap Gate.inputs).count v.val < (H.neighborSet v).ncard) →
      H.edgeSet.ncard ≤ k * (C.size + 1)) :
    ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (H : SimpleGraph (Fin n)),
      IsLeastAO G C → TopForm G C → H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
      H.edgeSet.ncard ≤ k * (C.size + 1) := by
  classical
  obtain ⟨k,core⟩ := dense
  refine ⟨k+10,?_⟩
  intro n G inst girth nonempty C H least top inside _
  let S := (Set.toFinite G.support).toFinset
  have sBound : S.card ≤ C.size+1 := by
    rw [← Set.ncard_eq_toFinset_card G.support (Set.toFinite G.support)]
    exact support n G C least
  have hSub : H.support ⊆ (S : Set (Fin n)) := by
    rintro v ⟨u,hu⟩
    have hv : v ∈ G.support := ⟨u,(G.deleteEdges_le _) (inside hu)⟩
    simpa only [S, Finset.mem_coe, Set.Finite.mem_toFinset] using hv
  let pins := C.gates.flatMap Gate.inputs
  have sumPins : (∑ v ∈ S, pins.count v.val) ≤ pins.length := by
    let T := S.image Fin.val
    have reindex : (∑ i ∈ T, pins.count i) = ∑ v ∈ S, pins.count v.val := by
      unfold T
      exact Finset.sum_image (fun _ _ _ _ eq => Fin.ext eq)
    let P := pins.toFinset
    have onlyUsed : (∑ i ∈ T ∩ P, pins.count i) = ∑ i ∈ T, pins.count i := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro i ti skipped
      apply List.count_eq_zero_of_not_mem
      intro ip
      exact skipped (Finset.mem_inter.mpr ⟨ti,List.mem_toFinset.mpr ip⟩)
    rw [← reindex, ← onlyUsed]
    exact (Finset.sum_le_sum_of_subset Finset.inter_subset_right).trans
      (List.sum_toFinset_count_eq_length pins).le
  have slots (gs : List Gate) (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have hv := fanin g (by simp)
      have tail := ih (fun h hh => fanin h (List.mem_cons_of_mem _ hh))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have slotBudget : pins.length ≤ 2 * C.size :=
    slots C.gates (fun g hg => (least.1.2.2 g hg).le)
  let w (v : Fin n) := 2 + 4 * pins.count v.val
  have weights : (∑ v ∈ S, w v) ≤ 10 * (C.size+1) := by
    have const : (∑ _ ∈ S, (2 : ℕ)) = S.card * 2 := Finset.sum_const_nat (by simp)
    have mult : (∑ v ∈ S, 4 * pins.count v.val) = 4 * ∑ v ∈ S, pins.count v.val := by
      rw [Finset.mul_sum]
    simp only [w, Finset.sum_add_distrib, const, mult]
    omega
  obtain ⟨K,leH,heavy,paid⟩ := peel n H S w hSub
  have hCore := core n G girth nonempty C K least top (leH.trans inside) heavy
  rw [Nat.add_mul]
  omega
