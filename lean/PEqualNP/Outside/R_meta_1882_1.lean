import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.R_meta_1882_1 :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → x2.support.ncard ≤ x4.size + (1 : ℕ)) →
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬ ∃ S : Finset (Fin x2), ∃ missed : Finset (Sym2 (Fin x2)),
      S.card ≤ 4 ∧ missed.card ≤ x7.size + 1 ∧
      ∀ e ∈ PEqualNP.TopForm.Ustar x3 x7, e ∈ missed ∨ ∃ p q : Fin x2, e = s(p, q) ∧
        ((∃ z ∈ S, x3.Adj p z) ∨ ∃ z ∈ S, x3.Adj q z)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) →
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) := by
  intro hSupport hRemaining
  obtain ⟨c, hc⟩ := hRemaining
  refine ⟨max 5 c, ?_⟩
  intro n G _ hg hne C hl ht hTwo hNested
  let V := Fin n
  let Near (G : SimpleGraph V) (S : Finset V) (p : V) : Prop :=
    ∃ z ∈ S, G.Adj p z

  let NoTriangle (G : SimpleGraph V) : Prop :=
    ∀ p z w, G.Adj p z → G.Adj p w → ¬ G.Adj z w

  let UniqueCommonNeighbor (G : SimpleGraph V) : Prop :=
    ∀ p z a b, p ≠ z → G.Adj p a → G.Adj z a → G.Adj p b → G.Adj z b → a = b

  have noTriangle_of_girth (G : SimpleGraph V)
      (hg : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length) : NoTriangle G := by
    intro p z u hpz hpu hzu
    let w : G.Walk p p := .cons hpz (.cons hzu (.cons hpu.symm .nil))
    have hc : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · rw [SimpleGraph.Walk.isPath_def]
        simp [w, hzu.ne, hpz.ne.symm, hpu.ne.symm]
      · simp [w]
    have h := hg p w hc
    simp [w] at h

  have uniqueCommonNeighbor_of_girth (G : SimpleGraph V)
      (hg : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length) : UniqueCommonNeighbor G := by
    intro p z a b hpz hpa hza hpb hzb
    by_contra hab
    let w : G.Walk p p := .cons hpa (.cons hza.symm (.cons hzb (.cons hpb.symm .nil)))
    have hc : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · rw [SimpleGraph.Walk.isPath_def]
        simp [w, hpz.symm, hab, hza.ne.symm, hpa.ne.symm, hzb.ne, hpb.ne.symm]
      · simp [w]
    have h := hg p w hc
    simp [w] at h

  let neighborhoodEdges (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) (z : V) :=
    E.filter (fun e => ∃ p q, e = s(p, q) ∧ G.Adj z p)

  have one_neighborhood_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
      (h3 : NoTriangle G) (h4 : UniqueCommonNeighbor G) (E : Finset (Sym2 V))
      (hE : E ⊆ G.edgeFinset) (D : Finset V)
      (hD : ∀ p q, G.Adj p q → p ∈ D ∧ q ∈ D) (z : V) :
      (neighborhoodEdges G E z).card ≤ D.card := by
    classical
    let bucket (v : V) := E.filter (fun e =>
      (e = s(z, v) ∧ G.Adj z v) ∨
      (v ≠ z ∧ ¬ G.Adj z v ∧ ∃ u, e = s(u, v) ∧ G.Adj z u))
    have hB (v : V) (hv : v ∈ D) : (bucket v).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he f hf
      obtain ⟨heE, heB⟩ := Finset.mem_filter.mp he
      obtain ⟨hfE, hfB⟩ := Finset.mem_filter.mp hf
      rcases heB with ⟨rfl, heA⟩ | ⟨hvZ, hvA, u, rfl, hzu⟩ <;>
        rcases hfB with ⟨rfl, hfA⟩ | ⟨hvZ', hvA', w, rfl, hzw⟩
      · rfl
      · exact False.elim (hvA' heA)
      · exact False.elim (hvA hfA)
      · have huv : G.Adj u v := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hE heE))
        have hwv : G.Adj w v := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hE hfE))
        rw [h4 v z u w hvZ (G.adj_symm huv) hzu (G.adj_symm hwv) hzw]
    have hcov : neighborhoodEdges G E z ⊆ D.biUnion bucket := by
      intro e he
      have he' : e ∈ E ∧ ∃ p q, e = s(p, q) ∧ G.Adj z p := Finset.mem_filter.mp he
      obtain ⟨heE, p, q, rfl, hzp⟩ := he'
      have hpq : G.Adj p q := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hE heE))
      have hpD := (hD p q hpq).1
      have hqD := (hD p q hpq).2
      by_cases hqz : q = z
      · subst q
        refine Finset.mem_biUnion.mpr ⟨p, hpD, Finset.mem_filter.mpr ⟨heE, Or.inl ?_⟩⟩
        exact ⟨Sym2.eq_swap, hzp⟩
      · have hnq : ¬ G.Adj z q := fun hzq => h3 z p q hzp hzq hpq
        exact Finset.mem_biUnion.mpr ⟨q, hqD,
          Finset.mem_filter.mpr ⟨heE, Or.inr ⟨hqz, hnq, p, rfl, hzp⟩⟩⟩
    have htotal := Finset.card_biUnion_le_card_mul D bucket 1 hB
    exact (Finset.card_le_card hcov).trans (by simpa using htotal)

  have neighborhood_cover_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
      (h3 : NoTriangle G) (h4 : UniqueCommonNeighbor G) (E : Finset (Sym2 V))
      (hE : E ⊆ G.edgeFinset) (D : Finset V)
      (hD : ∀ p q, G.Adj p q → p ∈ D ∧ q ∈ D) (S : Finset V)
      (hc : ∀ e ∈ E, ∃ p q, e = s(p, q) ∧ (Near G S p ∨ Near G S q)) :
      E.card ≤ S.card * D.card := by
    classical
    have hsub : E ⊆ S.biUnion (neighborhoodEdges G E) := by
      intro e he
      obtain ⟨p, q, eq, hp | hq⟩ := hc e he
      · obtain ⟨z, hz, hpz⟩ := hp
        refine Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩
        exact Finset.mem_filter.mpr ⟨he, p, q, eq, G.adj_symm hpz⟩
      · obtain ⟨z, hz, hqz⟩ := hq
        refine Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩
        exact Finset.mem_filter.mpr ⟨he, q, p, eq.trans Sym2.eq_swap, G.adj_symm hqz⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul S _ _
      (fun z _ => one_neighborhood_card_le G h3 h4 E hE D hD z))

  let SmallNeighborhoodCover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
    ∃ S : Finset (Fin n), ∃ missed : Finset (Sym2 (Fin n)),
      S.card ≤ 4 ∧ missed.card ≤ C.size + 1 ∧
      ∀ e ∈ Ustar G C, e ∈ missed ∨ ∃ p q : Fin n, e = s(p, q) ∧
        ((∃ z ∈ S, G.Adj p z) ∨ ∃ z ∈ S, G.Adj q z)

  have small_neighborhood_case (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (hg : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length)
      (hSupport : G.support.ncard ≤ C.size + 1) (hSmall : SmallNeighborhoodCover G C) :
      (Ustar G C).card ≤ 5 * (C.size + 1) := by
    classical
    obtain ⟨S, missed, hs, hm, hcov⟩ := hSmall
    let known := Ustar G C \ missed
    let support := (Finset.univ : Finset (Fin n)).filter (fun p => p ∈ G.support)
    have hsSet : (support : Set (Fin n)) = G.support := by
      ext p
      simp [support]
    have hsCard : support.card = G.support.ncard := by
      rw [← hsSet, Set.ncard_coe_finset]
    have hsMem (p q : Fin n) (hadj : G.Adj p q) : p ∈ support ∧ q ∈ support := by
      have hp : p ∈ G.support := ⟨q, hadj⟩
      have hq : q ∈ G.support := ⟨p, hadj.symm⟩
      simp [support, hp, hq]
    have hKnown : known ⊆ G.edgeFinset := fun _ he =>
      Finset.sdiff_subset ((Finset.mem_sdiff.mp he).1)
    have hCover : ∀ e ∈ known, ∃ p q : Fin n, e = s(p, q) ∧ (Near G S p ∨ Near G S q) := by
      intro e he
      obtain ⟨hu, hnm⟩ := Finset.mem_sdiff.mp he
      exact (hcov e hu).resolve_left hnm
    have hCount := neighborhood_cover_card_le G (noTriangle_of_girth G hg) (uniqueCommonNeighbor_of_girth G hg)
      known hKnown support hsMem S hCover
    have hK : known.card ≤ 4 * (C.size + 1) := hCount.trans
      (Nat.mul_le_mul hs (hsCard.trans_le hSupport))
    have hu : Ustar G C ⊆ known ∪ missed := by
      intro e he
      by_cases hem : e ∈ missed
      · exact Finset.mem_union_right _ hem
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he, hem⟩)
    calc
      (Ustar G C).card ≤ known.card + missed.card :=
        (Finset.card_le_card hu).trans (Finset.card_union_le known missed)
      _ ≤ 4 * (C.size + 1) + (C.size + 1) := Nat.add_le_add hK hm
      _ = 5 * (C.size + 1) := (Nat.succ_mul 4 (C.size + 1)).symm
  by_cases hsmall : SmallNeighborhoodCover G C
  · exact (small_neighborhood_case G C hg (hSupport n G C hl) hsmall).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_left 5 c))
  · exact (hc n G hg hne C hl ht hTwo hNested hsmall).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_right 5 c))
