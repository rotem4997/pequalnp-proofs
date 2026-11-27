import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- The circuit provides a small cover of the star edges. A cheap cover of the
-- missed edges finishes the count by union, including whenever paying twice
-- for each missed edge fits the spare gates. Only a deficit needs an exchange:
-- omit S from one colour class and take its neighbours in T instead.
theorem PEqualNP.Outside.R_meta_4545_612
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (deficit : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
        (A : Finset (Fin n)),
      let U := Ustar G C
      let r := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      (∀ D, IsLeastAO G D → TopForm G D → U.card ≤ (Ustar G D).card) →
      (∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A)) →
      (∀ u, (G.neighborSet u).ncard ≠ 1) →
      (∀ B : Finset (Fin n), (∀ u v, s(u,v) ∈ U → u ∈ B ∨ v ∈ B) → r < U.card + B.card) →
      ∃ S T : Finset (Fin n), S ⊆ A ∧ (∀ u ∈ S, ∀ v, G.Adj u v → v ∈ T) ∧
        U.card + A.card + T.card ≤ (tops G C \ centreless G C).card + r + S.card) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x1 × Fin x1)), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x10 → PEqualNP.TopForm.TopForm x2 x10 → (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.Ustar x2 x10).card) → (∃ (x11 : Fin x1 → Bool), ∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x11 x12 ≠ x11 x13) → (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard ≠ (1 : ℕ)) → (∀ x13 ∈ x5, x2.Adj x13.1 x13.2) → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → (∀ x16 ∈ x5, ∀ x18 ∈ x5, x16.1 ≠ x18.2) → (PEqualNP.TopForm.Ustar x2 x4).card + x5.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  intro n G inst C M hc4 hne hC htf hmin hbip hdeg hadj hrow hcol hdis
  let U := Ustar G C
  let r := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  have match_le (V : Finset (Fin n))
      (cov : ∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) : M.card ≤ V.card := by
    let pick (e : Fin n × Fin n) := if e.1 ∈ V then e.1 else e.2
    apply Finset.card_le_card_of_injOn pick
    · intro e he
      change pick e ∈ V
      by_cases h : e.1 ∈ V
      · simp [pick,h]
      · simpa [pick,h] using (cov _ _ (hadj e he)).resolve_left h
    · intro e he f hf heq
      change pick e = pick f at heq
      by_cases u : e.1 ∈ V <;> by_cases v : f.1 ∈ V <;> simp only [pick,u,v,ite_true,ite_false] at heq
      · exact hrow e he f hf heq
      · exact False.elim (hdis e he f hf heq)
      · exact False.elim (hdis f hf e he heq.symm)
      · exact hcol e he f hf heq
  change U.card + M.card ≤ (tops G C \ centreless G C).card +
    2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  suffices h : U.card + M.card ≤ (tops G C \ centreless G C).card + r by
    unfold r at h
    omega
  by_cases cheap : ∃ B : Finset (Fin n),
      (∀ u v, s(u,v) ∈ U → u ∈ B ∨ v ∈ B) ∧ U.card + B.card ≤ r
  · obtain ⟨B, hB, hb⟩ := cheap
    let H := G.deleteEdges (U : Set (Sym2 (Fin n)))
    have hex : ∃ k : ℕ, ∃ V : Finset (Fin n), H.IsVertexCover (V : Set (Fin n)) ∧ V.card = k :=
      ⟨_, Finset.univ, fun _ _ _ => Or.inl (Finset.mem_univ _), rfl⟩
    obtain ⟨K, coverK, eqK⟩ := Nat.find_spec hex
    have minimal : PEqualNP.MetaComplexity.NestedCover.IsMinCover H K := by
      refine ⟨coverK, fun V hV => ?_⟩
      rw [eqK]
      exact Nat.find_min' hex ⟨V, hV, rfl⟩
    have hk := (stars n G C hc4 hne hC htf).2 K minimal
    have hK (u v : Fin n) (h : G.Adj u v) (hm : s(u,v) ∉ U) : u ∈ K ∨ v ∈ K :=
      coverK (SimpleGraph.deleteEdges_adj.mpr ⟨h, hm⟩)
    have cover : ∀ u v, G.Adj u v → u ∈ K ∪ B ∨ v ∈ K ∪ B := by
      intro u v huv
      by_cases hm : s(u,v) ∈ U
      · exact (hB u v hm).imp (Finset.mem_union_right K) (Finset.mem_union_right K)
      · exact (hK u v huv hm).imp (Finset.mem_union_left B) (Finset.mem_union_left B)
    have h := match_le (K ∪ B) cover
    have := Finset.card_union_le K B
    omega
  · obtain ⟨c, hc⟩ := hbip
    let A := Finset.univ.filter fun u => c u = false
    have cut : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A) := by
      intro u v h
      have hne' := hc u v h
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h₁ : c u <;> cases h₂ : c v <;> simp [h₁, h₂] at hne' ⊢
    obtain ⟨S, T, hSA, hN, hprice⟩ := deficit n G C A hc4 hne hC htf hmin cut hdeg
      (fun B hB => Nat.lt_of_not_ge (fun h => cheap ⟨B, hB, h⟩))
    have row (u v : Fin n) (hu : u ∈ A) (h : G.Adj u v) :
        u ∈ (A \ S) ∪ T ∨ v ∈ (A \ S) ∪ T := by
      by_cases hs : u ∈ S
      · exact Or.inr (Finset.mem_union_right _ (hN u hs v h))
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu,hs⟩))
    have hcov : ∀ u v, G.Adj u v → u ∈ (A \ S) ∪ T ∨ v ∈ (A \ S) ∪ T := by
      intro u v h
      by_cases hu : u ∈ A
      · exact row u v hu h
      · exact (row v u ((cut v u h.symm).2 hu) h.symm).symm
    have h := match_le _ hcov
    have hcount := Finset.card_union_le (A \ S) T
    rw [Finset.card_sdiff_of_subset hSA] at hcount
    have := Finset.card_le_card hSA
    change U.card + A.card + T.card ≤ (tops G C \ centreless G C).card + r + S.card at hprice
    omega
