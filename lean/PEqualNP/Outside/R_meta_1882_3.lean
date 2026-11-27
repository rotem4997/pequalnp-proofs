import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1882_3
    (hSupport : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (hTwo : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length) →
      IsLeastAO G C → TopForm G C → (junk G C).card = 2 →
      (∃ i ∈ junk G C, ∃ j ∈ junk G C, PEqualNP.EdgeOwnership.InCone n C i j) →
      (Ustar G C).card ≤ 4 * (C.size + 1))
    (hCore : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      3 ≤ (junk G C).card →
      (∃ i ∈ junk G C, ∃ j ∈ junk G C, PEqualNP.EdgeOwnership.InCone n C i j) →
      ∀ S : Finset (Fin n),
      let E := (Ustar G C).filter (fun e => ∀ v : Fin n, v ∈ e → v ∈ S)
      (∀ v ∈ S, 5 ≤ (E.filter (fun e => v ∈ e)).card) →
      E.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k, core⟩ := hCore
  refine ⟨4 + k, ?_⟩
  intro n G _ girth nonempty C least top two nested
  by_cases pair : (junk G C).card = 2
  · exact (hTwo n G C girth least top pair nested).trans
      (Nat.mul_le_mul_right _ (by omega : 4 ≤ 4 + k))
  have three : 3 ≤ (junk G C).card := by omega
  have strip (U : Finset (Sym2 (Fin n)))
      (coreBound : ∀ S : Finset (Fin n),
        let E := U.filter (fun e => ∀ v : Fin n, v ∈ e → v ∈ S)
        (∀ v ∈ S, 5 ≤ (E.filter (fun e => v ∈ e)).card) → E.card ≤ k * (C.size + 1))
      (S : Finset (Fin n)) :
      (U.filter (fun e => ∀ v : Fin n, v ∈ e → v ∈ S)).card ≤
        4 * S.card + k * (C.size + 1) := by
    let E (S : Finset (Fin n)) :=
      U.filter (fun e => ∀ v : Fin n, v ∈ e → v ∈ S)
    have peel (S : Finset (Fin n)) :
        (E S).card ≤ 4 * S.card + k * (C.size + 1) := by
      induction S using Finset.strongInductionOn with
      | _ S ih =>
        by_cases dense : ∀ v ∈ S, 5 ≤ ((E S).filter (fun e => v ∈ e)).card
        · have bound := coreBound S dense
          change (E S).card ≤ k * (C.size + 1) at bound
          omega
        · push Not at dense
          obtain ⟨v, hv, low⟩ := dense
          have keep : (E S).filter (fun e => v ∉ e) = E (S.erase v) := by
            ext e
            simp only [E, Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨⟨old, cover⟩, avoid⟩
              refine ⟨old, fun u hu => ⟨?_, cover u hu⟩⟩
              rintro rfl
              exact avoid hu
            · rintro ⟨old, cover⟩
              exact ⟨⟨old, fun u hu => (cover u hu).2⟩, fun h => (cover v h).1 rfl⟩
          have split := (E S).card_filter_add_card_filter_not (fun e => v ∈ e)
          rw [keep] at split
          have rest := ih (S.erase v) (Finset.erase_ssubset hv)
          have smaller := Finset.card_erase_add_one hv
          omega
    exact peel S
  let support := (Finset.univ : Finset (Fin n)).filter (fun v => v ∈ G.support)
  have full : (Ustar G C).filter (fun e => ∀ v : Fin n, v ∈ e → v ∈ support) = Ustar G C := by
    apply Finset.filter_true_of_mem
    intro e he v hv
    obtain ⟨u, eq⟩ := Sym2.mem_iff_exists.mp hv
    have adj : G.Adj v u := by
      have edge : e ∈ G.edgeFinset := Finset.sdiff_subset he
      rw [eq] at edge
      exact G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp edge)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, adj.mem_support_left⟩
  have supports : (support : Set (Fin n)) = G.support := by ext v; simp [support]
  have count : support.card ≤ C.size + 1 := by
    rw [← Set.ncard_coe_finset, supports]
    exact hSupport n G C least
  have b := strip (Ustar G C) (core n G girth nonempty C least top three nested) support
  rw [full] at b
  rw [Nat.add_mul]
  omega
