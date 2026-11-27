import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- If a junk gate detects precisely one of the remaining residual edges,
-- remove that edge and pay for it with this gate. The gate then detects
-- no surviving edge. Repeat before attempting any structural circuit bound.
-- The second child only concerns nonempty families where every junk gate
-- detects zero or at least two edges. Its budget retains every unused gate.
theorem PEqualNP.Outside.R_meta_2382_271
    (peel : ∀ (S : Finset (Sym2 (Fin 11))) (J : Finset ℕ) (A : ℕ → Finset (Sym2 (Fin 11))),
      ∃ V ⊆ S, (S \ V).card ≤ (J.filter (fun j => Disjoint V (A j))).card ∧
        ∀ j ∈ J, (V ∩ A j).card ≠ 1)
    (core :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        2 ≤ J.card → ∀ V ⊆ U, V.Nonempty →
          (U \ V).card ≤ (J.filter (fun j => Disjoint V (gammaE G C j))).card →
          (∀ j ∈ J, (V ∩ gammaE G C j).card ≠ 1) →
          (∀ e ∈ U, ∃ j ∈ J, e ∈ gammaE G C j) →
          V.card ≤ 2 * (centreless G C).card + (J.card - (U \ V).card) +
            (orN G C \ lam G C).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8 := by
  classical
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  dsimp only
  intro C hsize hleast htop hjunk hcover _
  let U := Ustar G C
  let J := junk G C
  change U.card ≤ 2 * (centreless G C).card + J.card + (orN G C \ lam G C).card
  obtain ⟨V, hV, hretired, hclosed⟩ := peel U J (gammaE G C)
  have hpaid : (U \ V).card ≤ J.card :=
    hretired.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hpartition := Finset.card_sdiff_add_card_eq_card hV
  by_cases hnon : V.Nonempty
  · have hwitness : ∀ e ∈ U, ∃ j ∈ J, e ∈ gammaE G C j := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro hU
        obtain ⟨j, hj, hval⟩ := hcover u v hU
        refine ⟨j, hj, Finset.mem_filter.mpr ⟨?_, u, v, rfl, hval⟩⟩
        exact (Finset.mem_sdiff.mp hU).1
    have bound := core C hsize hleast htop hjunk V hV hnon hretired hclosed hwitness
    change V.card ≤ 2 * (centreless G C).card + (J.card - (U \ V).card) +
      (orN G C \ lam G C).card at bound
    omega
  · have hz : V.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hnon)
    omega

-- Proof of the first child. After introducing S, J and A, the following
-- proof works for any edge type with decidable equality.
--   classical
--   induction S using Finset.strongInductionOn generalizing J with
--   | _ S ih =>
--     by_cases h : ∃ j ∈ J, (S ∩ A j).card = 1
--     · obtain ⟨j, hj, hs⟩ := h
--       obtain ⟨e, he⟩ := Finset.card_eq_one.mp hs
--       have heS : e ∈ S := Finset.mem_inter.mp (he.symm ▸ Finset.mem_singleton_self e) |>.1
--       obtain ⟨V, hV, hcard, hclosed⟩ := ih (S.erase e) (Finset.erase_ssubset heS) (J.erase j)
--       have hVS : V ⊆ S := hV.trans (Finset.erase_subset _ _)
--       have heV : e ∉ V := fun hev => Finset.notMem_erase _ _ (hV hev)
--       have hjzero : Disjoint V (A j) := by
--         apply Finset.disjoint_left.mpr
--         intro x hx hxa
--         have hmem : x ∈ S ∩ A j := Finset.mem_inter.mpr ⟨hVS hx, hxa⟩
--         rw [he, Finset.mem_singleton] at hmem
--         exact heV (hmem ▸ hx)
--       refine ⟨V, hVS, ?_, ?_⟩
--       · have hnew : j ∉ (J.erase j).filter (fun k => Disjoint V (A k)) := by simp
--         have hsubset :
--             insert j ((J.erase j).filter (fun k => Disjoint V (A k))) ⊆
--               J.filter (fun k => Disjoint V (A k)) := by
--           intro k hk
--           rcases Finset.mem_insert.mp hk with rfl | hk
--           · exact Finset.mem_filter.mpr ⟨hj, hjzero⟩
--           · rcases Finset.mem_filter.mp hk with ⟨hker, hkd⟩
--             exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hker).2, hkd⟩
--         have hcount := Finset.card_le_card hsubset
--         rw [Finset.card_insert_of_notMem hnew] at hcount
--         have hfull := Finset.card_sdiff_add_card_eq_card hVS
--         have hrest := Finset.card_sdiff_add_card_eq_card hV
--         have hstep := Finset.card_erase_add_one heS
--         omega
--       · intro k hk
--         by_cases hkj : k = j
--         · subst k
--           rw [Finset.disjoint_iff_inter_eq_empty.mp hjzero]
--           simp
--         · exact hclosed k (Finset.mem_erase.mpr ⟨hkj, hk⟩)
--     · refine ⟨S, Finset.Subset.rfl, by simp, ?_⟩
--       exact fun j hj hj1 => h ⟨j, hj, hj1⟩
