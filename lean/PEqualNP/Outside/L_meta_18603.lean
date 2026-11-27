import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18603

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

/-! ### Section 1: Konig decomposition of a finite bipartite graph -/

lemma has_edge_of_not_acyclic {n : ℕ} (G : SimpleGraph (Fin n)) (hcyc : ¬G.IsAcyclic) :
    ∃ u v : Fin n, G.Adj u v := by
  unfold SimpleGraph.IsAcyclic at hcyc
  push Not at hcyc
  obtain ⟨u, p, hp⟩ := hcyc
  cases p with
  | nil => exact absurd rfl hp.ne_nil
  | cons h _ => exact ⟨_, _, h⟩

lemma vertexCoverNum_pos_of_adj {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n} (h : G.Adj u v) :
    1 ≤ G.vertexCoverNum.toNat := by
  classical
  obtain ⟨S, hScard, hScov⟩ := G.vertexCoverNum_exists
  have hfin : S.Finite := Set.toFinite S
  have hne : S.Nonempty := by
    rcases hScov h with hu | hv
    · exact ⟨u, hu⟩
    · exact ⟨v, hv⟩
  have hpos : 0 < hfin.toFinset.card := Finset.card_pos.mpr (hfin.toFinset_nonempty.mpr hne)
  have heq : G.vertexCoverNum.toNat = hfin.toFinset.card := by
    have h1 : S.encard = (hfin.toFinset.card : ℕ∞) := by
      simpa using Set.encard_eq_coe_toFinset_card S
    rw [← hScard, h1]; rfl
  omega

lemma konig_decomp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hcyc : ¬G.IsAcyclic) :
    ∃ (uL uR : ℕ) (e : (Fin G.vertexCoverNum.toNat ⊕ Fin uL) ⊕ (Fin G.vertexCoverNum.toNat ⊕ Fin uR) ≃ Fin n),
      1 ≤ G.vertexCoverNum.toNat ∧
      (∀ r : Fin G.vertexCoverNum.toNat,
        G.Adj (e (Sum.inl (Sum.inl r))) (e (Sum.inr (Sum.inl r)))) ∧
      (∀ x y : Fin G.vertexCoverNum.toNat ⊕ Fin uL,
        ¬G.Adj (e (Sum.inl x)) (e (Sum.inl y))) ∧
      (∀ x y : Fin G.vertexCoverNum.toNat ⊕ Fin uR,
        ¬G.Adj (e (Sum.inr x)) (e (Sum.inr y))) ∧
      (∀ (j : Fin uL) (k : Fin uR),
        ¬G.Adj (e (Sum.inl (Sum.inr j))) (e (Sum.inr (Sum.inr k)))) := by
  classical
  obtain ⟨u0, v0, huv0⟩ := has_edge_of_not_acyclic G hcyc
  have htpos : 1 ≤ G.vertexCoverNum.toNat := vertexCoverNum_pos_of_adj G huv0
  obtain ⟨col⟩ := hbip
  obtain ⟨Sset, hSenc, hScov⟩ := G.vertexCoverNum_exists
  let S : Finset (Fin n) := Sset.toFinset
  have hScard : S.card = G.vertexCoverNum.toNat := by
    have h1 : Sset.encard = (S.card : ℕ∞) := by
      simpa [S] using Set.encard_eq_coe_toFinset_card Sset
    rw [← hSenc, h1]; rfl
  have hScov' : ∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S := by
    intro a b hab
    simpa [S] using hScov hab
  have hSmin : ∀ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) → S.card ≤ T.card := by
    intro T hT
    have hTcov : G.IsVertexCover (T : Set (Fin n)) := fun a b hab => by simpa using hT a b hab
    have hle := hTcov.vertexCoverNum_le
    rw [← hSenc, Set.encard_eq_coe_toFinset_card Sset, Set.encard_coe_eq_coe_finsetCard] at hle
    exact_mod_cast hle
  let L : Finset (Fin n) := Finset.univ.filter fun v => col v = 0
  let R : Finset (Fin n) := Finset.univ.filter fun v => col v = 1
  have hLR_disj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and] at hvL hvR
    rw [hvL] at hvR; exact absurd hvR (by decide)
  have hLR_univ : ∀ v : Fin n, v ∈ L ∨ v ∈ R := by
    intro v
    have hfin := (col v).isLt
    by_cases h0 : (col v).val = 0
    · left; simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]; exact Fin.ext h0
    · right; simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]; exact Fin.ext (by omega)
  have hAdj_LR : ∀ a b : Fin n, G.Adj a b → (a ∈ L ∧ b ∈ R) ∨ (a ∈ R ∧ b ∈ L) := by
    intro a b hab
    have hne : col a ≠ col b := col.valid hab
    rcases hLR_univ a with ha | ha <;> rcases hLR_univ b with hb | hb
    · exfalso; simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb; exact hne (ha.trans hb.symm)
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exfalso; simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb; exact hne (ha.trans hb.symm)
  let SL : Finset (Fin n) := S ∩ L
  let SR : Finset (Fin n) := S ∩ R
  let UL0 : Finset (Fin n) := L \ SL
  let UR0 : Finset (Fin n) := R \ SR
  have hSL_SR_disj : Disjoint SL SR :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hLR_disj)
  have hS_eq : SL ∪ SR = S := by
    ext v; simp only [SL, SR, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h; rcases hLR_univ v with hv | hv
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
  -- Hall matching from SL into UR0
  let nbL : {x // x ∈ SL} → Finset (Fin n) := fun u => UR0.filter (G.Adj u.1)
  have hHallL : ∀ A : Finset {x // x ∈ SL}, A.card ≤ (A.biUnion nbL).card := by
    intro A
    by_contra! hlt
    let A' : Finset (Fin n) := A.image Subtype.val
    let N' : Finset (Fin n) := A.biUnion nbL
    let T : Finset (Fin n) := (S \ A') ∪ N'
    have hA'sub : A' ⊆ S := by
      intro x hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_inter.mp u.2).1
    have hA'card : A'.card = A.card := Finset.card_image_of_injective A Subtype.val_injective
    have hTcov : ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a b hab
      have aux : ∀ x y : Fin n, G.Adj x y → x ∈ L → y ∈ R → x ∈ T ∨ y ∈ T := by
        intro x y hxy hxL hyR
        by_cases hyS : y ∈ S
        · right
          apply Finset.mem_union_left
          refine Finset.mem_sdiff.mpr ⟨hyS, ?_⟩
          intro hyA'
          obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hyA'
          have huL : u.1 ∈ L := (Finset.mem_inter.mp u.2).2
          rw [hu] at huL
          exact Finset.disjoint_left.mp hLR_disj huL hyR
        · have hxS : x ∈ S := (hScov' x y hxy).resolve_right hyS
          have hxSL : x ∈ SL := Finset.mem_inter.mpr ⟨hxS, hxL⟩
          by_cases hxA : (⟨x, hxSL⟩ : {z // z ∈ SL}) ∈ A
          · right
            apply Finset.mem_union_right
            refine Finset.mem_biUnion.mpr ⟨⟨x, hxSL⟩, hxA, ?_⟩
            simp only [nbL, UR0, SR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
            exact ⟨⟨hyR, fun h => hyS h.1⟩, hxy⟩
          · left
            apply Finset.mem_union_left
            refine Finset.mem_sdiff.mpr ⟨hxS, ?_⟩
            intro hxA'
            obtain ⟨u, huA, hu⟩ := Finset.mem_image.mp hxA'
            have heq_sub : (⟨x, hxSL⟩ : {z // z ∈ SL}) = u := Subtype.ext hu.symm
            exact hxA (heq_sub ▸ huA)
      rcases hAdj_LR a b hab with ⟨haL, hbR⟩ | ⟨haR, hbL⟩
      · exact aux a b hab haL hbR
      · exact (aux b a hab.symm hbL haR).symm
    have hle := hSmin T hTcov
    have hTcard : T.card ≤ (S \ A').card + N'.card := Finset.card_union_le _ _
    have hsdiff : (S \ A').card + A'.card = S.card := Finset.card_sdiff_add_card_eq_card hA'sub
    have hN'lt : N'.card < A.card := hlt
    omega
  obtain ⟨fL, hfLinj, hfLmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective nbL).mp hHallL
  -- Hall matching from SR into UL0
  let nbR : {x // x ∈ SR} → Finset (Fin n) := fun v => UL0.filter (G.Adj v.1)
  have hHallR : ∀ A : Finset {x // x ∈ SR}, A.card ≤ (A.biUnion nbR).card := by
    intro A
    by_contra! hlt
    let A' : Finset (Fin n) := A.image Subtype.val
    let N' : Finset (Fin n) := A.biUnion nbR
    let T : Finset (Fin n) := (S \ A') ∪ N'
    have hA'sub : A' ⊆ S := by
      intro x hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_inter.mp u.2).1
    have hA'card : A'.card = A.card := Finset.card_image_of_injective A Subtype.val_injective
    have hTcov : ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a b hab
      have aux : ∀ x y : Fin n, G.Adj x y → x ∈ R → y ∈ L → x ∈ T ∨ y ∈ T := by
        intro x y hxy hxR hyL
        by_cases hyS : y ∈ S
        · right
          apply Finset.mem_union_left
          refine Finset.mem_sdiff.mpr ⟨hyS, ?_⟩
          intro hyA'
          obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hyA'
          have huR : u.1 ∈ R := (Finset.mem_inter.mp u.2).2
          rw [hu] at huR
          exact Finset.disjoint_left.mp hLR_disj hyL huR
        · have hxS : x ∈ S := (hScov' x y hxy).resolve_right hyS
          have hxSR : x ∈ SR := Finset.mem_inter.mpr ⟨hxS, hxR⟩
          by_cases hxA : (⟨x, hxSR⟩ : {z // z ∈ SR}) ∈ A
          · right
            apply Finset.mem_union_right
            refine Finset.mem_biUnion.mpr ⟨⟨x, hxSR⟩, hxA, ?_⟩
            simp only [nbR, UL0, SL, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
            exact ⟨⟨hyL, fun h => hyS h.1⟩, hxy⟩
          · left
            apply Finset.mem_union_left
            refine Finset.mem_sdiff.mpr ⟨hxS, ?_⟩
            intro hxA'
            obtain ⟨u, huA, hu⟩ := Finset.mem_image.mp hxA'
            have heq_sub : (⟨x, hxSR⟩ : {z // z ∈ SR}) = u := Subtype.ext hu.symm
            exact hxA (heq_sub ▸ huA)
      rcases hAdj_LR a b hab with ⟨haL, hbR⟩ | ⟨haR, hbL⟩
      · exact (aux b a hab.symm hbR haL).symm
      · exact aux a b hab haR hbL
    have hle := hSmin T hTcov
    have hTcard : T.card ≤ (S \ A').card + N'.card := Finset.card_union_le _ _
    have hsdiff : (S \ A').card + A'.card = S.card := Finset.card_sdiff_add_card_eq_card hA'sub
    have hN'lt : N'.card < A.card := hlt
    omega
  obtain ⟨fR, hfRinj, hfRmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective nbR).mp hHallR
  -- Matched left/right sets and unmatched remainders
  let M1L : Finset (Fin n) := SL
  let M2L : Finset (Fin n) := Finset.univ.image fR
  let M1R : Finset (Fin n) := Finset.univ.image fL
  let M2R : Finset (Fin n) := SR
  have hM2L_sub : M2L ⊆ UL0 := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp (hfRmem v)).1
  have hM1R_sub : M1R ⊆ UR0 := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp (hfLmem u)).1
  have hML_disj : Disjoint M1L M2L :=
    Finset.disjoint_of_subset_right hM2L_sub Finset.disjoint_sdiff
  have hMR_disj : Disjoint M1R M2R :=
    Finset.disjoint_of_subset_left hM1R_sub Finset.sdiff_disjoint
  let ML : Finset (Fin n) := M1L ∪ M2L
  let MR : Finset (Fin n) := M1R ∪ M2R
  let UL : Finset (Fin n) := L \ ML
  let UR : Finset (Fin n) := R \ MR
  have hML_sub : ML ⊆ L := Finset.union_subset Finset.inter_subset_right
    (hM2L_sub.trans Finset.sdiff_subset)
  have hMR_sub : MR ⊆ R := Finset.union_subset (hM1R_sub.trans Finset.sdiff_subset)
    Finset.inter_subset_right
  -- Enumerate SL ⊕ SR ≃ Fin t
  have ht_eq : SL.card + SR.card = G.vertexCoverNum.toNat := by
    rw [← Finset.card_union_of_disjoint hSL_SR_disj, hS_eq, hScard]
  let eSL : {x // x ∈ SL} ≃ Fin SL.card := Fintype.equivFinOfCardEq (Fintype.card_coe SL)
  let eSR : {x // x ∈ SR} ≃ Fin SR.card := Fintype.equivFinOfCardEq (Fintype.card_coe SR)
  let eT : {x // x ∈ SL} ⊕ {x // x ∈ SR} ≃ Fin G.vertexCoverNum.toNat :=
    (Equiv.sumCongr eSL eSR).trans (finSumFinEquiv.trans (finCongr ht_eq))
  let eUL : Fin UL.card ≃ {x // x ∈ UL} := (Fintype.equivFinOfCardEq (Fintype.card_coe UL)).symm
  let eUR : Fin UR.card ≃ {x // x ∈ UR} := (Fintype.equivFinOfCardEq (Fintype.card_coe UR)).symm
  let mapL : Fin G.vertexCoverNum.toNat ⊕ Fin UL.card → Fin n
    | Sum.inl r => match eT.symm r with
      | Sum.inl u => u.1
      | Sum.inr v => fR v
    | Sum.inr j => (eUL j).1
  let mapR : Fin G.vertexCoverNum.toNat ⊕ Fin UR.card → Fin n
    | Sum.inl r => match eT.symm r with
      | Sum.inl u => fL u
      | Sum.inr v => v.1
    | Sum.inr k => (eUR k).1
  let mapAll : (Fin G.vertexCoverNum.toNat ⊕ Fin UL.card) ⊕ (Fin G.vertexCoverNum.toNat ⊕ Fin UR.card) → Fin n
    | Sum.inl x => mapL x
    | Sum.inr y => mapR y
  have hmapL_mem : ∀ x, mapL x ∈ L := by
    rintro (r | j)
    · simp only [mapL]
      cases hr : eT.symm r with
      | inl u => exact (Finset.mem_inter.mp u.2).2
      | inr v => exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hfRmem v)).1).1
    · exact (Finset.mem_sdiff.mp (eUL j).2).1
  have hmapR_mem : ∀ y, mapR y ∈ R := by
    rintro (r | k)
    · simp only [mapR]
      cases hr : eT.symm r with
      | inl u => exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hfLmem u)).1).1
      | inr v => exact (Finset.mem_inter.mp v.2).2
    · exact (Finset.mem_sdiff.mp (eUR k).2).1
  have hmapL_inj : Function.Injective mapL := by
    intro x1 x2 heq
    rcases x1 with r1 | j1 <;> rcases x2 with r2 | j2
    · congr 1
      apply eT.symm.injective
      simp only [mapL] at heq
      cases h1 : eT.symm r1 with
      | inl u1 =>
        cases h2 : eT.symm r2 with
        | inl u2 => rw [h1, h2] at heq; dsimp only at heq; exact congrArg Sum.inl (Subtype.ext heq)
        | inr v2 =>
          rw [h1, h2] at heq; dsimp only at heq
          have hv2 : fR v2 ∈ UL0 := (Finset.mem_filter.mp (hfRmem v2)).1
          rw [← heq] at hv2
          exact absurd u1.2 (Finset.mem_sdiff.mp hv2).2
      | inr v1 =>
        cases h2 : eT.symm r2 with
        | inl u2 =>
          rw [h1, h2] at heq; dsimp only at heq
          have hv1 : fR v1 ∈ UL0 := (Finset.mem_filter.mp (hfRmem v1)).1
          rw [heq] at hv1
          exact absurd u2.2 (Finset.mem_sdiff.mp hv1).2
        | inr v2 =>
          rw [h1, h2] at heq; dsimp only at heq
          exact congrArg Sum.inr (hfRinj heq)
    · exfalso
      have hj : (eUL j2).1 ∉ ML := (Finset.mem_sdiff.mp (eUL j2).2).2
      apply hj
      simp only [mapL] at heq
      rw [← heq]
      cases hr : eT.symm r1 with
      | inl u => exact Finset.mem_union_left _ u.2
      | inr v => exact Finset.mem_union_right _ (Finset.mem_image_of_mem fR (Finset.mem_univ v))
    · exfalso
      have hj : (eUL j1).1 ∉ ML := (Finset.mem_sdiff.mp (eUL j1).2).2
      apply hj
      simp only [mapL] at heq
      rw [heq]
      cases hr : eT.symm r2 with
      | inl u => exact Finset.mem_union_left _ u.2
      | inr v => exact Finset.mem_union_right _ (Finset.mem_image_of_mem fR (Finset.mem_univ v))
    · exact congrArg Sum.inr (eUL.injective (Subtype.ext heq))
  have hmapR_inj : Function.Injective mapR := by
    intro x1 x2 heq
    rcases x1 with r1 | k1 <;> rcases x2 with r2 | k2
    · congr 1
      apply eT.symm.injective
      simp only [mapR] at heq
      cases h1 : eT.symm r1 with
      | inl u1 =>
        cases h2 : eT.symm r2 with
        | inl u2 => rw [h1, h2] at heq; dsimp only at heq; exact congrArg Sum.inl (hfLinj heq)
        | inr v2 =>
          rw [h1, h2] at heq; dsimp only at heq
          have hu1 : fL u1 ∈ UR0 := (Finset.mem_filter.mp (hfLmem u1)).1
          rw [heq] at hu1
          exact absurd v2.2 (Finset.mem_sdiff.mp hu1).2
      | inr v1 =>
        cases h2 : eT.symm r2 with
        | inl u2 =>
          rw [h1, h2] at heq; dsimp only at heq
          have hu2 : fL u2 ∈ UR0 := (Finset.mem_filter.mp (hfLmem u2)).1
          rw [← heq] at hu2
          exact absurd v1.2 (Finset.mem_sdiff.mp hu2).2
        | inr v2 =>
          rw [h1, h2] at heq; dsimp only at heq
          exact congrArg Sum.inr (Subtype.ext heq)
    · exfalso
      have hk : (eUR k2).1 ∉ MR := (Finset.mem_sdiff.mp (eUR k2).2).2
      apply hk
      simp only [mapR] at heq
      rw [← heq]
      cases hr : eT.symm r1 with
      | inl u => exact Finset.mem_union_left _ (Finset.mem_image_of_mem fL (Finset.mem_univ u))
      | inr v => exact Finset.mem_union_right _ v.2
    · exfalso
      have hk : (eUR k1).1 ∉ MR := (Finset.mem_sdiff.mp (eUR k1).2).2
      apply hk
      simp only [mapR] at heq
      rw [heq]
      cases hr : eT.symm r2 with
      | inl u => exact Finset.mem_union_left _ (Finset.mem_image_of_mem fL (Finset.mem_univ u))
      | inr v => exact Finset.mem_union_right _ v.2
    · exact congrArg Sum.inr (eUR.injective (Subtype.ext heq))
  have hmapAll_inj : Function.Injective mapAll := by
    intro x1 x2 heq
    rcases x1 with a1 | b1 <;> rcases x2 with a2 | b2
    · exact congrArg Sum.inl (hmapL_inj heq)
    · exfalso
      have heq' : mapL a1 = mapR b2 := heq
      exact Finset.disjoint_left.mp hLR_disj (hmapL_mem a1) (heq' ▸ hmapR_mem b2)
    · exfalso
      have heq' : mapR b1 = mapL a2 := heq
      exact Finset.disjoint_left.mp hLR_disj (heq' ▸ hmapL_mem a2) (hmapR_mem b1)
    · exact congrArg Sum.inr (hmapR_inj heq)
  have hcard_all : Fintype.card ((Fin G.vertexCoverNum.toNat ⊕ Fin UL.card) ⊕ (Fin G.vertexCoverNum.toNat ⊕ Fin UR.card)) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hML_card : ML.card = G.vertexCoverNum.toNat := by
      rw [Finset.card_union_of_disjoint hML_disj]
      have h2 : M2L.card = SR.card := by
        rw [Finset.card_image_of_injective _ hfRinj, Finset.card_univ, Fintype.card_coe]
      rw [h2]; exact ht_eq
    have hMR_card : MR.card = G.vertexCoverNum.toNat := by
      rw [Finset.card_union_of_disjoint hMR_disj]
      have h1 : M1R.card = SL.card := by
        rw [Finset.card_image_of_injective _ hfLinj, Finset.card_univ, Fintype.card_coe]
      rw [h1]; exact ht_eq
    have hL_split : UL.card + ML.card = L.card := Finset.card_sdiff_add_card_eq_card hML_sub
    have hR_split : UR.card + MR.card = R.card := Finset.card_sdiff_add_card_eq_card hMR_sub
    have hLR_sum : L.card + R.card = n := by
      rw [← Finset.card_union_of_disjoint hLR_disj]
      have huniv : L ∪ R = Finset.univ := by
        ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hLR_univ v
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    omega
  let e := Equiv.ofBijective mapAll
    ((Fintype.bijective_iff_injective_and_card mapAll).mpr ⟨hmapAll_inj, hcard_all⟩)
  refine ⟨UL.card, UR.card, e, htpos, ?_, ?_, ?_, ?_⟩
  · intro r
    change G.Adj (mapL (Sum.inl r)) (mapR (Sum.inl r))
    simp only [mapL, mapR]
    cases hr : eT.symm r with
    | inl u => exact (Finset.mem_filter.mp (hfLmem u)).2
    | inr v => exact ((Finset.mem_filter.mp (hfRmem v)).2).symm
  · intro x y hab
    rcases hAdj_LR _ _ hab with ⟨_, hyR⟩ | ⟨hxR, _⟩
    · exact Finset.disjoint_left.mp hLR_disj (hmapL_mem y) hyR
    · exact Finset.disjoint_left.mp hLR_disj (hmapL_mem x) hxR
  · intro x y hab
    rcases hAdj_LR _ _ hab with ⟨hxL, _⟩ | ⟨_, hyL⟩
    · exact Finset.disjoint_left.mp hLR_disj hxL (hmapR_mem x)
    · exact Finset.disjoint_left.mp hLR_disj hyL (hmapR_mem y)
  · intro j k hab
    have hnotSL : (eUL j).1 ∉ S := by
      intro hS
      have hmem : (eUL j).1 ∈ ML :=
        Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hS, (Finset.mem_sdiff.mp (eUL j).2).1⟩)
      exact (Finset.mem_sdiff.mp (eUL j).2).2 hmem
    have hnotSR : (eUR k).1 ∉ S := by
      intro hS
      have hmem : (eUR k).1 ∈ MR :=
        Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hS, (Finset.mem_sdiff.mp (eUR k).2).1⟩)
      exact (Finset.mem_sdiff.mp (eUR k).2).2 hmem
    rcases hScov' _ _ hab with h | h
    · exact hnotSL h
    · exact hnotSR h

/-! ### Section 2: Cyclic 3-regular C4-free 3-connected bipartite scaffold -/

def cycAdj (q : ℕ) (a b : Fin q) : Prop :=
  b.val = a.val ∨ b.val = (a.val + 1) % q ∨ b.val = (a.val + 3) % q

lemma mod_add_left_cancel {q c x y : ℕ} (hx : x < q) (hy : y < q)
    (h : (c + x) % q = (c + y) % q) : x = y := by
  have hq : 0 < q := by omega
  have h1 : (q - c % q + (c + x)) % q = (q - c % q + (c + y)) % q := by
    rw [Nat.add_mod, h, ← Nat.add_mod]
  have hcm : c % q < q := Nat.mod_lt c hq
  have hdiv := Nat.div_add_mod c q
  have hmul : q * (c / q + 1) = q * (c / q) + q := Nat.mul_succ q (c / q)
  have hx' : (q - c % q + (c + x)) % q = x := by
    rw [show q - c % q + (c + x) = x + q * (c / q + 1) by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hy' : (q - c % q + (c + y)) % q = y := by
    rw [show q - c % q + (c + y) = y + q * (c / q + 1) by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  rw [hx', hy'] at h1
  exact h1

lemma cycAdj_iff_exists_shift {q : ℕ} (a b : Fin q) :
    cycAdj q a b ↔ ∃ d : ℕ, (d = 0 ∨ d = 1 ∨ d = 3) ∧ b.val = (a.val + d) % q := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0, Or.inl rfl, by simpa [Nat.mod_eq_of_lt a.isLt] using h⟩
    · exact ⟨1, Or.inr (Or.inl rfl), h⟩
    · exact ⟨3, Or.inr (Or.inr rfl), h⟩
  · rintro ⟨d, rfl | rfl | rfl, h⟩
    · left; simpa [Nat.mod_eq_of_lt a.isLt] using h
    · right; left; exact h
    · right; right; exact h

lemma cycAdj_noC4_left {q : ℕ} (hq : 10 ≤ q) (a1 a2 : Fin q) (hne : a1 ≠ a2)
    {b1 b2 : Fin q} (h11 : cycAdj q a1 b1) (h21 : cycAdj q a2 b1)
    (h12 : cycAdj q a1 b2) (h22 : cycAdj q a2 b2) : b1 = b2 := by
  obtain ⟨d1, hd1, hb1_1⟩ := (cycAdj_iff_exists_shift a1 b1).mp h11
  obtain ⟨e1, he1, hb1_2⟩ := (cycAdj_iff_exists_shift a2 b1).mp h21
  obtain ⟨d2, hd2, hb2_1⟩ := (cycAdj_iff_exists_shift a1 b2).mp h12
  obtain ⟨e2, he2, hb2_2⟩ := (cycAdj_iff_exists_shift a2 b2).mp h22
  have hsum : (a1.val + a2.val + (d1 + e2)) % q = (a1.val + a2.val + (d2 + e1)) % q := by
    calc (a1.val + a2.val + (d1 + e2)) % q
        = ((a1.val + d1) + (a2.val + e2)) % q := by congr 1; omega
      _ = ((a1.val + d1) % q + (a2.val + e2) % q) % q := Nat.add_mod _ _ _
      _ = (b1.val + b2.val) % q := by rw [← hb1_1, ← hb2_2]
      _ = ((a2.val + e1) % q + (a1.val + d2) % q) % q := by rw [hb1_2, hb2_1]
      _ = ((a2.val + e1) + (a1.val + d2)) % q := (Nat.add_mod _ _ _).symm
      _ = (a1.val + a2.val + (d2 + e1)) % q := by congr 1; omega
  have hde : d1 + e2 = d2 + e1 :=
    mod_add_left_cancel (by omega) (by omega) hsum
  by_cases hdd : d1 = d2
  · apply Fin.ext; rw [hb1_1, hb2_1, hdd]
  · exfalso
    have heq : d1 = e1 := by omega
    have ha : (d1 + a1.val) % q = (d1 + a2.val) % q := by
      rw [Nat.add_comm d1 a1.val, Nat.add_comm d1 a2.val, ← hb1_1, heq, ← hb1_2]
    exact hne (Fin.ext (mod_add_left_cancel a1.isLt a2.isLt ha))

lemma cycAdj_noC4_right {q : ℕ} (hq : 10 ≤ q) (b1 b2 : Fin q) (hne : b1 ≠ b2)
    {a1 a2 : Fin q} (h11 : cycAdj q a1 b1) (h12 : cycAdj q a1 b2)
    (h21 : cycAdj q a2 b1) (h22 : cycAdj q a2 b2) : a1 = a2 := by
  by_contra hane
  exact hne (cycAdj_noC4_left hq a1 a2 hane h11 h21 h12 h22)

lemma cycAdj_hit_mul10 {q0 : ℕ} (a b1 b2 : Fin (10 * q0))
    (h1 : cycAdj (10 * q0) a b1) (h2 : cycAdj (10 * q0) a b2)
    (hm1 : b1.val % 10 = 0) (hm2 : b2.val % 10 = 0) : b1 = b2 := by
  have hmod10 : ∀ x : ℕ, (x % (10 * q0)) % 10 = x % 10 := fun x =>
    Nat.mod_mod_of_dvd x ⟨q0, rfl⟩
  obtain ⟨d1, hd1, hb1⟩ := (cycAdj_iff_exists_shift a b1).mp h1
  obtain ⟨d2, hd2, hb2⟩ := (cycAdj_iff_exists_shift a b2).mp h2
  have h1' : (a.val + d1) % 10 = 0 := by rw [← hmod10, ← hb1]; exact hm1
  have h2' : (a.val + d2) % 10 = 0 := by rw [← hmod10, ← hb2]; exact hm2
  have hd : d1 = d2 := by omega
  apply Fin.ext; rw [hb1, hb2, hd]

lemma cycAdj_mul10_slot {q0 : ℕ} (s : ℕ) (hs : s < q0)
    (b : Fin (10 * q0)) (h : cycAdj (10 * q0) ⟨10 * s, by omega⟩ b) :
    b.val / 10 = s := by
  rcases h with h | h | h <;> dsimp only at h
  · omega
  · have hlt : 10 * s + 1 < 10 * q0 := by omega
    rw [Nat.mod_eq_of_lt hlt] at h; omega
  · have hlt : 10 * s + 3 < 10 * q0 := by omega
    rw [Nat.mod_eq_of_lt hlt] at h; omega

lemma cycAdj_right_neighbors {q : ℕ} (hq : 10 ≤ q) (a : Fin q) [DecidablePred (cycAdj q a)] :
    (Finset.univ.filter fun b : Fin q => cycAdj q a b).card = 3 := by
  let b0 : Fin q := a
  let b1 : Fin q := ⟨(a.val + 1) % q, Nat.mod_lt _ (by omega)⟩
  let b3 : Fin q := ⟨(a.val + 3) % q, Nat.mod_lt _ (by omega)⟩
  have heq : (Finset.univ.filter fun b : Fin q => cycAdj q a b) = {b0, b1, b3} := by
    ext b
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, cycAdj, Fin.ext_iff, b0, b1, b3]
  rw [heq]
  have h01 : b0 ≠ b1 := by
    intro h; have hv := congrArg Fin.val h; dsimp [b0, b1] at hv
    have := mod_add_left_cancel (q := q) (c := a.val) (x := 0) (y := 1) (by omega) (by omega)
      (by simpa [Nat.mod_eq_of_lt a.isLt] using hv)
    omega
  have h03 : b0 ≠ b3 := by
    intro h; have hv := congrArg Fin.val h; dsimp [b0, b3] at hv
    have := mod_add_left_cancel (q := q) (c := a.val) (x := 0) (y := 3) (by omega) (by omega)
      (by simpa [Nat.mod_eq_of_lt a.isLt] using hv)
    omega
  have h13 : b1 ≠ b3 := by
    intro h; have hv := congrArg Fin.val h; dsimp [b1, b3] at hv
    have := mod_add_left_cancel (q := q) (c := a.val) (x := 1) (y := 3) (by omega) (by omega) hv
    omega
  rw [Finset.card_insert_of_notMem (by simp [h01, h03]),
      Finset.card_insert_of_notMem (by simp [h13]), Finset.card_singleton]

lemma cycAdj_left_neighbors {q : ℕ} (hq : 10 ≤ q) (b : Fin q) [DecidablePred (fun a => cycAdj q a b)] :
    (Finset.univ.filter fun a : Fin q => cycAdj q a b).card = 3 := by
  let a0 : Fin q := b
  let a1 : Fin q := ⟨(b.val + q - 1) % q, Nat.mod_lt _ (by omega)⟩
  let a3 : Fin q := ⟨(b.val + q - 3) % q, Nat.mod_lt _ (by omega)⟩
  have hiff : ∀ a : Fin q, cycAdj q a b ↔ a = a0 ∨ a = a1 ∨ a = a3 := by
    intro a
    constructor
    · rintro (h | h | h)
      · left; exact Fin.ext h.symm
      · right; left; apply Fin.ext; dsimp [a1]
        have ha : (1 + a.val) % q = (1 + (b.val + q - 1) % q) % q := by
          rw [Nat.add_comm 1 a.val, ← h]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
              show 1 + (b.val + q - 1) = b.val + q * 1 by omega,
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
        exact mod_add_left_cancel a.isLt (Nat.mod_lt _ (by omega)) ha
      · right; right; apply Fin.ext; dsimp [a3]
        have ha : (3 + a.val) % q = (3 + (b.val + q - 3) % q) % q := by
          rw [Nat.add_comm 3 a.val, ← h]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
              show 3 + (b.val + q - 3) = b.val + q * 1 by omega,
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
        exact mod_add_left_cancel a.isLt (Nat.mod_lt _ (by omega)) ha
    · rintro (rfl | rfl | rfl)
      · left; rfl
      · right; left; dsimp [a1]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show b.val + q - 1 + 1 = b.val + q * 1 by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
      · right; right; dsimp [a3]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show b.val + q - 3 + 3 = b.val + q * 1 by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
  have heq : (Finset.univ.filter fun a : Fin q => cycAdj q a b) = {a0, a1, a3} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hiff]
  rw [heq]
  have h01 : a0 ≠ a1 := by
    intro h; have hv := congrArg Fin.val h; dsimp [a0, a1] at hv
    have hb1 : (1 + (b.val + q - 1) % q) % q = b.val := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show 1 + (b.val + q - 1) = b.val + q * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    rw [← hv] at hb1
    have := mod_add_left_cancel (q := q) (c := b.val) (x := 1) (y := 0) (by omega) (by omega)
      (by simpa [Nat.add_comm, Nat.mod_eq_of_lt b.isLt] using hb1)
    omega
  have h03 : a0 ≠ a3 := by
    intro h; have hv := congrArg Fin.val h; dsimp [a0, a3] at hv
    have hb3 : (3 + (b.val + q - 3) % q) % q = b.val := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show 3 + (b.val + q - 3) = b.val + q * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    rw [← hv] at hb3
    have := mod_add_left_cancel (q := q) (c := b.val) (x := 3) (y := 0) (by omega) (by omega)
      (by simpa [Nat.add_comm, Nat.mod_eq_of_lt b.isLt] using hb3)
    omega
  have h13 : a1 ≠ a3 := by
    intro h; have hv := congrArg Fin.val h; dsimp [a1, a3] at hv
    have hb1 : ((b.val + q - 1) % q + 1) % q = b.val := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show b.val + q - 1 + 1 = b.val + q * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    have hb3 : ((b.val + q - 3) % q + 3) % q = b.val := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show b.val + q - 3 + 3 = b.val + q * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    rw [hv] at hb1
    have := mod_add_left_cancel (q := q) (c := (b.val + q - 3) % q) (x := 1) (y := 3)
      (by omega) (by omega) (hb1.trans hb3.symm)
    omega
  rw [Finset.card_insert_of_notMem (by simp [h01, h03]),
      Finset.card_insert_of_notMem (by simp [h13]), Finset.card_singleton]

def cycGraph (q : ℕ) : SimpleGraph (Fin q ⊕ Fin q) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inr b => cycAdj q a b
    | Sum.inr b, Sum.inl a => cycAdj q a b
    | _, _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

def cycPos {q : ℕ} (hq : 0 < q) (p : Fin (2 * q)) : Fin q ⊕ Fin q :=
  if p.val % 2 = 0 then
    Sum.inl ⟨p.val / 2, by omega⟩
  else
    Sum.inr ⟨(p.val / 2 + 1) % q, Nat.mod_lt _ hq⟩

lemma cycPos_bij {q : ℕ} (hq : 0 < q) : Function.Bijective (cycPos hq) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp [two_mul]⟩
  intro p1 p2 heq
  unfold cycPos at heq
  by_cases h1 : p1.val % 2 = 0 <;> by_cases h2 : p2.val % 2 = 0
  · simp only [h1, h2, ↓reduceIte, Sum.inl.injEq, Fin.mk.injEq] at heq
    exact Fin.ext (by omega)
  · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at heq
  · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at heq
  · simp only [h1, h2, ↓reduceIte, Sum.inr.injEq, Fin.mk.injEq] at heq
    have hd : p1.val / 2 = p2.val / 2 :=
      mod_add_left_cancel (q := q) (c := 1) (x := p1.val / 2) (y := p2.val / 2)
        (by omega) (by omega) (by simpa [Nat.add_comm] using heq)
    exact Fin.ext (by omega)

lemma cycPos_step {q : ℕ} (hq : 10 ≤ q) (p : Fin (2 * q)) :
    (cycGraph q).Adj (cycPos (by omega : 0 < q) p)
      (cycPos (by omega : 0 < q) ⟨(p.val + 1) % (2 * q), Nat.mod_lt _ (by omega)⟩) := by
  unfold cycPos
  by_cases hp : p.val % 2 = 0
  · have hp1 : (p.val + 1) % (2 * q) = p.val + 1 := Nat.mod_eq_of_lt (by omega)
    have hodd : ¬(p.val + 1) % (2 * q) % 2 = 0 := by omega
    simp only [hp, hodd, ↓reduceIte]
    change cycAdj q ⟨p.val / 2, _⟩ ⟨((p.val + 1) % (2 * q) / 2 + 1) % q, _⟩
    right; left; dsimp
    rw [hp1, show (p.val + 1) / 2 = p.val / 2 by omega]
  · have heven : (p.val + 1) % (2 * q) % 2 = 0 := by
      have h2 : 2 ∣ 2 * q := ⟨q, rfl⟩
      rw [Nat.mod_mod_of_dvd _ h2]; omega
    simp only [hp, heven, ↓reduceIte]
    change cycAdj q ⟨(p.val + 1) % (2 * q) / 2, _⟩ ⟨(p.val / 2 + 1) % q, _⟩
    left; dsimp
    by_cases hlast : p.val + 1 < 2 * q
    · rw [Nat.mod_eq_of_lt hlast]
      have hlt : p.val / 2 + 1 < q := by omega
      rw [Nat.mod_eq_of_lt hlt]; omega
    · have hEq : p.val + 1 = 2 * q := by omega
      rw [hEq, Nat.mod_self]
      have hd : p.val / 2 + 1 = q := by omega
      rw [hd, Nat.mod_self]

lemma cycPos_chord_even {q : ℕ} (hq : 10 ≤ q) (p : Fin (2 * q)) (he : p.val % 2 = 0) :
    (cycGraph q).Adj (cycPos (by omega : 0 < q) p)
      (cycPos (by omega : 0 < q) ⟨(p.val + 5) % (2 * q), Nat.mod_lt _ (by omega)⟩) := by
  unfold cycPos
  have hodd : ¬(p.val + 5) % (2 * q) % 2 = 0 := by
    have h2 : 2 ∣ 2 * q := ⟨q, rfl⟩
    rw [Nat.mod_mod_of_dvd _ h2]; omega
  simp only [he, hodd, ↓reduceIte]
  change cycAdj q ⟨p.val / 2, _⟩ ⟨((p.val + 5) % (2 * q) / 2 + 1) % q, _⟩
  right; right; dsimp
  by_cases hlt : p.val + 5 < 2 * q
  · rw [Nat.mod_eq_of_lt hlt]
    have hdiv : (p.val + 5) / 2 + 1 = p.val / 2 + 3 := by omega
    rw [hdiv]
  · have hwrap : (p.val + 5) % (2 * q) = p.val + 5 - 2 * q := by
      have : p.val + 5 < 2 * (2 * q) := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hwrap]
    have hdiv : (p.val + 5 - 2 * q) / 2 + 1 = p.val / 2 + 3 - q := by omega
    have hmod : (p.val / 2 + 3) % q = p.val / 2 + 3 - q := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hdiv, hmod, Nat.mod_eq_of_lt (by omega)]

lemma cycPos_chord_odd {q : ℕ} (hq : 10 ≤ q) (p : Fin (2 * q)) (ho : p.val % 2 = 1) :
    (cycGraph q).Adj (cycPos (by omega : 0 < q) p)
      (cycPos (by omega : 0 < q) ⟨(p.val + 2 * q - 5) % (2 * q), Nat.mod_lt _ (by omega)⟩) := by
  let p' : Fin (2 * q) := ⟨(p.val + 2 * q - 5) % (2 * q), Nat.mod_lt _ (by omega)⟩
  have he : p'.val % 2 = 0 := by
    dsimp [p']
    have h2 : 2 ∣ 2 * q := ⟨q, rfl⟩
    rw [Nat.mod_mod_of_dvd _ h2]; omega
  have hback : (⟨(p'.val + 5) % (2 * q), Nat.mod_lt _ (by omega)⟩ : Fin (2 * q)) = p := by
    apply Fin.ext; dsimp [p']
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        show p.val + 2 * q - 5 + 5 = p.val + 2 * q * 1 by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.isLt]
  have hadj := cycPos_chord_even hq p' he
  rw [hback] at hadj
  exact hadj.symm

lemma mod_lt_two_mul {M u : ℕ} (hu : u < 2 * M) :
    u % M = if u < M then u else u - M := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma cyc_add_mod_ne {M a j : ℕ} (ha : a < M) (hj1 : 1 ≤ j) (hj2 : j < M) :
    (a + j) % M ≠ a := by
  rw [mod_lt_two_mul (by omega)]; split_ifs <;> omega

lemma cycGraph_threeConn {q : ℕ} (hq : 10 ≤ q) (S : Finset (Fin q ⊕ Fin q)) (hS : S.card ≤ 2) :
    ((cycGraph q).induce (↑S : Set (Fin q ⊕ Fin q))ᶜ).Connected := by
  classical
  have hq0 : 0 < q := by omega
  let M : ℕ := 2 * q
  have hM : 20 ≤ M := by omega
  let e := Equiv.ofBijective (cycPos hq0) (cycPos_bij hq0)
  let T : Finset (Fin M) := S.preimage (cycPos hq0) (by intro a _ b _ h; exact e.injective h)
  have hmemT : ∀ p : Fin M, p ∈ T ↔ cycPos hq0 p ∈ S := fun p => Finset.mem_preimage
  have hTcard : T.card ≤ 2 := by
    have himg : T.image (cycPos hq0) ⊆ S := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact (hmemT p).mp hp
    have hle : T.card ≤ S.card := by
      calc T.card = (T.image (cycPos hq0)).card := (Finset.card_image_of_injective T e.injective).symm
        _ ≤ S.card := Finset.card_le_card himg
    omega
  let H := (cycGraph q).induce (↑S : Set (Fin q ⊕ Fin q))ᶜ
  let mkV (p : Fin M) (hp : p ∉ T) : ((↑S : Set (Fin q ⊕ Fin q))ᶜ : Set (Fin q ⊕ Fin q)) :=
    ⟨cycPos hq0 p, fun h => hp ((hmemT p).mpr (by simpa using h))⟩
  have hreach_arc : ∀ (s k : ℕ)
      (hgood : ∀ j ≤ k, (⟨(s + j) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) ∉ T),
      H.Reachable (mkV ⟨s % M, Nat.mod_lt _ (by omega)⟩ (by simpa using hgood 0 (Nat.zero_le _)))
        (mkV ⟨(s + k) % M, Nat.mod_lt _ (by omega)⟩ (hgood k le_rfl)) := by
    intro s k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      intro hgood
      have h1 := ih (fun j hj => hgood j (Nat.le_succ_of_le hj))
      have hstep : H.Adj
          (mkV ⟨(s + k) % M, Nat.mod_lt _ (by omega)⟩ (hgood k (Nat.le_succ k)))
          (mkV ⟨(s + (k + 1)) % M, Nat.mod_lt _ (by omega)⟩ (hgood (k + 1) le_rfl)) := by
        have heq : (⟨(((s + k) % M) + 1) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) =
            ⟨(s + (k + 1)) % M, Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext; dsimp
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        have hadj := cycPos_step hq ⟨(s + k) % M, Nat.mod_lt _ (by omega)⟩
        rw [heq] at hadj
        exact hadj
      exact h1.trans hstep.reachable
  have hconnect_from_base : ∀ (base : Fin M) (hb : base ∉ T),
      (∀ p : Fin M, (hp : p ∉ T) → H.Reachable (mkV base hb) (mkV p hp)) → H.Connected := by
    intro base hb hall
    have : Nonempty ((↑S : Set (Fin q ⊕ Fin q))ᶜ : Set (Fin q ⊕ Fin q)) := ⟨mkV base hb⟩
    refine ⟨fun u v => ?_⟩
    let pu : Fin M := e.symm u.1
    let pv : Fin M := e.symm v.1
    have hpu : pu ∉ T := fun h => u.2 (by
      have := (hmemT pu).mp h
      have heu : cycPos hq0 pu = u.1 := e.apply_symm_apply u.1
      rw [heu] at this; exact this)
    have hpv : pv ∉ T := fun h => v.2 (by
      have := (hmemT pv).mp h
      have hev : cycPos hq0 pv = v.1 := e.apply_symm_apply v.1
      rw [hev] at this; exact this)
    have hu_eq : mkV pu hpu = u := Subtype.ext (e.apply_symm_apply u.1)
    have hv_eq : mkV pv hpv = v := Subtype.ext (e.apply_symm_apply v.1)
    rw [← hu_eq, ← hv_eq]
    exact (hall pu hpu).symm.trans (hall pv hpv)
  -- Helper: clockwise distance from a to b in [0, M)
  let cdist (a b : Fin M) : ℕ := if a.val ≤ b.val then b.val - a.val else M + b.val - a.val
  have hcdist_lt : ∀ a b : Fin M, cdist a b < M := fun a b => by
    dsimp [cdist]; split_ifs <;> omega
  have hcdist_add : ∀ a b : Fin M, (a.val + cdist a b) % M = b.val := fun a b => by
    dsimp [cdist]; split_ifs with h
    · rw [show a.val + (b.val - a.val) = b.val by omega, Nat.mod_eq_of_lt b.isLt]
    · rw [show a.val + (M + b.val - a.val) = b.val + M * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
  have hcdist_pos : ∀ a b : Fin M, a ≠ b → 1 ≤ cdist a b := fun a b hne => by
    have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
    dsimp [cdist]; split_ifs <;> omega
  have hcdist_symm : ∀ a b : Fin M, a ≠ b → cdist a b + cdist b a = M := fun a b hne => by
    have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
    dsimp [cdist]; split_ifs <;> omega
  have hmod_step_eq : ∀ (a k1 k2 : ℕ), a < M → k1 < M → k2 < M →
      (a + k1) % M = (a + k2) % M → k1 = k2 := fun a k1 k2 _ hk1 hk2 h =>
    mod_add_left_cancel hk1 hk2 h
  by_cases hT2 : T.card ≤ 1
  · obtain ⟨x, hx⟩ : ∃ x : Fin M, ∀ z ∈ T, z = x := by
      have hle1 : ∀ a b : Fin M, a ∈ T → b ∈ T → a = b :=
        fun _ _ ha hb => Finset.card_le_one_iff.mp hT2 ha hb
      by_cases hne : T.Nonempty
      · obtain ⟨x, hxT⟩ := hne
        exact ⟨x, fun z hz => hle1 z x hz hxT⟩
      · exact ⟨⟨0, by omega⟩, fun z hz => absurd ⟨z, hz⟩ hne⟩
    let base : Fin M := ⟨(x.val + 1) % M, Nat.mod_lt _ (by omega)⟩
    have hbase : base ∉ T := by
      intro h
      have hv := congrArg Fin.val (hx base h)
      exact cyc_add_mod_ne x.isLt (by omega) (by omega) hv
    apply hconnect_from_base base hbase
    intro p hp
    by_cases hpx' : p = x
    · have hTempty : T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz; exact hp (by rw [hpx', ← hx z hz]; exact hz)
      have hgood : ∀ j ≤ M - 1, (⟨(x.val + 1 + j) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) ∉ T := by
        intro j _; rw [hTempty]; simp
      have hreach := hreach_arc (x.val + 1) (M - 1) hgood
      have hlast : (⟨(x.val + 1 + (M - 1)) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) = p := by
        apply Fin.ext; dsimp
        rw [show x.val + 1 + (M - 1) = x.val + M * 1 by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.isLt, hpx']
      have hlast_eq : mkV ⟨(x.val + 1 + (M - 1)) % M, Nat.mod_lt _ (by omega)⟩ (hgood (M - 1) le_rfl) = mkV p hp :=
        Subtype.ext (congrArg (cycPos hq0) hlast)
      rw [← hlast_eq]; exact hreach
    · let k : ℕ := cdist x p - 1
      have hdp1 : 1 ≤ cdist x p := hcdist_pos x p (Ne.symm hpx')
      have hdplt : cdist x p < M := hcdist_lt x p
      have hgood : ∀ j ≤ k, (⟨(x.val + 1 + j) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) ∉ T := by
        intro j hj hmem
        have hv := congrArg Fin.val (hx _ hmem)
        dsimp at hv
        rw [Nat.add_assoc] at hv
        exact cyc_add_mod_ne x.isLt (by omega) (by omega) hv
      have hreach := hreach_arc (x.val + 1) k hgood
      have hlast : (⟨(x.val + 1 + k) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) = p := by
        apply Fin.ext; dsimp
        rw [show x.val + 1 + k = x.val + cdist x p by omega, hcdist_add x p]
      have hlast_eq : mkV ⟨(x.val + 1 + k) % M, Nat.mod_lt _ (by omega)⟩ (hgood k le_rfl) = mkV p hp :=
        Subtype.ext (congrArg (cycPos hq0) hlast)
      rw [← hlast_eq]; exact hreach
  · have hT_eq2 : T.card = 2 := by omega
    obtain ⟨a, b, hab, hTab⟩ := Finset.card_eq_two.mp hT_eq2
    obtain ⟨x, y, hxy_ne, hTxy, hd_lo, hd_hi⟩ :
        ∃ x y : Fin M, x ≠ y ∧ T = {x, y} ∧ 1 ≤ cdist x y ∧ cdist x y ≤ q := by
      have hsum := hcdist_symm a b hab
      have hpos1 := hcdist_pos a b hab
      have hpos2 := hcdist_pos b a hab.symm
      by_cases hdir : cdist a b ≤ q
      · exact ⟨a, b, hab, hTab, hpos1, hdir⟩
      · exact ⟨b, a, hab.symm, by rw [hTab, Finset.pair_comm], hpos2, by omega⟩
    let d : ℕ := cdist x y
    have hy_mod : (x.val + d) % M = y.val := hcdist_add x y
    have hnotT_from_x : ∀ r : ℕ, 1 ≤ r → r < M → r ≠ d →
        (⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) ∉ T := by
      intro r hr1 hr2 hrd hmem
      rw [hTxy] at hmem
      rcases Finset.mem_insert.mp hmem with hx' | hy'
      · exact cyc_add_mod_ne x.isLt hr1 hr2 (congrArg Fin.val hx')
      · have hy'' := congrArg Fin.val (Finset.mem_singleton.mp hy')
        dsimp at hy''
        exact hrd (hmod_step_eq x.val r d x.isLt hr2 (by omega) (hy''.trans hy_mod.symm))
    have hstep_y : ∀ k : ℕ, (y.val + k) % M = (x.val + (d + k)) % M := fun k => by
      rw [← hy_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    -- Base vertex in arc 2: x + (d + 1) = y + 1
    let base : Fin M := ⟨(x.val + (d + 1)) % M, Nat.mod_lt _ (by omega)⟩
    have hbase : base ∉ T := hnotT_from_x (d + 1) (by omega) (by omega) (by omega)
    have harc2 : ∀ (r : ℕ) (hr1 : d + 1 ≤ r) (hr2 : r < M),
        H.Reachable (mkV base hbase)
          (mkV ⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ (hnotT_from_x r (by omega) hr2 (by omega))) := by
      intro r hr1 hr2
      let k := r - (d + 1)
      have hgood : ∀ j ≤ k, (⟨(x.val + (d + 1) + j) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) ∉ T := by
        intro j hj
        rw [show x.val + (d + 1) + j = x.val + (d + 1 + j) by omega]
        exact hnotT_from_x (d + 1 + j) (by omega) (by omega) (by omega)
      have hreach := hreach_arc (x.val + (d + 1)) k hgood
      have hlast : (⟨(x.val + (d + 1) + k) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) =
          ⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ := by
        apply Fin.ext; dsimp; congr 1; omega
      have hlast_eq : mkV ⟨(x.val + (d + 1) + k) % M, Nat.mod_lt _ (by omega)⟩ (hgood k le_rfl) =
          mkV ⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ (hnotT_from_x r (by omega) hr2 (by omega)) :=
        Subtype.ext (congrArg (cycPos hq0) hlast)
      rw [← hlast_eq]; exact hreach
    apply hconnect_from_base base hbase
    intro p hp
    have hpx : p ≠ x := fun h => hp (by rw [hTxy, h]; exact Finset.mem_insert_self x {y})
    have hpy : p ≠ y := fun h => hp (by rw [hTxy, h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    let r : ℕ := cdist x p
    have hr1 : 1 ≤ r := hcdist_pos x p hpx.symm
    have hr2 : r < M := hcdist_lt x p
    have hpeq : (⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) = p :=
      Fin.ext (hcdist_add x p)
    have hrd : r ≠ d := by
      intro heq
      apply hpy; apply Fin.ext
      rw [← hcdist_add x p, ← hcdist_add x y]; exact congrArg (fun z => (x.val + z) % M) heq
    have hp_mk : mkV ⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ (hnotT_from_x r hr1 hr2 hrd) = mkV p hp :=
      Subtype.ext (congrArg (cycPos hq0) hpeq)
    rw [← hp_mk]
    by_cases hside : d + 1 ≤ r
    · exact harc2 r hside hr2
    · -- p is in arc 1: 1 <= r < d, so d >= 2
      have hd2 : 2 ≤ d := by omega
      let a1 : Fin M := ⟨(x.val + 1) % M, Nat.mod_lt _ (by omega)⟩
      have ha1 : a1 ∉ T := hnotT_from_x 1 (by omega) (by omega) (by omega)
      have ha1_to_p : H.Reachable (mkV a1 ha1)
          (mkV ⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ (hnotT_from_x r hr1 hr2 hrd)) := by
        let k := r - 1
        have hgood : ∀ j ≤ k, (⟨(x.val + 1 + j) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) ∉ T := by
          intro j hj
          rw [show x.val + 1 + j = x.val + (1 + j) by omega]
          exact hnotT_from_x (1 + j) (by omega) (by omega) (by omega)
        have hreach := hreach_arc (x.val + 1) k hgood
        have hlast : (⟨(x.val + 1 + k) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) =
            ⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext; dsimp; congr 1; omega
        have hlast_eq : mkV ⟨(x.val + 1 + k) % M, Nat.mod_lt _ (by omega)⟩ (hgood k le_rfl) =
            mkV ⟨(x.val + r) % M, Nat.mod_lt _ (by omega)⟩ (hnotT_from_x r hr1 hr2 hrd) :=
          Subtype.ext (congrArg (cycPos hq0) hlast)
        rw [← hlast_eq]; exact hreach
      have hbase_to_a1 : H.Reachable (mkV base hbase) (mkV a1 ha1) := by
        by_cases ha1_odd : a1.val % 2 = 1
        · -- Case 1: a1 is odd -> chordOdd goes to a1 + M - 5 = x + (M - 4) in arc 2
          have hw_eq : (⟨(a1.val + M - 5) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) =
              ⟨(x.val + (M - 4)) % M, Nat.mod_lt _ (by omega)⟩ := by
            apply Fin.ext; dsimp [a1]
            have h1 : (x.val + 1) % M + M - 5 = ((x.val + 1) % M + (M - 5)) := by omega
            rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            congr 1; omega
          have hw : (⟨(x.val + (M - 4)) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) ∉ T :=
            hnotT_from_x (M - 4) (by omega) (by omega) (by omega)
          have hr1 := harc2 (M - 4) (by omega) (by omega)
          have hadj0 := cycPos_chord_odd hq a1 ha1_odd
          rw [hw_eq] at hadj0
          exact hr1.trans (SimpleGraph.Adj.reachable hadj0.symm)
        · by_cases hd3 : 3 ≤ d
          · -- Case 2: a1 even, d >= 3 -> a2 = x + 2 is odd -> chordOdd goes to x + (M - 3) in arc 2
            let a2 : Fin M := ⟨(x.val + 2) % M, Nat.mod_lt _ (by omega)⟩
            have ha2 : a2 ∉ T := hnotT_from_x 2 (by omega) (by omega) (by omega)
            have ha2_odd : a2.val % 2 = 1 := by
              have h2 : 2 ∣ M := ⟨q, rfl⟩
              have ha1e : (x.val + 1) % M % 2 = 0 := by dsimp [a1] at ha1_odd; omega
              dsimp [a2]
              rw [Nat.mod_mod_of_dvd _ h2] at ha1e ⊢; omega
            have hw_eq : (⟨(a2.val + M - 5) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) =
                ⟨(x.val + (M - 3)) % M, Nat.mod_lt _ (by omega)⟩ := by
              apply Fin.ext; dsimp [a2]
              have h1 : (x.val + 2) % M + M - 5 = ((x.val + 2) % M + (M - 5)) := by omega
              rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              congr 1; omega
            have hr1 := harc2 (M - 3) (by omega) (by omega)
            have hadj1 := cycPos_chord_odd hq a2 ha2_odd
            rw [hw_eq] at hadj1
            have ha2_step : (⟨(a1.val + 1) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) = a2 := by
              apply Fin.ext; dsimp [a1, a2]
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have hadj2 := cycPos_step hq a1
            rw [ha2_step] at hadj2
            have hs1 : H.Adj (mkV ⟨(x.val + (M - 3)) % M, Nat.mod_lt _ (by omega)⟩
                (hnotT_from_x (M - 3) (by omega) (by omega) (by omega))) (mkV a2 ha2) := hadj1.symm
            have hs2 : H.Adj (mkV a2 ha2) (mkV a1 ha1) := hadj2.symm
            exact hr1.trans (hs1.reachable.trans hs2.reachable)
          · -- Case 3: a1 even, d = 2 -> chordEven goes to a1 + 5 = x + 6 in arc 2
            have ha1_even : a1.val % 2 = 0 := by omega
            have hw_eq : (⟨(a1.val + 5) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) =
                ⟨(x.val + 6) % M, Nat.mod_lt _ (by omega)⟩ := by
              apply Fin.ext; dsimp [a1]
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have hr1 := harc2 6 (by omega) (by omega)
            have hadj0 := cycPos_chord_even hq a1 ha1_even
            rw [hw_eq] at hadj0
            exact hr1.trans (SimpleGraph.Adj.reachable hadj0.symm)
      exact hbase_to_a1.trans ha1_to_p

/-! ### Section 3: Modular IsAO2 circuit builder -/

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalAll (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl stepW w

lemma evalAll_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalAll (gs1 ++ gs2) w = evalAll gs2 (evalAll gs1 w) := by
  simp [evalAll, List.foldl_append]

lemma evalAll_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    evalAll (gs ++ [g]) w = stepW (evalAll gs w) g := by
  simp [evalAll, List.foldl_append]

lemma evalAll_length (gs : List Gate) (w : List Bool) :
    (evalAll gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalAll]
  | cons g gs ih =>
    simp only [evalAll, List.foldl_cons] at ih ⊢
    rw [ih (stepW w g)]
    simp [stepW]; omega

lemma evalAll_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (evalAll gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalAll, List.foldl_cons] at ih ⊢
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def Valid (N : ℕ) (gs : List Gate) (fs : List ((Fin N → Bool) → Bool)) : Prop :=
  (∀ x : Fin N → Bool, evalAll gs (List.ofFn x) = List.ofFn x ++ fs.map (fun f => f x)) ∧
  fs.length = gs.length ∧
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < N + j)

def Wire (N : ℕ) (fs : List ((Fin N → Bool) → Bool)) (w : ℕ) (F : (Fin N → Bool) → Bool) : Prop :=
  w < N + fs.length ∧
  ∀ x : Fin N → Bool, (List.ofFn x ++ fs.map (fun f => f x)).getD w false = F x

lemma valid_nil (N : ℕ) : Valid N [] [] := by
  refine ⟨fun x => by simp [evalAll], rfl, ?_, ?_⟩ <;> simp

lemma wire_in {N : ℕ} (fs : List ((Fin N → Bool) → Bool)) (v : Fin N) :
    Wire N fs v.val (fun x => x v) := by
  refine ⟨by omega, fun x => ?_⟩
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma wire_mono {N : ℕ} {fs : List ((Fin N → Bool) → Bool)} {w : ℕ}
    {F : (Fin N → Bool) → Bool} (h : Wire N fs w F) (fs' : List ((Fin N → Bool) → Bool)) :
    Wire N (fs ++ fs') w F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  have hlen : w < (List.ofFn x ++ fs.map (fun f => f x)).length := by
    simp; exact h.1
  rw [List.map_append, ← List.append_assoc, List.getD_append _ _ _ _ hlen]
  exact h.2 x

lemma wire_new {N : ℕ} (fs : List ((Fin N → Bool) → Bool)) (F : (Fin N → Bool) → Bool) :
    Wire N (fs ++ [F]) (N + fs.length) F := by
  refine ⟨by simp, fun x => ?_⟩
  rw [List.map_append, ← List.append_assoc,
      List.getD_append_right _ _ _ _ (by simp)]
  have hsub : N + fs.length - (List.ofFn x ++ fs.map (fun f => f x)).length = 0 := by
    simp
  rw [hsub]; simp

lemma push_gate {N : ℕ} {gs : List Gate} {fs : List ((Fin N → Bool) → Bool)}
    (hv : Valid N gs fs) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : ℕ) (A B : (Fin N → Bool) → Bool) (ha : Wire N fs a A) (hb : Wire N fs b B) :
    Valid N (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Wire N (fs ++ [fun x => op.eval [A x, B x]]) (N + fs.length)
        (fun x => op.eval [A x, B x]) := by
  obtain ⟨hsem, hlen, hgates, hrb⟩ := hv
  refine ⟨⟨?_, by simp [hlen], ?_, ?_⟩, wire_new fs _⟩
  · intro x
    rw [evalAll_snoc, hsem x]
    simp only [stepW, List.map_cons, List.map_nil, ha.2 x, hb.2 x, List.map_append,
      List.append_assoc]
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hgates g hg
    · simp only [List.mem_singleton] at hg; subst hg; exact ⟨hop, rfl⟩
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [List.getD_append _ _ _ _ hlt] at hi
      exact hrb j hlt i hi
    · rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := ha.1; omega
      · have := hb.1; omega

lemma push_or_chain {N : ℕ} :
    ∀ (rest : List (ℕ × ((Fin N → Bool) → Bool))) (gs : List Gate)
      (fs : List ((Fin N → Bool) → Bool)) (acc : ℕ) (F : (Fin N → Bool) → Bool),
      Valid N gs fs →
      Wire N fs acc F →
      (∀ p ∈ rest, Wire N fs p.1 p.2) →
      ∃ (gs' : List Gate) (fs' : List ((Fin N → Bool) → Bool)) (out : ℕ),
        gs'.length = rest.length ∧
        Valid N (gs ++ gs') (fs ++ fs') ∧
        Wire N (fs ++ fs') out (fun x => F x || rest.any (fun p => p.2 x)) := by
  intro rest
  induction rest with
  | nil =>
    intro gs fs acc F hv hacc _
    refine ⟨[], [], acc, rfl, by simpa using hv, ?_⟩
    simpa [Bool.or_false] using hacc
  | cons hd tl ih =>
    intro gs fs acc F hv hacc hrest
    have hhd : Wire N fs hd.1 hd.2 := hrest hd (List.mem_cons_self ..)
    obtain ⟨hv1, hw1⟩ := push_gate hv GateOp.or (Or.inr rfl) acc hd.1 F hd.2 hacc hhd
    have htl : ∀ p ∈ tl, Wire N (fs ++ [fun x => GateOp.or.eval [F x, hd.2 x]]) p.1 p.2 :=
      fun p hp => wire_mono (hrest p (List.mem_cons_of_mem hd hp)) _
    obtain ⟨gs', fs', out, hlen', hv2, hw2⟩ := ih _ _ _ _ hv1 hw1 htl
    refine ⟨[⟨GateOp.or, [acc, hd.1]⟩] ++ gs',
      [fun x => GateOp.or.eval [F x, hd.2 x]] ++ fs', out, by simp [hlen'],
      by simpa [List.append_assoc] using hv2, ?_⟩
    have heq : (fun x => GateOp.or.eval [F x, hd.2 x] || tl.any (fun p => p.2 x)) =
        (fun x => F x || (hd :: tl).any (fun p => p.2 x)) := by
      funext x
      simp [GateOp.eval, Bool.or_assoc]
    rw [heq] at hw2
    simpa [List.append_assoc] using hw2

lemma push_star {N : ℕ} {gs : List Gate} {fs : List ((Fin N → Bool) → Bool)}
    (hv : Valid N gs fs) (center : Fin N) (nbrs : List (Fin N)) (hne : nbrs ≠ []) :
    ∃ (gs' : List Gate) (fs' : List ((Fin N → Bool) → Bool)) (out : ℕ),
      gs'.length = nbrs.length ∧
      Valid N (gs ++ gs') (fs ++ fs') ∧
      Wire N (fs ++ fs') out (fun x => x center && nbrs.any (fun v => x v)) := by
  cases nbrs with
  | nil => exact absurd rfl hne
  | cons v0 rest =>
    let pairs := rest.map fun v => (v.val, fun x : Fin N → Bool => x v)
    have hrest : ∀ p ∈ pairs, Wire N fs p.1 p.2 := by
      intro p hp
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
      exact wire_in fs v
    obtain ⟨gs1, fs1, wOr, hlen1, hv1, hw1⟩ :=
      push_or_chain pairs gs fs v0.val (fun x => x v0) hv (wire_in fs v0) hrest
    obtain ⟨hv2, hw2⟩ := push_gate hv1 GateOp.and (Or.inl rfl) center.val wOr
      (fun x => x center) (fun x => x v0 || pairs.any (fun p => p.2 x))
      (wire_in (fs ++ fs1) center) hw1
    refine ⟨gs1 ++ [⟨GateOp.and, [center.val, wOr]⟩],
      fs1 ++ [fun x => GateOp.and.eval [x center, x v0 || pairs.any (fun p => p.2 x)]],
      N + (fs ++ fs1).length, by simp [hlen1, pairs],
      by simpa [List.append_assoc] using hv2, ?_⟩
    refine ⟨by have := hw2.1; simp only [List.length_append] at this ⊢; omega, fun x => ?_⟩
    have h := hw2.2 x
    rw [List.append_assoc] at h
    rw [h]
    simp [GateOp.eval, pairs, List.any_map, Function.comp_def]

lemma push_stars {N : ℕ} :
    ∀ (stars : List (Fin N × List (Fin N))) (gs : List Gate) (fs : List ((Fin N → Bool) → Bool)),
      Valid N gs fs →
      (∀ s ∈ stars, s.2 ≠ []) →
      ∃ (gs' : List Gate) (fs' : List ((Fin N → Bool) → Bool))
        (outs : List (ℕ × ((Fin N → Bool) → Bool))),
        gs'.length = (stars.map fun s => s.2.length).sum ∧
        outs.length = stars.length ∧
        Valid N (gs ++ gs') (fs ++ fs') ∧
        (∀ p ∈ outs, Wire N (fs ++ fs') p.1 p.2) ∧
        (∀ x, outs.any (fun p => p.2 x) =
          stars.any (fun s => x s.1 && s.2.any (fun v => x v))) := by
  intro stars
  induction stars with
  | nil =>
    intro gs fs hv _
    exact ⟨[], [], [], rfl, rfl, by simpa using hv, by simp, fun _ => rfl⟩
  | cons s tl ih =>
    intro gs fs hv hne
    obtain ⟨gs1, fs1, out1, hlen1, hv1, hw1⟩ := push_star hv s.1 s.2 (hne s (List.mem_cons_self ..))
    obtain ⟨gs2, fs2, outs2, hlen2, hol2, hv2, hws2, hany2⟩ :=
      ih _ _ hv1 (fun s' hs' => hne s' (List.mem_cons_of_mem s hs'))
    refine ⟨gs1 ++ gs2, fs1 ++ fs2,
      (out1, fun x => x s.1 && s.2.any (fun v => x v)) :: outs2,
      by simp [hlen1, hlen2], by simp [hol2],
      by simpa [List.append_assoc] using hv2, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa [List.append_assoc] using wire_mono hw1 fs2
      · simpa [List.append_assoc] using hws2 p hp
    · intro x
      simp [hany2 x]

def shiftWire (n N off : ℕ) (emb : Fin n → Fin N) (w : ℕ) : ℕ :=
  if h : w < n then (emb ⟨w, h⟩).val else N + off + (w - n)

def shiftGate (n N off : ℕ) (emb : Fin n → Fin N) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire n N off emb)⟩

lemma push_copy_prefix {n N : ℕ} (emb : Fin n → Fin N) (off : ℕ)
    (gsC : List Gate) (gs0 : List Gate) (fs0 : List ((Fin N → Bool) → Bool))
    (hoff : off = gs0.length)
    (hv0 : Valid N gs0 fs0)
    (hAO : ∀ g ∈ gsC, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRB : ∀ j < gsC.length, ∀ i ∈ (gsC.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) :
    ∃ fsC : List ((Fin N → Bool) → Bool),
      fsC.length = gsC.length ∧
      Valid N (gs0 ++ gsC.map (shiftGate n N off emb)) (fs0 ++ fsC) ∧
      ∀ (x : Fin N → Bool) (w : ℕ), w < n + gsC.length →
        (List.ofFn x ++ (fs0 ++ fsC).map (fun f => f x)).getD (shiftWire n N off emb w) false =
          (evalAll gsC (List.ofFn (x ∘ emb))).getD w false := by
  induction gsC using List.reverseRecOn with
  | nil =>
    refine ⟨[], rfl, by simpa using hv0, ?_⟩
    intro x w hw
    have hw' : w < n := by simpa using hw
    simp only [shiftWire, hw', ↓reduceDIte, List.append_nil, evalAll, List.foldl_nil]
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, hw', Function.comp_def]
  | append_singleton gsC g ih =>
    have hAO' : ∀ g' ∈ gsC, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
      fun g' hg' => hAO g' (List.mem_append_left _ hg')
    have hRB' : ∀ j < gsC.length, ∀ i ∈ (gsC.getD j ⟨GateOp.or, []⟩).inputs, i < n + j := by
      intro j hj i hi
      have hi' : i ∈ ((gsC ++ [g]).getD j ⟨GateOp.or, []⟩).inputs := by
        rwa [List.getD_append _ _ _ _ hj]
      exact hRB j (by simp; omega) i hi'
    obtain ⟨fsC, hfsClen, hv1, hsim1⟩ := ih hAO' hRB'
    have hgAO := hAO g (by simp)
    have hgRB : ∀ i ∈ g.inputs, i < n + gsC.length := by
      intro i hi
      have hget : (gsC ++ [g]).getD gsC.length ⟨GateOp.or, []⟩ = g := by
        rw [List.getD_append_right _ _ _ _ le_rfl]; simp
      have hi' : i ∈ ((gsC ++ [g]).getD gsC.length ⟨GateOp.or, []⟩).inputs := by
        rw [hget]; exact hi
      exact hRB gsC.length (by simp) i hi'
    rcases hgAO with ⟨hgop, hglen⟩
    rcases List.length_eq_two.mp hglen with ⟨i1, i2, hginp⟩
    have hi1 : i1 < n + gsC.length := hgRB i1 (by rw [hginp]; simp)
    have hi2 : i2 < n + gsC.length := hgRB i2 (by rw [hginp]; simp)
    have hsw_lt : ∀ w, w < n + gsC.length → shiftWire n N off emb w < N + (fs0 ++ fsC).length := by
      intro w hw
      have hfs0len : fs0.length = gs0.length := hv0.2.1
      unfold shiftWire
      split_ifs with hwn
      · have := (emb ⟨w, hwn⟩).isLt; omega
      · simp [hfs0len, hfsClen, hoff]; omega
    have hw1 : Wire N (fs0 ++ fsC) (shiftWire n N off emb i1)
        (fun x => (evalAll gsC (List.ofFn (x ∘ emb))).getD i1 false) :=
      ⟨hsw_lt i1 hi1, fun x => hsim1 x i1 hi1⟩
    have hw2 : Wire N (fs0 ++ fsC) (shiftWire n N off emb i2)
        (fun x => (evalAll gsC (List.ofFn (x ∘ emb))).getD i2 false) :=
      ⟨hsw_lt i2 hi2, fun x => hsim1 x i2 hi2⟩
    let Fnew : (Fin N → Bool) → Bool := fun x =>
      g.op.eval [(evalAll gsC (List.ofFn (x ∘ emb))).getD i1 false,
                 (evalAll gsC (List.ofFn (x ∘ emb))).getD i2 false]
    obtain ⟨hv2, hwnew⟩ := push_gate hv1 g.op hgop
      (shiftWire n N off emb i1) (shiftWire n N off emb i2) _ _ hw1 hw2
    have hsg : shiftGate n N off emb g =
        ⟨g.op, [shiftWire n N off emb i1, shiftWire n N off emb i2]⟩ := by
      simp [shiftGate, hginp]
    refine ⟨fsC ++ [Fnew], by simp [hfsClen], ?_, ?_⟩
    · rw [List.map_append, List.map_singleton, hsg, ← List.append_assoc, ← List.append_assoc]
      exact hv2
    · intro x w hw
      rw [List.length_append, List.length_singleton] at hw
      rw [evalAll_snoc]
      by_cases hlt : w < n + gsC.length
      · have hw_len : w < (evalAll gsC (List.ofFn (x ∘ emb))).length := by
          rw [evalAll_length]; simp; exact hlt
        rw [show stepW (evalAll gsC (List.ofFn (x ∘ emb))) g =
              evalAll gsC (List.ofFn (x ∘ emb)) ++
                [g.op.eval (g.inputs.map fun i => (evalAll gsC (List.ofFn (x ∘ emb))).getD i false)]
              from rfl,
            List.getD_append _ _ _ _ hw_len]
        have hwm := wire_mono (⟨hsw_lt w hlt, fun y => hsim1 y w hlt⟩ :
          Wire N (fs0 ++ fsC) (shiftWire n N off emb w)
            (fun y => (evalAll gsC (List.ofFn (y ∘ emb))).getD w false)) [Fnew]
        rw [← List.append_assoc]
        exact hwm.2 x
      · have heqw : w = n + gsC.length := by omega
        subst heqw
        have hfs0len : fs0.length = gs0.length := hv0.2.1
        have hsw_eq : shiftWire n N off emb (n + gsC.length) = N + (fs0 ++ fsC).length := by
          unfold shiftWire
          have hnot : ¬n + gsC.length < n := by omega
          simp only [hnot, ↓reduceDIte]
          simp [hfs0len, hfsClen, hoff]; omega
        rw [← List.append_assoc, hsw_eq, hwnew.2 x]
        have hlen_c : (evalAll gsC (List.ofFn (x ∘ emb))).length = n + gsC.length := by
          rw [evalAll_length]; simp
        unfold stepW
        rw [List.getD_append_right _ _ _ _ (by omega), hlen_c, Nat.sub_self]
        simp [hginp]

lemma push_copies {n N : ℕ} (C : Circuit) (hAO : IsAO2 n C) (hout : C.output < n + C.size) :
    ∀ (embs : List (Fin n → Fin N)) (gs : List Gate) (fs : List ((Fin N → Bool) → Bool)),
      Valid N gs fs →
      ∃ (gs' : List Gate) (fs' : List ((Fin N → Bool) → Bool))
        (outs : List (ℕ × ((Fin N → Bool) → Bool))),
        gs'.length = embs.length * C.size ∧
        outs.length = embs.length ∧
        Valid N (gs ++ gs') (fs ++ fs') ∧
        (∀ p ∈ outs, Wire N (fs ++ fs') p.1 p.2) ∧
        (∀ x, outs.any (fun p => p.2 x) =
          embs.any (fun emb => C.eval (List.ofFn (x ∘ emb)))) := by
  intro embs
  induction embs with
  | nil =>
    intro gs fs hv
    exact ⟨[], [], [], by simp, rfl, by simpa using hv, by simp, fun _ => rfl⟩
  | cons emb tl ih =>
    intro gs fs hv
    have hAO' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
      fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩
    have hRB' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < n + j :=
      fun j hj i hi => hAO.2.1 j hj i hi
    obtain ⟨fs1, hfs1len, hv1, hsim1⟩ := push_copy_prefix emb gs.length C.gates gs fs rfl hv hAO' hRB'
    have hfs0len : fs.length = gs.length := hv.2.1
    have hout_lt : shiftWire n N gs.length emb C.output < N + (fs ++ fs1).length := by
      unfold shiftWire
      split_ifs with hlt
      · have := (emb ⟨C.output, hlt⟩).isLt; omega
      · simp [hfs0len, hfs1len]; unfold Circuit.size at hout; omega
    have hw1 : Wire N (fs ++ fs1) (shiftWire n N gs.length emb C.output)
        (fun x => C.eval (List.ofFn (x ∘ emb))) :=
      ⟨hout_lt, fun x => hsim1 x C.output hout⟩
    obtain ⟨gs2, fs2, outs2, hlen2, hol2, hv2, hws2, hany2⟩ := ih _ _ hv1
    refine ⟨C.gates.map (shiftGate n N gs.length emb) ++ gs2, fs1 ++ fs2,
      (shiftWire n N gs.length emb C.output, fun x => C.eval (List.ofFn (x ∘ emb))) :: outs2,
      by simp only [List.length_append, List.length_map, List.length_cons, hlen2, Circuit.size]
         rw [Nat.add_mul, one_mul, Nat.add_comm], by simp [hol2],
      by simpa [List.append_assoc] using hv2, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa [List.append_assoc] using wire_mono hw1 fs2
      · simpa [List.append_assoc] using hws2 p hp
    · intro x
      simp [hany2 x]

lemma valid_to_isAO2 {N : ℕ} {gs : List Gate} {fs : List ((Fin N → Bool) → Bool)} {out : ℕ}
    {F : (Fin N → Bool) → Bool} (hv : Valid N gs fs) (hw : Wire N fs out F) :
    IsAO2 N ⟨gs, out⟩ ∧ circuitFun N ⟨gs, out⟩ = F := by
  obtain ⟨hsem, _, hgates, hrb⟩ := hv
  refine ⟨⟨fun g hg => (hgates g hg).1, fun j hj i hi => hrb j hj i hi,
           fun g hg => (hgates g hg).2⟩, ?_⟩
  funext x
  change (evalAll gs (List.ofFn x)).getD out false = F x
  rw [hsem x]
  exact hw.2 x

/-! ### Section 4: The amplified graph on AmpV m t (10 * q0) -/

abbrev LeftV (m t q : ℕ) := (Fin m × Fin t) ⊕ Fin q ⊕ Fin q
abbrev RightV (m t q : ℕ) := (Fin m × Fin t) ⊕ Fin q ⊕ Fin q
abbrev AmpV (m t q : ℕ) := LeftV m t q ⊕ RightV m t q

def vA0 {m t q : ℕ} (i : Fin m) (r : Fin t) : AmpV m t q := Sum.inl (Sum.inl (i, r))
def vX1 {m t q : ℕ} (x : Fin q) : AmpV m t q := Sum.inl (Sum.inr (Sum.inl x))
def vWL {m t q : ℕ} (x : Fin q) : AmpV m t q := Sum.inl (Sum.inr (Sum.inr x))
def vB0 {m t q : ℕ} (i : Fin m) (r : Fin t) : AmpV m t q := Sum.inr (Sum.inl (i, r))
def vWR {m t q : ℕ} (x : Fin q) : AmpV m t q := Sum.inr (Sum.inr (Sum.inl x))
def vY2 {m t q : ℕ} (x : Fin q) : AmpV m t q := Sum.inr (Sum.inr (Sum.inr x))

lemma mul_add_lt_mul {a b c d : ℕ} (ha : a < c) (hb : b < d) : a * d + b < c * d := by
  have h1 : (a + 1) * d ≤ c * d := Nat.mul_le_mul_right d ha
  rw [Nat.add_mul, one_mul] at h1
  omega

lemma mul_add_inj {a1 a2 b1 b2 d : ℕ} (hb1 : b1 < d) (hb2 : b2 < d)
    (heq : a1 * d + b1 = a2 * d + b2) : a1 = a2 ∧ b1 = b2 := by
  have ha : a1 = a2 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.mul_le_mul_right d h; rw [Nat.succ_mul] at this; omega
    · have := Nat.mul_le_mul_right d h; rw [Nat.succ_mul] at this; omega
  exact ⟨ha, by subst ha; omega⟩

def slotUL {m t uL q0 : ℕ} (hs : m * uL + 3 * (m * t) + 3 ≤ q0) (i : Fin m) (j : Fin uL) :
    Fin (10 * q0) :=
  ⟨10 * (i.val * uL + j.val), by have := mul_add_lt_mul i.isLt j.isLt; omega⟩

def slotAttA {m t uL q0 : ℕ} (hs : m * uL + 3 * (m * t) + 3 ≤ q0)
    (i : Fin m) (r : Fin t) (d : Fin 3) : Fin (10 * q0) :=
  ⟨10 * (m * uL + 3 * (i.val * t + r.val) + d.val), by
    have := mul_add_lt_mul i.isLt r.isLt; have := d.isLt; omega⟩

def slotBrR {m t uL q0 : ℕ} (hs : m * uL + 3 * (m * t) + 3 ≤ q0) (d : Fin 3) : Fin (10 * q0) :=
  ⟨10 * (m * uL + 3 * (m * t) + d.val), by have := d.isLt; omega⟩

def slotUR {m t uR q0 : ℕ} (hs : m * uR + 3 * (m * t) + 3 ≤ q0) (i : Fin m) (k : Fin uR) :
    Fin (10 * q0) :=
  ⟨10 * (i.val * uR + k.val), by have := mul_add_lt_mul i.isLt k.isLt; omega⟩

def slotAttB {m t uR q0 : ℕ} (hs : m * uR + 3 * (m * t) + 3 ≤ q0)
    (i : Fin m) (r : Fin t) (d : Fin 3) : Fin (10 * q0) :=
  ⟨10 * (m * uR + 3 * (i.val * t + r.val) + d.val), by
    have := mul_add_lt_mul i.isLt r.isLt; have := d.isLt; omega⟩

def slotBrL {m t uR q0 : ℕ} (hs : m * uR + 3 * (m * t) + 3 ≤ q0) (d : Fin 3) : Fin (10 * q0) :=
  ⟨10 * (m * uR + 3 * (m * t) + d.val), by have := d.isLt; omega⟩

lemma slotUL_inj {m t uL q0 : ℕ} (hs : m * uL + 3 * (m * t) + 3 ≤ q0)
    {i1 i2 : Fin m} {j1 j2 : Fin uL} (h : slotUL hs i1 j1 = slotUL hs i2 j2) :
    i1 = i2 ∧ j1 = j2 := by
  have hv : i1.val * uL + j1.val = i2.val * uL + j2.val := by
    have := congrArg Fin.val h; dsimp [slotUL] at this; omega
  obtain ⟨hi, hj⟩ := mul_add_inj j1.isLt j2.isLt hv
  exact ⟨Fin.ext hi, Fin.ext hj⟩

lemma slotUR_inj {m t uR q0 : ℕ} (hs : m * uR + 3 * (m * t) + 3 ≤ q0)
    {i1 i2 : Fin m} {k1 k2 : Fin uR} (h : slotUR hs i1 k1 = slotUR hs i2 k2) :
    i1 = i2 ∧ k1 = k2 := by
  have hv : i1.val * uR + k1.val = i2.val * uR + k2.val := by
    have := congrArg Fin.val h; dsimp [slotUR] at this; omega
  obtain ⟨hi, hk⟩ := mul_add_inj k1.isLt k2.isLt hv
  exact ⟨Fin.ext hi, Fin.ext hk⟩

lemma slotAttA_inj {m t uL q0 : ℕ} (hs : m * uL + 3 * (m * t) + 3 ≤ q0)
    {i1 i2 : Fin m} {r1 r2 : Fin t} {d1 d2 : Fin 3}
    (h : slotAttA hs i1 r1 d1 = slotAttA hs i2 r2 d2) :
    i1 = i2 ∧ r1 = r2 ∧ d1 = d2 := by
  have hv : 3 * (i1.val * t + r1.val) + d1.val = 3 * (i2.val * t + r2.val) + d2.val := by
    have := congrArg Fin.val h; dsimp [slotAttA] at this; omega
  have hd : d1.val = d2.val := by omega
  have hir : i1.val * t + r1.val = i2.val * t + r2.val := by omega
  obtain ⟨hi, hr⟩ := mul_add_inj r1.isLt r2.isLt hir
  exact ⟨Fin.ext hi, Fin.ext hr, Fin.ext hd⟩

lemma slotAttB_inj {m t uR q0 : ℕ} (hs : m * uR + 3 * (m * t) + 3 ≤ q0)
    {i1 i2 : Fin m} {r1 r2 : Fin t} {d1 d2 : Fin 3}
    (h : slotAttB hs i1 r1 d1 = slotAttB hs i2 r2 d2) :
    i1 = i2 ∧ r1 = r2 ∧ d1 = d2 := by
  have hv : 3 * (i1.val * t + r1.val) + d1.val = 3 * (i2.val * t + r2.val) + d2.val := by
    have := congrArg Fin.val h; dsimp [slotAttB] at this; omega
  have hd : d1.val = d2.val := by omega
  have hir : i1.val * t + r1.val = i2.val * t + r2.val := by omega
  obtain ⟨hi, hr⟩ := mul_add_inj r1.isLt r2.isLt hir
  exact ⟨Fin.ext hi, Fin.ext hr, Fin.ext hd⟩

lemma slotBrR_inj {m t uL q0 : ℕ} (hs : m * uL + 3 * (m * t) + 3 ≤ q0)
    {d1 d2 : Fin 3} (h : slotBrR hs d1 = slotBrR hs d2) : d1 = d2 := by
  apply Fin.ext; have := congrArg Fin.val h; dsimp [slotBrR] at this; omega

lemma slotBrL_inj {m t uR q0 : ℕ} (hs : m * uR + 3 * (m * t) + 3 ≤ q0)
    {d1 d2 : Fin 3} (h : slotBrL hs d1 = slotBrL hs d2) : d1 = d2 := by
  apply Fin.ext; have := congrArg Fin.val h; dsimp [slotBrL] at this; omega

def dirAdj {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0) :
    LeftV m t (10 * q0) → RightV m t (10 * q0) → Prop
  | Sum.inl (i, r), Sum.inl (i', r') =>
      i = i' ∧ G.Adj (eG (Sum.inl (Sum.inl r))) (eG (Sum.inr (Sum.inl r')))
  | Sum.inl (i, r), Sum.inr (Sum.inr y) =>
      ∃ k : Fin uR, y = slotUR hsR i k ∧
        G.Adj (eG (Sum.inl (Sum.inl r))) (eG (Sum.inr (Sum.inr k)))
  | Sum.inl (i, r), Sum.inr (Sum.inl wR) =>
      ∃ d : Fin 3, wR = slotAttA hsL i r d
  | Sum.inr (Sum.inl x), Sum.inl (i, r') =>
      ∃ j : Fin uL, x = slotUL hsL i j ∧
        G.Adj (eG (Sum.inl (Sum.inr j))) (eG (Sum.inr (Sum.inl r')))
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl wR) =>
      cycAdj (10 * q0) x wR
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) =>
      False
  | Sum.inr (Sum.inr wL), Sum.inl (i, r') =>
      ∃ d : Fin 3, wL = slotAttB hsR i r' d
  | Sum.inr (Sum.inr wL), Sum.inr (Sum.inl wR) =>
      ∃ d : Fin 3, wL = slotBrL hsR d ∧ wR = slotBrR hsL d
  | Sum.inr (Sum.inr wL), Sum.inr (Sum.inr y) =>
      cycAdj (10 * q0) y wL

def ampGraph0 {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0) :
    SimpleGraph (AmpV m t (10 * q0)) where
  Adj u v := match u, v with
    | Sum.inl l, Sum.inr r => dirAdj G eG hsL hsR l r
    | Sum.inr r, Sum.inl l => dirAdj G eG hsL hsR l r
    | _, _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

def copyEmb0 {n t uL uR m q0 : ℕ}
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (i : Fin m) (v : Fin n) : AmpV m t (10 * q0) :=
  match eG.symm v with
  | Sum.inl (Sum.inl r) => vA0 i r
  | Sum.inl (Sum.inr j) => vX1 (slotUL hsL i j)
  | Sum.inr (Sum.inl r) => vB0 i r
  | Sum.inr (Sum.inr k) => vY2 (slotUR hsR i k)

lemma noFourCycle_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h : NoFourCycle G) {a b w1 w2 : Fin n} (hne : a ≠ b)
    (h1a : G.Adj a w1) (h1b : G.Adj b w1) (h2a : G.Adj a w2) (h2b : G.Adj b w2) :
    w1 = w2 :=
  Finset.card_le_one.mp (h a b hne) w1
    (Finset.mem_filter.mpr ⟨Finset.mem_univ w1, h1a, h1b⟩) w2
    (Finset.mem_filter.mpr ⟨Finset.mem_univ w2, h2a, h2b⟩)

lemma ampGraph0_bipartite {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0) :
    (ampGraph0 G eG hsL hsR).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk
    (fun u => match u with | Sum.inl _ => (0 : Fin 2) | Sum.inr _ => (1 : Fin 2))
    (fun {u v} h => by cases u <;> cases v <;> simp [ampGraph0] at h ⊢)⟩

lemma ampGraph0_perfectMatching {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (hmatch : ∀ r : Fin t, G.Adj (eG (Sum.inl (Sum.inl r))) (eG (Sum.inr (Sum.inl r)))) :
    ∃ M : (ampGraph0 G eG hsL hsR).Subgraph, M.IsPerfectMatching := by
  let mate : AmpV m t (10 * q0) → AmpV m t (10 * q0)
    | Sum.inl (Sum.inl p) => Sum.inr (Sum.inl p)
    | Sum.inr (Sum.inl p) => Sum.inl (Sum.inl p)
    | Sum.inl (Sum.inr (Sum.inl x)) => Sum.inr (Sum.inr (Sum.inl x))
    | Sum.inr (Sum.inr (Sum.inl x)) => Sum.inl (Sum.inr (Sum.inl x))
    | Sum.inl (Sum.inr (Sum.inr x)) => Sum.inr (Sum.inr (Sum.inr x))
    | Sum.inr (Sum.inr (Sum.inr x)) => Sum.inl (Sum.inr (Sum.inr x))
  have hmate_inv : ∀ u, mate (mate u) = u := by
    intro u; rcases u with (p | x | x) | (p | x | x) <;> rfl
  have hmate_adj : ∀ u, (ampGraph0 G eG hsL hsR).Adj u (mate u) := by
    intro u
    rcases u with (⟨i, r⟩ | x | x) | (⟨i, r⟩ | x | x)
    · exact ⟨rfl, hmatch r⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact ⟨rfl, hmatch r⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
  let M : (ampGraph0 G eG hsL hsR).Subgraph := {
    verts := Set.univ
    Adj := fun u v => v = mate u
    adj_sub := fun {u v} h => by rw [h]; exact hmate_adj u
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun {u v} h => by rw [h, hmate_inv]⟩
  }
  refine ⟨M, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr fun v => ?_⟩
  exact ⟨mate v, rfl, fun w hw => hw⟩

def isRightOutside {m t uR q0 : ℕ} (hsR : m * uR + 3 * (m * t) + 3 ≤ q0) :
    RightV m t (10 * q0) → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr y) => ∃ i k, y = slotUR hsR i k

def isLeftOutside {m t uL q0 : ℕ} (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) :
    LeftV m t (10 * q0) → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inr _) => True
  | Sum.inr (Sum.inl x) => ∃ i j, x = slotUL hsL i j

lemma wL_unique_outside {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (wL : Fin (10 * q0)) (r1 r2 : RightV m t (10 * q0))
    (h1 : dirAdj G eG hsL hsR (Sum.inr (Sum.inr wL)) r1)
    (h2 : dirAdj G eG hsL hsR (Sum.inr (Sum.inr wL)) r2)
    (ho1 : isRightOutside hsR r1) (ho2 : isRightOutside hsR r2) :
    r1 = r2 := by
  rcases r1 with ⟨i1, p1⟩ | wR1 | y1 <;> rcases r2 with ⟨i2, p2⟩ | wR2 | y2
  · obtain ⟨d1, hd1⟩ := h1; obtain ⟨d2, hd2⟩ := h2
    obtain ⟨hi, hp, _⟩ := slotAttB_inj hsR (hd1.symm.trans hd2)
    subst hi; subst hp; rfl
  · exfalso
    obtain ⟨d1, hd1⟩ := h1; obtain ⟨d2, hd2, _⟩ := h2
    have hv := congrArg Fin.val (hd1.symm.trans hd2)
    dsimp [slotAttB, slotBrL] at hv
    have := mul_add_lt_mul i1.isLt p1.isLt; have := d1.isLt; have := d2.isLt; omega
  · exfalso
    obtain ⟨d1, hd1⟩ := h1; obtain ⟨i2, k2, rfl⟩ := ho2
    have hslot := cycAdj_mul10_slot (i2.val * uR + k2.val)
      (by have := mul_add_lt_mul i2.isLt k2.isLt; omega) wL h2
    have hdiv : wL.val / 10 = m * uR + 3 * (i1.val * t + p1.val) + d1.val := by
      rw [hd1]; dsimp [slotAttB]; omega
    have := mul_add_lt_mul i2.isLt k2.isLt; omega
  · exfalso
    obtain ⟨d1, hd1, _⟩ := h1; obtain ⟨d2, hd2⟩ := h2
    have hv := congrArg Fin.val (hd1.symm.trans hd2)
    dsimp [slotAttB, slotBrL] at hv
    have := mul_add_lt_mul i2.isLt p2.isLt; have := d1.isLt; have := d2.isLt; omega
  · obtain ⟨d1, hd1, hw1⟩ := h1; obtain ⟨d2, hd2, hw2⟩ := h2
    have hd := slotBrL_inj hsR (hd1.symm.trans hd2)
    subst hd; rw [hw1, hw2]
  · exfalso
    obtain ⟨d1, hd1, _⟩ := h1; obtain ⟨i2, k2, rfl⟩ := ho2
    have hslot := cycAdj_mul10_slot (i2.val * uR + k2.val)
      (by have := mul_add_lt_mul i2.isLt k2.isLt; omega) wL h2
    have hdiv : wL.val / 10 = m * uR + 3 * (m * t) + d1.val := by
      rw [hd1]; dsimp [slotBrL]; omega
    have := mul_add_lt_mul i2.isLt k2.isLt; omega
  · exfalso
    obtain ⟨i1, k1, rfl⟩ := ho1; obtain ⟨d2, hd2⟩ := h2
    have hslot := cycAdj_mul10_slot (i1.val * uR + k1.val)
      (by have := mul_add_lt_mul i1.isLt k1.isLt; omega) wL h1
    have hdiv : wL.val / 10 = m * uR + 3 * (i2.val * t + p2.val) + d2.val := by
      rw [hd2]; dsimp [slotAttB]; omega
    have := mul_add_lt_mul i1.isLt k1.isLt; omega
  · exfalso
    obtain ⟨i1, k1, rfl⟩ := ho1; obtain ⟨d2, hd2, _⟩ := h2
    have hslot := cycAdj_mul10_slot (i1.val * uR + k1.val)
      (by have := mul_add_lt_mul i1.isLt k1.isLt; omega) wL h1
    have hdiv : wL.val / 10 = m * uR + 3 * (m * t) + d2.val := by
      rw [hd2]; dsimp [slotBrL]; omega
    have := mul_add_lt_mul i1.isLt k1.isLt; omega
  · obtain ⟨i1, k1, rfl⟩ := ho1; obtain ⟨i2, k2, rfl⟩ := ho2
    have hs1 := cycAdj_mul10_slot (i1.val * uR + k1.val)
      (by have := mul_add_lt_mul i1.isLt k1.isLt; omega) wL h1
    have hs2 := cycAdj_mul10_slot (i2.val * uR + k2.val)
      (by have := mul_add_lt_mul i2.isLt k2.isLt; omega) wL h2
    obtain ⟨hi, hk⟩ := mul_add_inj k1.isLt k2.isLt (hs1.symm.trans hs2)
    have hi' : i1 = i2 := Fin.ext hi
    have hk' : k1 = k2 := Fin.ext hk
    subst hi'; subst hk'; rfl

lemma wR_unique_outside {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (wR : Fin (10 * q0)) (l1 l2 : LeftV m t (10 * q0))
    (h1 : dirAdj G eG hsL hsR l1 (Sum.inr (Sum.inl wR)))
    (h2 : dirAdj G eG hsL hsR l2 (Sum.inr (Sum.inl wR)))
    (ho1 : isLeftOutside hsL l1) (ho2 : isLeftOutside hsL l2) :
    l1 = l2 := by
  rcases l1 with ⟨i1, p1⟩ | x1 | wL1 <;> rcases l2 with ⟨i2, p2⟩ | x2 | wL2
  · obtain ⟨d1, hd1⟩ := h1; obtain ⟨d2, hd2⟩ := h2
    obtain ⟨hi, hp, _⟩ := slotAttA_inj hsL (hd1.symm.trans hd2)
    subst hi; subst hp; rfl
  · exfalso
    obtain ⟨d1, hd1⟩ := h1; obtain ⟨i2, j2, rfl⟩ := ho2
    have hslot := cycAdj_mul10_slot (i2.val * uL + j2.val)
      (by have := mul_add_lt_mul i2.isLt j2.isLt; omega) wR h2
    have hdiv : wR.val / 10 = m * uL + 3 * (i1.val * t + p1.val) + d1.val := by
      rw [hd1]; dsimp [slotAttA]; omega
    have := mul_add_lt_mul i2.isLt j2.isLt; omega
  · exfalso
    obtain ⟨d1, hd1⟩ := h1; obtain ⟨d2, _, hd2⟩ := h2
    have hv := congrArg Fin.val (hd1.symm.trans hd2)
    dsimp [slotAttA, slotBrR] at hv
    have := mul_add_lt_mul i1.isLt p1.isLt; have := d1.isLt; have := d2.isLt; omega
  · exfalso
    obtain ⟨i1, j1, rfl⟩ := ho1; obtain ⟨d2, hd2⟩ := h2
    have hslot := cycAdj_mul10_slot (i1.val * uL + j1.val)
      (by have := mul_add_lt_mul i1.isLt j1.isLt; omega) wR h1
    have hdiv : wR.val / 10 = m * uL + 3 * (i2.val * t + p2.val) + d2.val := by
      rw [hd2]; dsimp [slotAttA]; omega
    have := mul_add_lt_mul i1.isLt j1.isLt; omega
  · obtain ⟨i1, j1, rfl⟩ := ho1; obtain ⟨i2, j2, rfl⟩ := ho2
    have hs1 := cycAdj_mul10_slot (i1.val * uL + j1.val)
      (by have := mul_add_lt_mul i1.isLt j1.isLt; omega) wR h1
    have hs2 := cycAdj_mul10_slot (i2.val * uL + j2.val)
      (by have := mul_add_lt_mul i2.isLt j2.isLt; omega) wR h2
    obtain ⟨hi, hj⟩ := mul_add_inj j1.isLt j2.isLt (hs1.symm.trans hs2)
    have hi' : i1 = i2 := Fin.ext hi
    have hj' : j1 = j2 := Fin.ext hj
    subst hi'; subst hj'; rfl
  · exfalso
    obtain ⟨i1, j1, rfl⟩ := ho1; obtain ⟨d2, _, hd2⟩ := h2
    have hslot := cycAdj_mul10_slot (i1.val * uL + j1.val)
      (by have := mul_add_lt_mul i1.isLt j1.isLt; omega) wR h1
    have hdiv : wR.val / 10 = m * uL + 3 * (m * t) + d2.val := by
      rw [hd2]; dsimp [slotBrR]; omega
    have := mul_add_lt_mul i1.isLt j1.isLt; omega
  · exfalso
    obtain ⟨d1, _, hd1⟩ := h1; obtain ⟨d2, hd2⟩ := h2
    have hv := congrArg Fin.val (hd1.symm.trans hd2)
    dsimp [slotAttA, slotBrR] at hv
    have := mul_add_lt_mul i2.isLt p2.isLt; have := d1.isLt; have := d2.isLt; omega
  · exfalso
    obtain ⟨d1, _, hd1⟩ := h1; obtain ⟨i2, j2, rfl⟩ := ho2
    have hslot := cycAdj_mul10_slot (i2.val * uL + j2.val)
      (by have := mul_add_lt_mul i2.isLt j2.isLt; omega) wR h2
    have hdiv : wR.val / 10 = m * uL + 3 * (m * t) + d1.val := by
      rw [hd1]; dsimp [slotBrR]; omega
    have := mul_add_lt_mul i2.isLt j2.isLt; omega
  · obtain ⟨d1, hw1, hd1⟩ := h1; obtain ⟨d2, hw2, hd2⟩ := h2
    have hd := slotBrR_inj hsL (hd1.symm.trans hd2)
    subst hd; rw [hw1, hw2]

lemma dirAdj_noC4_left {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G)
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    {l1 l2 : LeftV m t (10 * q0)} (hne : l1 ≠ l2)
    {r1 r2 : RightV m t (10 * q0)}
    (h11 : dirAdj G eG hsL hsR l1 r1) (h21 : dirAdj G eG hsL hsR l2 r1)
    (h12 : dirAdj G eG hsL hsR l1 r2) (h22 : dirAdj G eG hsL hsR l2 r2) :
    r1 = r2 := by
  have hq : 10 ≤ 10 * q0 := by omega
  have hA0_out : ∀ (p : Fin m × Fin t) (r : RightV m t (10 * q0)),
      dirAdj G eG hsL hsR (Sum.inl p) r → isRightOutside hsR r := by
    intro ⟨i, p⟩ r hr
    rcases r with _ | _ | y
    · trivial
    · trivial
    · obtain ⟨k, hy, _⟩ := hr; exact ⟨i, k, hy⟩
  have hX1_out : ∀ (x : Fin (10 * q0)) (r : RightV m t (10 * q0)),
      dirAdj G eG hsL hsR (Sum.inr (Sum.inl x)) r → isRightOutside hsR r := by
    intro x r hr
    rcases r with _ | _ | y
    · trivial
    · trivial
    · exact False.elim hr
  have hG_from_A0 : ∀ (i : Fin m) (p1 p2 : Fin t) (hp : p1 ≠ p2)
      (r1 r2 : RightV m t (10 * q0)),
      dirAdj G eG hsL hsR (Sum.inl (i, p1)) r1 →
      dirAdj G eG hsL hsR (Sum.inl (i, p2)) r1 →
      dirAdj G eG hsL hsR (Sum.inl (i, p1)) r2 →
      dirAdj G eG hsL hsR (Sum.inl (i, p2)) r2 →
      r1 = r2 := by
    intro i p1 p2 hp r1 r2 ha1 hb1 ha2 hb2
    have hnotWR : ∀ wR, ¬(dirAdj G eG hsL hsR (Sum.inl (i, p1)) (Sum.inr (Sum.inl wR)) ∧
        dirAdj G eG hsL hsR (Sum.inl (i, p2)) (Sum.inr (Sum.inl wR))) := by
      rintro wR ⟨h1, h2⟩
      have heq := wR_unique_outside G eG hsL hsR wR _ _ h1 h2 trivial trivial
      exact hp (congrArg Prod.snd (Sum.inl.inj heq))
    have hneG : eG (Sum.inl (Sum.inl p1)) ≠ eG (Sum.inl (Sum.inl p2)) :=
      fun h => hp (Sum.inl.inj (Sum.inl.inj (eG.injective h)))
    rcases r1 with ⟨i1, q1⟩ | wR1 | y1 <;> rcases r2 with ⟨i2, q2⟩ | wR2 | y2
    · obtain ⟨rfl, hg11⟩ := ha1; obtain ⟨_, hg21⟩ := hb1
      obtain ⟨rfl, hg12⟩ := ha2; obtain ⟨_, hg22⟩ := hb2
      have hq := noFourCycle_unique hno4 hneG hg11 hg21 hg12 hg22
      have hq' : q1 = q2 := Sum.inl.inj (Sum.inr.inj (eG.injective hq))
      subst hq'; rfl
    · exact False.elim (hnotWR wR2 ⟨ha2, hb2⟩)
    · obtain ⟨rfl, hg11⟩ := ha1; obtain ⟨_, hg21⟩ := hb1
      obtain ⟨k2, rfl, hg12⟩ := ha2; obtain ⟨k2', hk2, hg22⟩ := hb2
      have hq := noFourCycle_unique hno4 hneG hg11 hg21 hg12 (by rw [(slotUR_inj hsR hk2).2]; exact hg22)
      have := Sum.inr.inj (eG.injective hq)
      exact absurd this (by simp)
    · exact False.elim (hnotWR wR1 ⟨ha1, hb1⟩)
    · exact False.elim (hnotWR wR1 ⟨ha1, hb1⟩)
    · exact False.elim (hnotWR wR1 ⟨ha1, hb1⟩)
    · obtain ⟨k1, rfl, hg11⟩ := ha1; obtain ⟨k1', hk1, hg21⟩ := hb1
      obtain ⟨rfl, hg12⟩ := ha2; obtain ⟨_, hg22⟩ := hb2
      have hq := noFourCycle_unique hno4 hneG hg11 (by rw [(slotUR_inj hsR hk1).2]; exact hg21) hg12 hg22
      have := Sum.inr.inj (eG.injective hq)
      exact absurd this (by simp)
    · exact False.elim (hnotWR wR2 ⟨ha2, hb2⟩)
    · obtain ⟨k1, rfl, hg11⟩ := ha1; obtain ⟨k1', hk1, hg21⟩ := hb1
      obtain ⟨k2, rfl, hg12⟩ := ha2; obtain ⟨k2', hk2, hg22⟩ := hb2
      have hq := noFourCycle_unique hno4 hneG hg11 (by rw [(slotUR_inj hsR hk1).2]; exact hg21)
        hg12 (by rw [(slotUR_inj hsR hk2).2]; exact hg22)
      have hk : k1 = k2 := Sum.inr.inj (Sum.inr.inj (eG.injective hq))
      subst hk; rfl
  rcases l1 with ⟨i1, p1⟩ | x1 | wL1 <;> rcases l2 with ⟨i2, p2⟩ | x2 | wL2
  · by_cases hi : i1 = i2
    · subst hi
      have hp : p1 ≠ p2 := fun h => hne (by subst h; rfl)
      exact hG_from_A0 i1 p1 p2 hp r1 r2 h11 h21 h12 h22
    · exfalso
      rcases r1 with ⟨ir, qr⟩ | wR1 | y1
      · exact hi (h11.1.trans h21.1.symm)
      · have heq := wR_unique_outside G eG hsL hsR wR1 _ _ h11 h21 trivial trivial
        exact hi (congrArg Prod.fst (Sum.inl.inj heq))
      · obtain ⟨k1, hy1, _⟩ := h11; obtain ⟨k2, hy2, _⟩ := h21
        exact hi (slotUR_inj hsR (hy1.symm.trans hy2)).1
  · by_cases hx2 : ∃ i j, x2 = slotUL hsL i j
    · obtain ⟨i2, j2, rfl⟩ := hx2
      have hnotWR : ∀ wR, ¬(dirAdj G eG hsL hsR (Sum.inl (i1, p1)) (Sum.inr (Sum.inl wR)) ∧
          dirAdj G eG hsL hsR (Sum.inr (Sum.inl (slotUL hsL i2 j2))) (Sum.inr (Sum.inl wR))) := by
        rintro wR ⟨ha, hb⟩
        have heq := wR_unique_outside G eG hsL hsR wR _ _ ha hb trivial ⟨i2, j2, rfl⟩
        exact absurd heq (by simp)
      rcases r1 with ⟨ir1, qr1⟩ | wR1 | y1 <;> rcases r2 with ⟨ir2, qr2⟩ | wR2 | y2
      · obtain ⟨rfl, hg11⟩ := h11; obtain ⟨j1', hj1, hg21⟩ := h21
        obtain ⟨rfl, hg12⟩ := h12; obtain ⟨j2', hj2, hg22⟩ := h22
        obtain ⟨_, hj1eq⟩ := slotUL_inj hsL hj1
        obtain ⟨_, hj2eq⟩ := slotUL_inj hsL hj2
        subst hj1eq; subst hj2eq
        have hneG : eG (Sum.inl (Sum.inl p1)) ≠ eG (Sum.inl (Sum.inr j2)) :=
          fun h => by have := Sum.inl.inj (eG.injective h); simp at this
        have hq := noFourCycle_unique hno4 hneG hg11 hg21 hg12 hg22
        have hq' : qr1 = qr2 := Sum.inl.inj (Sum.inr.inj (eG.injective hq))
        subst hq'; rfl
      · exact False.elim (hnotWR wR2 ⟨h12, h22⟩)
      · exact False.elim h22
      · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
      · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
      · exact False.elim h22
      · exact False.elim h21
      · exact False.elim h21
      · exact False.elim h21
    · have honlyWR : ∀ r, dirAdj G eG hsL hsR (Sum.inr (Sum.inl x2)) r →
          ∃ wR, r = Sum.inr (Sum.inl wR) ∧ cycAdj (10 * q0) x2 wR := by
        intro r hr
        rcases r with ⟨ir, qr⟩ | wR | y
        · obtain ⟨j, hj, _⟩ := hr; exact absurd ⟨ir, j, hj⟩ hx2
        · exact ⟨wR, rfl, hr⟩
        · exact False.elim hr
      obtain ⟨wR1, rfl, hc1⟩ := honlyWR r1 h21
      obtain ⟨wR2, rfl, hc2⟩ := honlyWR r2 h22
      obtain ⟨d1, hd1⟩ := h11; obtain ⟨d2, hd2⟩ := h12
      have hm1 : wR1.val % 10 = 0 := by rw [hd1]; dsimp [slotAttA]; omega
      have hm2 : wR2.val % 10 = 0 := by rw [hd2]; dsimp [slotAttA]; omega
      rw [cycAdj_hit_mul10 x2 wR1 wR2 hc1 hc2 hm1 hm2]
  · exact wL_unique_outside G eG hsL hsR wL2 r1 r2 h21 h22 (hA0_out _ r1 h11) (hA0_out _ r2 h12)
  · by_cases hx1 : ∃ i j, x1 = slotUL hsL i j
    · obtain ⟨i1, j1, rfl⟩ := hx1
      have hnotWR : ∀ wR, ¬(dirAdj G eG hsL hsR (Sum.inr (Sum.inl (slotUL hsL i1 j1))) (Sum.inr (Sum.inl wR)) ∧
          dirAdj G eG hsL hsR (Sum.inl (i2, p2)) (Sum.inr (Sum.inl wR))) := by
        rintro wR ⟨ha, hb⟩
        have heq := wR_unique_outside G eG hsL hsR wR _ _ ha hb ⟨i1, j1, rfl⟩ trivial
        exact absurd heq (by simp)
      rcases r1 with ⟨ir1, qr1⟩ | wR1 | y1 <;> rcases r2 with ⟨ir2, qr2⟩ | wR2 | y2
      · obtain ⟨j1', hj1, hg11⟩ := h11; obtain ⟨rfl, hg21⟩ := h21
        obtain ⟨j2', hj2, hg12⟩ := h12; obtain ⟨rfl, hg22⟩ := h22
        obtain ⟨_, hj1eq⟩ := slotUL_inj hsL hj1
        obtain ⟨_, hj2eq⟩ := slotUL_inj hsL hj2
        subst hj1eq; subst hj2eq
        have hneG : eG (Sum.inl (Sum.inr j1)) ≠ eG (Sum.inl (Sum.inl p2)) :=
          fun h => by have := Sum.inl.inj (eG.injective h); simp at this
        have hq := noFourCycle_unique hno4 hneG hg11 hg21 hg12 hg22
        have hq' : qr1 = qr2 := Sum.inl.inj (Sum.inr.inj (eG.injective hq))
        subst hq'; rfl
      · exact False.elim (hnotWR wR2 ⟨h12, h22⟩)
      · exact False.elim h12
      · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
      · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
      · exact False.elim h12
      · exact False.elim h11
      · exact False.elim h11
      · exact False.elim h11
    · have honlyWR : ∀ r, dirAdj G eG hsL hsR (Sum.inr (Sum.inl x1)) r →
          ∃ wR, r = Sum.inr (Sum.inl wR) ∧ cycAdj (10 * q0) x1 wR := by
        intro r hr
        rcases r with ⟨ir, qr⟩ | wR | y
        · obtain ⟨j, hj, _⟩ := hr; exact absurd ⟨ir, j, hj⟩ hx1
        · exact ⟨wR, rfl, hr⟩
        · exact False.elim hr
      obtain ⟨wR1, rfl, hc1⟩ := honlyWR r1 h11
      obtain ⟨wR2, rfl, hc2⟩ := honlyWR r2 h12
      obtain ⟨d1, hd1⟩ := h21; obtain ⟨d2, hd2⟩ := h22
      have hm1 : wR1.val % 10 = 0 := by rw [hd1]; dsimp [slotAttA]; omega
      have hm2 : wR2.val % 10 = 0 := by rw [hd2]; dsimp [slotAttA]; omega
      rw [cycAdj_hit_mul10 x1 wR1 wR2 hc1 hc2 hm1 hm2]
  · have hxne : x1 ≠ x2 := fun h => hne (by subst h; rfl)
    by_cases hboth : (∃ i j, x1 = slotUL hsL i j) ∧ (∃ i j, x2 = slotUL hsL i j)
    · obtain ⟨⟨i1, j1, rfl⟩, ⟨i2, j2, rfl⟩⟩ := hboth
      have hnotWR : ∀ wR, ¬(dirAdj G eG hsL hsR (Sum.inr (Sum.inl (slotUL hsL i1 j1))) (Sum.inr (Sum.inl wR)) ∧
          dirAdj G eG hsL hsR (Sum.inr (Sum.inl (slotUL hsL i2 j2))) (Sum.inr (Sum.inl wR))) := by
        rintro wR ⟨ha, hb⟩
        have heq := wR_unique_outside G eG hsL hsR wR _ _ ha hb ⟨i1, j1, rfl⟩ ⟨i2, j2, rfl⟩
        exact hne heq
      rcases r1 with ⟨ir1, qr1⟩ | wR1 | y1 <;> rcases r2 with ⟨ir2, qr2⟩ | wR2 | y2
      · obtain ⟨j1a, hj1a, hg11⟩ := h11; obtain ⟨j2a, hj2a, hg21⟩ := h21
        obtain ⟨j1b, hj1b, hg12⟩ := h12; obtain ⟨j2b, hj2b, hg22⟩ := h22
        obtain ⟨hi1a, hj1a'⟩ := slotUL_inj hsL hj1a
        obtain ⟨hi2a, hj2a'⟩ := slotUL_inj hsL hj2a
        obtain ⟨hi1b, hj1b'⟩ := slotUL_inj hsL hj1b
        obtain ⟨hi2b, hj2b'⟩ := slotUL_inj hsL hj2b
        subst hj1a'; subst hj2a'; subst hj1b'; subst hj2b'
        have hieq : ir1 = ir2 := hi1a.symm.trans hi1b
        have hi12 : i1 = i2 := hi1a.trans hi2a.symm
        subst hieq; subst hi1a; subst hi12
        have hjne : j1 ≠ j2 := fun h => hxne (by subst h; rfl)
        have hneG : eG (Sum.inl (Sum.inr j1)) ≠ eG (Sum.inl (Sum.inr j2)) :=
          fun h => hjne (Sum.inr.inj (Sum.inl.inj (eG.injective h)))
        have hq := noFourCycle_unique hno4 hneG hg11 hg21 hg12 hg22
        have hq' : qr1 = qr2 := Sum.inl.inj (Sum.inr.inj (eG.injective hq))
        subst hq'; rfl
      · exact False.elim (hnotWR wR2 ⟨h12, h22⟩)
      · exact False.elim h12
      · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
      · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
      · exact False.elim h12
      · exact False.elim h11
      · exact False.elim h11
      · exact False.elim h11
    · have hmustWR : ∀ r, dirAdj G eG hsL hsR (Sum.inr (Sum.inl x1)) r →
          dirAdj G eG hsL hsR (Sum.inr (Sum.inl x2)) r →
          ∃ wR, r = Sum.inr (Sum.inl wR) ∧ cycAdj (10 * q0) x1 wR ∧ cycAdj (10 * q0) x2 wR := by
        intro r ha hb
        rcases r with ⟨ir, qr⟩ | wR | y
        · obtain ⟨j1, hj1, _⟩ := ha; obtain ⟨j2, hj2, _⟩ := hb
          exact absurd ⟨⟨ir, j1, hj1⟩, ⟨ir, j2, hj2⟩⟩ hboth
        · exact ⟨wR, rfl, ha, hb⟩
        · exact False.elim ha
      obtain ⟨wR1, rfl, hc11, hc21⟩ := hmustWR r1 h11 h21
      obtain ⟨wR2, rfl, hc12, hc22⟩ := hmustWR r2 h12 h22
      rw [cycAdj_noC4_left hq x1 x2 hxne hc11 hc21 hc12 hc22]
  · exact wL_unique_outside G eG hsL hsR wL2 r1 r2 h21 h22 (hX1_out _ r1 h11) (hX1_out _ r2 h12)
  · exact wL_unique_outside G eG hsL hsR wL1 r1 r2 h11 h12 (hA0_out _ r1 h21) (hA0_out _ r2 h22)
  · exact wL_unique_outside G eG hsL hsR wL1 r1 r2 h11 h12 (hX1_out _ r1 h21) (hX1_out _ r2 h22)
  · have hwne : wL1 ≠ wL2 := fun h => hne (by subst h; rfl)
    have hnotWR : ∀ wR, ¬(dirAdj G eG hsL hsR (Sum.inr (Sum.inr wL1)) (Sum.inr (Sum.inl wR)) ∧
        dirAdj G eG hsL hsR (Sum.inr (Sum.inr wL2)) (Sum.inr (Sum.inl wR))) := by
      rintro wR ⟨⟨d1, hl1, hr1⟩, ⟨d2, hl2, hr2⟩⟩
      have hd := slotBrR_inj hsL (hr1.symm.trans hr2)
      subst hd; exact hwne (hl1.trans hl2.symm)
    rcases r1 with ⟨ir1, qr1⟩ | wR1 | y1 <;> rcases r2 with ⟨ir2, qr2⟩ | wR2 | y2
    · exact wL_unique_outside G eG hsL hsR wL1 _ _ h11 h12 trivial trivial
    · exact False.elim (hnotWR wR2 ⟨h12, h22⟩)
    · exfalso
      obtain ⟨d1, hd1⟩ := h11; obtain ⟨d2, hd2⟩ := h21
      have hm1 : wL1.val % 10 = 0 := by rw [hd1]; dsimp [slotAttB]; omega
      have hm2 : wL2.val % 10 = 0 := by rw [hd2]; dsimp [slotAttB]; omega
      exact hwne (cycAdj_hit_mul10 y2 wL1 wL2 h12 h22 hm1 hm2)
    · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
    · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
    · exact False.elim (hnotWR wR1 ⟨h11, h21⟩)
    · exfalso
      obtain ⟨d1, hd1⟩ := h12; obtain ⟨d2, hd2⟩ := h22
      have hm1 : wL1.val % 10 = 0 := by rw [hd1]; dsimp [slotAttB]; omega
      have hm2 : wL2.val % 10 = 0 := by rw [hd2]; dsimp [slotAttB]; omega
      exact hwne (cycAdj_hit_mul10 y1 wL1 wL2 h11 h21 hm1 hm2)
    · exact False.elim (hnotWR wR2 ⟨h12, h22⟩)
    · rw [cycAdj_noC4_right hq wL1 wL2 hwne h11 h21 h12 h22]

lemma dirAdj_noC4_right {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G)
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    {r1 r2 : RightV m t (10 * q0)} (hne : r1 ≠ r2)
    {l1 l2 : LeftV m t (10 * q0)}
    (h11 : dirAdj G eG hsL hsR l1 r1) (h12 : dirAdj G eG hsL hsR l1 r2)
    (h21 : dirAdj G eG hsL hsR l2 r1) (h22 : dirAdj G eG hsL hsR l2 r2) :
    l1 = l2 := by
  by_contra hlne
  exact hne (dirAdj_noC4_left G hno4 eG hq0 hsL hsR hlne h11 h21 h12 h22)

lemma ampGraph0_noFourCycle {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno4 : NoFourCycle G)
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    {a b w1 w2 : AmpV m t (10 * q0)} (hne : a ≠ b)
    (h1a : (ampGraph0 G eG hsL hsR).Adj a w1) (h1b : (ampGraph0 G eG hsL hsR).Adj b w1)
    (h2a : (ampGraph0 G eG hsL hsR).Adj a w2) (h2b : (ampGraph0 G eG hsL hsR).Adj b w2) :
    w1 = w2 := by
  rcases a with l1 | r1 <;> rcases b with l2 | r2 <;>
    rcases w1 with wl1 | wr1 <;> rcases w2 with wl2 | wr2
  all_goals first
    | exact False.elim h1a
    | exact False.elim h1b
    | exact False.elim h2a
    | (have hlne : l1 ≠ l2 := fun h => hne (by subst h; rfl)
       exact congrArg Sum.inr (dirAdj_noC4_left G hno4 eG hq0 hsL hsR hlne h1a h1b h2a h2b))
    | (have hrne : r1 ≠ r2 := fun h => hne (by subst h; rfl)
       exact congrArg Sum.inl (dirAdj_noC4_right G hno4 eG hq0 hsL hsR hrne h1a h1b h2a h2b))

lemma ampGraph0_threeConn {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (S : Finset (AmpV m t (10 * q0))) (hS : S.card ≤ 2) :
    ((ampGraph0 G eG hsL hsR).induce (↑S : Set (AmpV m t (10 * q0)))ᶜ).Connected := by
  classical
  let q := 10 * q0
  have hq : 10 ≤ q := by omega
  let H := (ampGraph0 G eG hsL hsR).induce (↑S : Set (AmpV m t q))ᶜ
  let embB1 : Fin q ⊕ Fin q → AmpV m t q
    | Sum.inl x => vX1 x
    | Sum.inr w => vWR w
  let embB2 : Fin q ⊕ Fin q → AmpV m t q
    | Sum.inl y => vY2 y
    | Sum.inr w => vWL w
  have hembB1_inj : Function.Injective embB1 := by
    rintro (x1 | w1) (x2 | w2) h <;> simp [embB1, vX1, vWR] at h <;> simp [h]
  have hembB2_inj : Function.Injective embB2 := by
    rintro (y1 | w1) (y2 | w2) h <;> simp [embB2, vY2, vWL] at h <;> simp [h]
  let S1 : Finset (Fin q ⊕ Fin q) := S.preimage embB1 (fun _ _ _ _ h => hembB1_inj h)
  let S2 : Finset (Fin q ⊕ Fin q) := S.preimage embB2 (fun _ _ _ _ h => hembB2_inj h)
  have hS1 : S1.card ≤ 2 := by
    have himg : S1.image embB1 ⊆ S := fun z hz => by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz; exact Finset.mem_preimage.mp hp
    have := (Finset.card_image_of_injective S1 hembB1_inj).symm.le.trans (Finset.card_le_card himg)
    omega
  have hS2 : S2.card ≤ 2 := by
    have himg : S2.image embB2 ⊆ S := fun z hz => by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz; exact Finset.mem_preimage.mp hp
    have := (Finset.card_image_of_injective S2 hembB2_inj).symm.le.trans (Finset.card_le_card himg)
    omega
  have hC1 := cycGraph_threeConn hq S1 hS1
  have hC2 := cycGraph_threeConn hq S2 hS2
  have hlift1 : ∀ (a b : Fin q ⊕ Fin q) (ha : embB1 a ∉ S) (hb : embB1 b ∉ S),
      H.Reachable ⟨embB1 a, ha⟩ ⟨embB1 b, hb⟩ := by
    intro a b ha hb
    have ha1 : a ∉ S1 := fun h => ha (Finset.mem_preimage.mp h)
    have hb1 : b ∉ S1 := fun h => hb (Finset.mem_preimage.mp h)
    let f1 : ((cycGraph q).induce (↑S1 : Set (Fin q ⊕ Fin q))ᶜ) →g H := {
      toFun := fun u => ⟨embB1 u.1, fun h => u.2 (Finset.mem_preimage.mpr (by simpa using h))⟩
      map_rel' := by
        rintro ⟨u, _⟩ ⟨v, _⟩ huv
        change (ampGraph0 G eG hsL hsR).Adj (embB1 u) (embB1 v)
        rcases u with x1 | w1 <;> rcases v with x2 | w2 <;> exact huv
    }
    exact (hC1.preconnected ⟨a, ha1⟩ ⟨b, hb1⟩).map f1
  have hlift2 : ∀ (a b : Fin q ⊕ Fin q) (ha : embB2 a ∉ S) (hb : embB2 b ∉ S),
      H.Reachable ⟨embB2 a, ha⟩ ⟨embB2 b, hb⟩ := by
    intro a b ha hb
    have ha2 : a ∉ S2 := fun h => ha (Finset.mem_preimage.mp h)
    have hb2 : b ∉ S2 := fun h => hb (Finset.mem_preimage.mp h)
    let f2 : ((cycGraph q).induce (↑S2 : Set (Fin q ⊕ Fin q))ᶜ) →g H := {
      toFun := fun u => ⟨embB2 u.1, fun h => u.2 (Finset.mem_preimage.mpr (by simpa using h))⟩
      map_rel' := by
        rintro ⟨u, _⟩ ⟨v, _⟩ huv
        change (ampGraph0 G eG hsL hsR).Adj (embB2 u) (embB2 v)
        rcases u with y1 | w1 <;> rcases v with y2 | w2 <;> exact huv
    }
    exact (hC2.preconnected ⟨a, ha2⟩ ⟨b, hb2⟩).map f2
  obtain ⟨d0, hd0L, hd0R⟩ : ∃ d : Fin 3, vWL (slotBrL hsR d) ∉ S ∧ vWR (slotBrR hsL d) ∉ S := by
    by_contra! hall
    have hcard : ∀ d : Fin 3, 1 ≤ ({vWL (slotBrL hsR d), vWR (slotBrR hsL d)} ∩ S).card := by
      intro d
      by_cases hL : vWL (slotBrL hsR d) ∈ S
      · exact Finset.card_pos.mpr ⟨vWL (slotBrL hsR d), Finset.mem_inter.mpr ⟨by simp, hL⟩⟩
      · have hR := hall d hL
        exact Finset.card_pos.mpr ⟨vWR (slotBrR hsL d), Finset.mem_inter.mpr ⟨by simp, hR⟩⟩
    let P (d : Fin 3) : Finset (AmpV m t q) := {vWL (slotBrL hsR d), vWR (slotBrR hsL d)} ∩ S
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 3)) P := by
      intro d1 _ d2 _ hne
      show Disjoint (P d1) (P d2)
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have h1 := (Finset.mem_inter.mp hz1).1
      have h2 := (Finset.mem_inter.mp hz2).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with h | h
      · exact hne (slotBrL_inj hsR (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj h))))
      · simp [vWL, vWR] at h
      · simp [vWL, vWR] at h
      · exact hne (slotBrR_inj hsL (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))))
    have hsub : Finset.univ.biUnion P ⊆ S := by
      intro z hz; obtain ⟨_, _, hzP⟩ := Finset.mem_biUnion.mp hz; exact (Finset.mem_inter.mp hzP).2
    have hsum : 3 ≤ S.card := by
      calc 3 = ∑ _d : Fin 3, 1 := by decide
        _ ≤ ∑ d : Fin 3, (P d).card := Finset.sum_le_sum fun d _ => hcard d
        _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion hdisj).symm
        _ ≤ S.card := Finset.card_le_card hsub
    omega
  let baseR : ((↑S : Set (AmpV m t q))ᶜ : Set (AmpV m t q)) := ⟨vWR (slotBrR hsL d0), hd0R⟩
  let baseL : ((↑S : Set (AmpV m t q))ᶜ : Set (AmpV m t q)) := ⟨vWL (slotBrL hsR d0), hd0L⟩
  have hbridge : H.Reachable baseL baseR := by
    have hadj : H.Adj baseL baseR :=
      show dirAdj G eG hsL hsR (Sum.inr (Sum.inr (slotBrL hsR d0)))
        (Sum.inr (Sum.inl (slotBrR hsL d0))) from ⟨d0, rfl, rfl⟩
    exact hadj.reachable
  have hreach_all : ∀ u : ((↑S : Set (AmpV m t q))ᶜ : Set (AmpV m t q)),
      H.Reachable baseR u := by
    intro ⟨u, hu⟩
    have huS : u ∉ S := hu
    rcases u with (⟨i, r⟩ | x | wL) | (⟨i, r⟩ | wR | y)
    · -- A0: 3 distinct WR neighbors -> at least one not in S
      obtain ⟨d, hd⟩ : ∃ d : Fin 3, vWR (slotAttA hsL i r d) ∉ S := by
        by_contra! hall
        let f : Fin 3 → AmpV m t q := fun d => vWR (slotAttA hsL i r d)
        have hfinj : Function.Injective f := fun d1 d2 h =>
          (slotAttA_inj hsL (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h)))).2.2
        have hsub : Finset.univ.image f ⊆ S := fun z hz => by
          obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz; exact hall d
        have h3 : 3 ≤ S.card := by
          calc 3 = (Finset.univ.image f).card := by
                rw [Finset.card_image_of_injective _ hfinj]; simp
            _ ≤ S.card := Finset.card_le_card hsub
        omega
      have hr1 : H.Reachable baseR ⟨vWR (slotAttA hsL i r d), hd⟩ :=
        hlift1 (Sum.inr (slotBrR hsL d0)) (Sum.inr (slotAttA hsL i r d)) hd0R hd
      have hadj : H.Adj ⟨vWR (slotAttA hsL i r d), hd⟩ ⟨vA0 i r, hu⟩ :=
        show dirAdj G eG hsL hsR (Sum.inl (i, r)) (Sum.inr (Sum.inl (slotAttA hsL i r d))) from ⟨d, rfl⟩
      exact hr1.trans hadj.reachable
    · exact hlift1 (Sum.inr (slotBrR hsL d0)) (Sum.inl x) hd0R huS
    · exact hbridge.symm.trans (hlift2 (Sum.inr (slotBrL hsR d0)) (Sum.inr wL) hd0L huS)
    · -- B0: 3 distinct WL neighbors -> at least one not in S
      obtain ⟨d, hd⟩ : ∃ d : Fin 3, vWL (slotAttB hsR i r d) ∉ S := by
        by_contra! hall
        let f : Fin 3 → AmpV m t q := fun d => vWL (slotAttB hsR i r d)
        have hfinj : Function.Injective f := fun d1 d2 h =>
          (slotAttB_inj hsR (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj h)))).2.2
        have hsub : Finset.univ.image f ⊆ S := fun z hz => by
          obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz; exact hall d
        have h3 : 3 ≤ S.card := by
          calc 3 = (Finset.univ.image f).card := by
                rw [Finset.card_image_of_injective _ hfinj]; simp
            _ ≤ S.card := Finset.card_le_card hsub
        omega
      have hr1 : H.Reachable baseL ⟨vWL (slotAttB hsR i r d), hd⟩ :=
        hlift2 (Sum.inr (slotBrL hsR d0)) (Sum.inr (slotAttB hsR i r d)) hd0L hd
      have hadj : H.Adj ⟨vWL (slotAttB hsR i r d), hd⟩ ⟨vB0 i r, hu⟩ :=
        show dirAdj G eG hsL hsR (Sum.inr (Sum.inr (slotAttB hsR i r d))) (Sum.inl (i, r)) from ⟨d, rfl⟩
      exact hbridge.symm.trans (hr1.trans hadj.reachable)
    · exact hlift1 (Sum.inr (slotBrR hsL d0)) (Sum.inr wR) hd0R huS
    · exact hbridge.symm.trans (hlift2 (Sum.inr (slotBrL hsR d0)) (Sum.inl y) hd0L huS)
  have : Nonempty ((↑S : Set (AmpV m t q))ᶜ : Set (AmpV m t q)) := ⟨baseR⟩
  exact ⟨fun u v => (hreach_all u).symm.trans (hreach_all v)⟩

lemma edgeFinset_card_bipartite {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (K : SimpleGraph (α ⊕ β)) [DecidableRel K.Adj]
    (hL : ∀ a1 a2 : α, ¬K.Adj (Sum.inl a1) (Sum.inl a2))
    (hR : ∀ b1 b2 : β, ¬K.Adj (Sum.inr b1) (Sum.inr b2)) :
    K.edgeFinset.card = (Finset.univ.filter fun p : α × β => K.Adj (Sum.inl p.1) (Sum.inr p.2)).card := by
  classical
  let P := Finset.univ.filter fun p : α × β => K.Adj (Sum.inl p.1) (Sum.inr p.2)
  let f : α × β → Sym2 (α ⊕ β) := fun p => s(Sum.inl p.1, Sum.inr p.2)
  have hfinj : Function.Injective f := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [f, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, or_false] at h
    exact Prod.ext h.1 h.2
  have himg : P.image f = K.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_image, P, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, f]
      constructor
      · rintro ⟨⟨a, b⟩, hab, heq⟩
        rw [← SimpleGraph.mem_edgeSet, ← heq]; exact hab
      · intro huv
        rcases u with a | b <;> rcases v with a' | b'
        · exact False.elim (hL a a' huv)
        · exact ⟨⟨a, b'⟩, huv, rfl⟩
        · exact ⟨⟨a', b⟩, huv.symm, Sym2.eq_swap⟩
        · exact False.elim (hR b b' huv)
  rw [← himg, Finset.card_image_of_injective P hfinj]

lemma ampGraph0_edgeCard {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hL : ∀ x y : Fin t ⊕ Fin uL, ¬G.Adj (eG (Sum.inl x)) (eG (Sum.inl y)))
    (hR : ∀ x y : Fin t ⊕ Fin uR, ¬G.Adj (eG (Sum.inr x)) (eG (Sum.inr y)))
    (hnoU : ∀ (j : Fin uL) (k : Fin uR),
      ¬G.Adj (eG (Sum.inl (Sum.inr j))) (eG (Sum.inr (Sum.inr k))))
    (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0) :
    letI : DecidableRel (ampGraph0 G eG hsL hsR).Adj := Classical.decRel _
    (ampGraph0 G eG hsL hsR).edgeFinset.card =
      m * G.edgeFinset.card + 6 * (10 * q0) + 6 * (m * t) + 3 := by
  classical
  let q := 10 * q0
  have hq : 10 ≤ q := by omega
  let H0 := ampGraph0 G eG hsL hsR
  rw [edgeFinset_card_bipartite H0 (fun _ _ h => h) (fun _ _ h => h)]
  let G' : SimpleGraph ((Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR)) := SimpleGraph.comap eG G
  have hGcard : G.edgeFinset.card =
      (Finset.univ.filter fun p : (Fin t ⊕ Fin uL) × (Fin t ⊕ Fin uR) =>
        G.Adj (eG (Sum.inl p.1)) (eG (Sum.inr p.2))).card := by
    have he1 : G.edgeFinset.card = G'.edgeFinset.card := by
      have h1 : G'.edgeFinset.image (Sym2.map eG) = G.edgeFinset := by
        ext e
        induction e using Sym2.ind with
        | _ u v =>
          simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          constructor
          · rintro ⟨e', he', heq⟩
            induction e' using Sym2.ind with
            | _ a b =>
              change s(eG a, eG b) = s(u, v) at heq
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact he'
              · exact he'.symm
          · intro huv
            refine ⟨s(eG.symm u, eG.symm v), ?_, ?_⟩
            · simp [G', huv]
            · simp
      rw [← h1, Finset.card_image_of_injective _ (Sym2.map.injective eG.injective)]
    rw [he1, edgeFinset_card_bipartite G' hL hR]
    rfl
  let Eall : Finset (LeftV m t q × RightV m t q) :=
    Finset.univ.filter fun p => dirAdj G eG hsL hsR p.1 p.2
  let E1 : Finset (LeftV m t q × RightV m t q) :=
    Eall.filter fun p =>
      match p with
      | (Sum.inl _, Sum.inl _) => True
      | (Sum.inl _, Sum.inr (Sum.inr _)) => True
      | (Sum.inr (Sum.inl _), Sum.inl _) => True
      | _ => False
  let E2 : Finset (LeftV m t q × RightV m t q) :=
    Eall.filter fun p => match p with | (Sum.inl _, Sum.inr (Sum.inl _)) => True | _ => False
  let E3 : Finset (LeftV m t q × RightV m t q) :=
    Eall.filter fun p => match p with | (Sum.inr (Sum.inl _), Sum.inr (Sum.inl _)) => True | _ => False
  let E4 : Finset (LeftV m t q × RightV m t q) :=
    Eall.filter fun p => match p with | (Sum.inr (Sum.inr _), Sum.inl _) => True | _ => False
  let E5 : Finset (LeftV m t q × RightV m t q) :=
    Eall.filter fun p => match p with | (Sum.inr (Sum.inr _), Sum.inr (Sum.inl _)) => True | _ => False
  let E6 : Finset (LeftV m t q × RightV m t q) :=
    Eall.filter fun p => match p with | (Sum.inr (Sum.inr _), Sum.inr (Sum.inr _)) => True | _ => False
  let GP := Finset.univ.filter fun p : (Fin t ⊕ Fin uL) × (Fin t ⊕ Fin uR) =>
    G.Adj (eG (Sum.inl p.1)) (eG (Sum.inr p.2))
  have hE1 : E1.card = m * G.edgeFinset.card := by
    rw [hGcard]
    let f1 : Fin m × ((Fin t ⊕ Fin uL) × (Fin t ⊕ Fin uR)) → LeftV m t q × RightV m t q :=
      fun ⟨i, a, b⟩ =>
        (match a with | Sum.inl r => Sum.inl (i, r) | Sum.inr j => Sum.inr (Sum.inl (slotUL hsL i j)),
         match b with | Sum.inl r => Sum.inl (i, r) | Sum.inr k => Sum.inr (Sum.inr (slotUR hsR i k)))
    have hf1_inj : ∀ p1 ∈ (Finset.univ : Finset (Fin m)) ×ˢ GP,
        ∀ p2 ∈ (Finset.univ : Finset (Fin m)) ×ˢ GP, f1 p1 = f1 p2 → p1 = p2 := by
      rintro ⟨i1, a1, b1⟩ _ ⟨i2, a2, b2⟩ _ heq
      have hl := congrArg Prod.fst heq
      have hr := congrArg Prod.snd heq
      rcases a1 with r1 | j1 <;> rcases a2 with r2 | j2 <;>
        rcases b1 with s1 | k1 <;> rcases b2 with s2 | k2
      all_goals simp [f1] at hl hr
      · rcases hl with ⟨rfl, rfl⟩; rcases hr with ⟨_, rfl⟩; rfl
      · rcases hl with ⟨rfl, rfl⟩; obtain ⟨_, rfl⟩ := slotUR_inj hsR hr; rfl
      · obtain ⟨rfl, rfl⟩ := slotUL_inj hsL hl; rcases hr with ⟨_, rfl⟩; rfl
      · obtain ⟨rfl, rfl⟩ := slotUL_inj hsL hl; obtain ⟨_, rfl⟩ := slotUR_inj hsR hr; rfl
    have hf1_img : ((Finset.univ : Finset (Fin m)) ×ˢ GP).image f1 = E1 := by
      ext ⟨l, r⟩
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
        GP, E1, Eall, Finset.mem_filter]
      constructor
      · rintro ⟨⟨i, a, b⟩, hab, heq⟩
        cases heq
        rcases a with r1 | j1 <;> rcases b with s1 | k1
        · exact ⟨⟨rfl, hab⟩, trivial⟩
        · exact ⟨⟨k1, rfl, hab⟩, trivial⟩
        · exact ⟨⟨j1, rfl, hab⟩, trivial⟩
        · exact False.elim (hnoU j1 k1 hab)
      · rintro ⟨hadj, hblk⟩
        rcases l with ⟨i1, r1⟩ | x1 | wL1 <;> rcases r with ⟨i2, s2⟩ | wR2 | y2
        · obtain ⟨rfl, hg⟩ := hadj; exact ⟨⟨i1, Sum.inl r1, Sum.inl s2⟩, hg, rfl⟩
        · exact False.elim hblk
        · obtain ⟨k, rfl, hg⟩ := hadj; exact ⟨⟨i1, Sum.inl r1, Sum.inr k⟩, hg, rfl⟩
        · obtain ⟨j, rfl, hg⟩ := hadj; exact ⟨⟨i2, Sum.inr j, Sum.inl s2⟩, hg, rfl⟩
        · exact False.elim hblk
        · exact False.elim hadj
        · exact False.elim hblk
        · exact False.elim hblk
        · exact False.elim hblk
    rw [← hf1_img, Finset.card_image_of_injOn (fun x hx y hy h => hf1_inj x hx y hy h),
        Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hE2 : E2.card = 3 * (m * t) := by
    let f2 : (Fin m × Fin t) × Fin 3 → LeftV m t q × RightV m t q :=
      fun ⟨⟨i, r⟩, d⟩ => (Sum.inl (i, r), Sum.inr (Sum.inl (slotAttA hsL i r d)))
    have hf2_inj : Function.Injective f2 := by
      rintro ⟨⟨i1, r1⟩, d1⟩ ⟨⟨i2, r2⟩, d2⟩ h
      simp only [f2, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h
      obtain ⟨_, _, hd⟩ := slotAttA_inj hsL h.2
      rw [h.1.1, h.1.2, hd]
    have hf2_img : Finset.univ.image f2 = E2 := by
      ext ⟨l, r⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, E2, Eall, Finset.mem_filter, f2]
      constructor
      · rintro ⟨⟨⟨i, p⟩, d⟩, heq⟩; cases heq; exact ⟨⟨d, rfl⟩, trivial⟩
      · rintro ⟨hadj, hblk⟩
        rcases l with ⟨i, p⟩ | x | wL <;> rcases r with ⟨i', p'⟩ | wR | y
        all_goals first | exact False.elim hblk | (obtain ⟨d, rfl⟩ := hadj; exact ⟨⟨⟨i, p⟩, d⟩, rfl⟩)
    rw [← hf2_img, Finset.card_image_of_injective _ hf2_inj, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]; ring
  have hE3 : E3.card = 3 * q := by
    let S3 := Finset.univ.filter fun p : Fin q × Fin q => cycAdj q p.1 p.2
    let f3 : Fin q × Fin q → LeftV m t q × RightV m t q :=
      fun p => (Sum.inr (Sum.inl p.1), Sum.inr (Sum.inl p.2))
    have hf3_inj : Function.Injective f3 := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      simp only [f3, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq] at h
      exact Prod.ext h.1 h.2
    have hf3_img : S3.image f3 = E3 := by
      ext ⟨l, r⟩
      simp only [Finset.mem_image, S3, E3, Eall, Finset.mem_filter, Finset.mem_univ, true_and, f3]
      constructor
      · rintro ⟨⟨a, b⟩, hab, heq⟩; cases heq; exact ⟨hab, trivial⟩
      · rintro ⟨hadj, hblk⟩
        rcases l with ⟨i, p⟩ | x | wL <;> rcases r with ⟨i', p'⟩ | wR | y
        all_goals first | exact False.elim hblk | exact ⟨⟨x, wR⟩, hadj, rfl⟩
    rw [← hf3_img, Finset.card_image_of_injective _ hf3_inj]
    have hS3 : S3 = Finset.univ.biUnion fun a : Fin q =>
        (Finset.univ.filter fun b : Fin q => cycAdj q a b).image fun b => (a, b) := by
      ext ⟨a, b⟩
      simp [S3]
    rw [hS3, Finset.card_biUnion]
    · trans ∑ _a : Fin q, 3
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
        exact cycAdj_right_neighbors hq a
      · simp [Nat.mul_comm]
    · intro a1 _ a2 _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hz1
      obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hz2
      exact hne (congrArg Prod.fst h2).symm
  have hE4 : E4.card = 3 * (m * t) := by
    let f4 : (Fin m × Fin t) × Fin 3 → LeftV m t q × RightV m t q :=
      fun ⟨⟨i, r⟩, d⟩ => (Sum.inr (Sum.inr (slotAttB hsR i r d)), Sum.inl (i, r))
    have hf4_inj : Function.Injective f4 := by
      rintro ⟨⟨i1, r1⟩, d1⟩ ⟨⟨i2, r2⟩, d2⟩ h
      simp only [f4, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h
      obtain ⟨_, _, hd⟩ := slotAttB_inj hsR h.1
      rw [h.2.1, h.2.2, hd]
    have hf4_img : Finset.univ.image f4 = E4 := by
      ext ⟨l, r⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, E4, Eall, Finset.mem_filter, f4]
      constructor
      · rintro ⟨⟨⟨i, p⟩, d⟩, heq⟩; cases heq; exact ⟨⟨d, rfl⟩, trivial⟩
      · rintro ⟨hadj, hblk⟩
        rcases l with ⟨i, p⟩ | x | wL <;> rcases r with ⟨i', p'⟩ | wR | y
        all_goals first | exact False.elim hblk | (obtain ⟨d, rfl⟩ := hadj; exact ⟨⟨⟨i', p'⟩, d⟩, rfl⟩)
    rw [← hf4_img, Finset.card_image_of_injective _ hf4_inj, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]; ring
  have hE5 : E5.card = 3 := by
    let f5 : Fin 3 → LeftV m t q × RightV m t q :=
      fun d => (Sum.inr (Sum.inr (slotBrL hsR d)), Sum.inr (Sum.inl (slotBrR hsL d)))
    have hf5_inj : Function.Injective f5 := by
      intro d1 d2 h
      simp only [f5, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq] at h
      exact slotBrL_inj hsR h.1
    have hf5_img : Finset.univ.image f5 = E5 := by
      ext ⟨l, r⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, E5, Eall, Finset.mem_filter, f5]
      constructor
      · rintro ⟨d, heq⟩; cases heq; exact ⟨⟨d, rfl, rfl⟩, trivial⟩
      · rintro ⟨hadj, hblk⟩
        rcases l with ⟨i, p⟩ | x | wL <;> rcases r with ⟨i', p'⟩ | wR | y
        all_goals first | exact False.elim hblk | (obtain ⟨d, rfl, rfl⟩ := hadj; exact ⟨d, rfl⟩)
    rw [← hf5_img, Finset.card_image_of_injective _ hf5_inj, Finset.card_univ, Fintype.card_fin]
  have hE6 : E6.card = 3 * q := by
    let S6 := Finset.univ.filter fun p : Fin q × Fin q => cycAdj q p.1 p.2
    let f6 : Fin q × Fin q → LeftV m t q × RightV m t q :=
      fun p => (Sum.inr (Sum.inr p.2), Sum.inr (Sum.inr p.1))
    have hf6_inj : Function.Injective f6 := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      simp only [f6, Prod.mk.injEq, Sum.inr.injEq] at h
      exact Prod.ext h.2 h.1
    have hf6_img : S6.image f6 = E6 := by
      ext ⟨l, r⟩
      simp only [Finset.mem_image, S6, E6, Eall, Finset.mem_filter, Finset.mem_univ, true_and, f6]
      constructor
      · rintro ⟨⟨a, b⟩, hab, heq⟩; cases heq; exact ⟨hab, trivial⟩
      · rintro ⟨hadj, hblk⟩
        rcases l with ⟨i, p⟩ | x | wL <;> rcases r with ⟨i', p'⟩ | wR | y
        all_goals first | exact False.elim hblk | exact ⟨⟨y, wL⟩, hadj, rfl⟩
    rw [← hf6_img, Finset.card_image_of_injective _ hf6_inj]
    have hS6 : S6 = Finset.univ.biUnion fun a : Fin q =>
        (Finset.univ.filter fun b : Fin q => cycAdj q a b).image fun b => (a, b) := by
      ext ⟨a, b⟩
      simp [S6]
    rw [hS6, Finset.card_biUnion]
    · trans ∑ _a : Fin q, 3
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
        exact cycAdj_right_neighbors hq a
      · simp [Nat.mul_comm]
    · intro a1 _ a2 _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hz1
      obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hz2
      exact hne (congrArg Prod.fst h2).symm
  have hunion : Eall = E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ E6 := by
    ext ⟨l, r⟩
    simp only [E1, E2, E3, E4, E5, E6, Eall, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rcases l with ⟨i, p⟩ | x | wL <;> rcases r with ⟨i', p'⟩ | wR | y <;> simp [dirAdj]
  have hd12 : Disjoint E1 E2 := Finset.disjoint_left.mpr fun ⟨l, r⟩ h1 h2 => by
    simp only [E1, E2, Finset.mem_filter] at h1 h2
    rcases l with _ | _ | _ <;> rcases r with _ | _ | _ <;> simp at h1 h2
  have hd123 : Disjoint (E1 ∪ E2) E3 := Finset.disjoint_left.mpr fun ⟨l, r⟩ h1 h2 => by
    simp only [E1, E2, E3, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases l with _ | _ | _ <;> rcases r with _ | _ | _ <;> simp at h1 h2
  have hd1234 : Disjoint (E1 ∪ E2 ∪ E3) E4 := Finset.disjoint_left.mpr fun ⟨l, r⟩ h1 h2 => by
    simp only [E1, E2, E3, E4, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases l with _ | _ | _ <;> rcases r with _ | _ | _ <;> simp at h1 h2
  have hd12345 : Disjoint (E1 ∪ E2 ∪ E3 ∪ E4) E5 := Finset.disjoint_left.mpr fun ⟨l, r⟩ h1 h2 => by
    simp only [E1, E2, E3, E4, E5, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases l with _ | _ | _ <;> rcases r with _ | _ | _ <;> simp at h1 h2
  have hd123456 : Disjoint (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5) E6 := Finset.disjoint_left.mpr fun ⟨l, r⟩ h1 h2 => by
    simp only [E1, E2, E3, E4, E5, E6, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases l with _ | _ | _ <;> rcases r with _ | _ | _ <;> simp at h1 h2
  change Eall.card = m * G.edgeFinset.card + 6 * q + 6 * (m * t) + 3
  rw [hunion, Finset.card_union_of_disjoint hd123456, Finset.card_union_of_disjoint hd12345,
      Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
      Finset.card_union_of_disjoint hd12, hE1, hE2, hE3, hE4, hE5, hE6]
  omega

/-! ### Section 5: Explicit star lists and final circuit assembly -/

def nbrsWR {m t uL uR q0 : ℕ} (ht : 1 ≤ t) (hq0 : 1 ≤ q0)
    (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (wR : Fin (10 * q0)) : List (AmpV m t (10 * q0)) :=
  let q := 10 * q0
  [vX1 wR,
   vX1 ⟨(wR.val + q - 1) % q, Nat.mod_lt _ (by omega)⟩,
   vX1 ⟨(wR.val + q - 3) % q, Nat.mod_lt _ (by omega)⟩] ++
  (if h1 : wR.val % 10 = 0 ∧ m * uL ≤ wR.val / 10 ∧ wR.val / 10 < m * uL + 3 * (m * t) then
    let idx := (wR.val / 10 - m * uL) / 3
    have hidx : idx < m * t := by omega
    [vA0 ⟨idx / t, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)⟩
         ⟨idx % t, Nat.mod_lt _ (by omega)⟩]
   else []) ++
  (if h2 : wR.val % 10 = 0 ∧ m * uL + 3 * (m * t) ≤ wR.val / 10 ∧ wR.val / 10 < m * uL + 3 * (m * t) + 3 then
    let d : Fin 3 := ⟨wR.val / 10 - (m * uL + 3 * (m * t)), by omega⟩
    [vWL (slotBrL hsR d)]
   else [])

def nbrsWL {m t uR q0 : ℕ} (ht : 1 ≤ t) (hq0 : 1 ≤ q0)
    (wL : Fin (10 * q0)) : List (AmpV m t (10 * q0)) :=
  let q := 10 * q0
  [vY2 wL,
   vY2 ⟨(wL.val + q - 1) % q, Nat.mod_lt _ (by omega)⟩,
   vY2 ⟨(wL.val + q - 3) % q, Nat.mod_lt _ (by omega)⟩] ++
  (if h1 : wL.val % 10 = 0 ∧ m * uR ≤ wL.val / 10 ∧ wL.val / 10 < m * uR + 3 * (m * t) then
    let idx := (wL.val / 10 - m * uR) / 3
    have hidx : idx < m * t := by omega
    [vB0 ⟨idx / t, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)⟩
         ⟨idx % t, Nat.mod_lt _ (by omega)⟩]
   else [])

lemma cycAdj_iff_sub {q : ℕ} (hq : 10 ≤ q) (a b : Fin q) :
    cycAdj q a b ↔
      a = b ∨
      a = ⟨(b.val + q - 1) % q, Nat.mod_lt _ (by omega)⟩ ∨
      a = ⟨(b.val + q - 3) % q, Nat.mod_lt _ (by omega)⟩ := by
  constructor
  · rintro (h | h | h)
    · left; exact Fin.ext h.symm
    · right; left; apply Fin.ext; dsimp
      have ha : (1 + a.val) % q = (1 + (b.val + q - 1) % q) % q := by
        rw [Nat.add_comm 1 a.val, ← h, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show 1 + (b.val + q - 1) = b.val + q * 1 by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
      exact mod_add_left_cancel a.isLt (Nat.mod_lt _ (by omega)) ha
    · right; right; apply Fin.ext; dsimp
      have ha : (3 + a.val) % q = (3 + (b.val + q - 3) % q) % q := by
        rw [Nat.add_comm 3 a.val, ← h, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show 3 + (b.val + q - 3) = b.val + q * 1 by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
      exact mod_add_left_cancel a.isLt (Nat.mod_lt _ (by omega)) ha
  · rintro (rfl | rfl | rfl)
    · left; rfl
    · right; left; dsimp
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show b.val + q - 1 + 1 = b.val + q * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    · right; right; dsimp
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show b.val + q - 3 + 3 = b.val + q * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]

lemma mem_nbrsWR_iff {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (ht : 1 ≤ t) (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (wR : Fin (10 * q0)) (u : AmpV m t (10 * q0)) :
    u ∈ nbrsWR (m := m) (uL := uL) ht hq0 hsR wR ↔
      (ampGraph0 G eG hsL hsR).Adj u (vWR wR) := by
  have hq : 10 ≤ 10 * q0 := by omega
  unfold nbrsWR
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((h0 | h1) | h2)
    · rcases h0 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (cycAdj_iff_sub hq _ wR).mpr (Or.inr (Or.inl rfl))
      · exact (cycAdj_iff_sub hq _ wR).mpr (Or.inr (Or.inr rfl))
    · split_ifs at h1 with hc
      · simp only [List.mem_singleton] at h1
        subst h1
        let idx := (wR.val / 10 - m * uL) / 3
        let d : Fin 3 := ⟨(wR.val / 10 - m * uL) % 3, Nat.mod_lt _ (by omega)⟩
        refine ⟨d, ?_⟩
        apply Fin.ext; dsimp [slotAttA, d]
        have hdm := Nat.div_add_mod idx t
        have hdm3 := Nat.div_add_mod (wR.val / 10 - m * uL) 3
        have hdm10 := Nat.div_add_mod wR.val 10
        have hmul : idx / t * t = t * (idx / t) := Nat.mul_comm _ _
        dsimp [idx] at hdm hmul
        omega
      · simp at h1
    · split_ifs at h2 with hc
      · simp only [List.mem_singleton] at h2
        subst h2
        let d : Fin 3 := ⟨wR.val / 10 - (m * uL + 3 * (m * t)), by omega⟩
        refine ⟨d, rfl, ?_⟩
        apply Fin.ext; dsimp [slotBrR, d]
        have hdm10 := Nat.div_add_mod wR.val 10
        omega
      · simp at h2
  · intro hadj
    rcases u with (⟨i, r⟩ | x | wL) | (⟨i, r⟩ | wR' | y)
    · obtain ⟨d, rfl⟩ := hadj
      left; right
      have hc : (slotAttA hsL i r d).val % 10 = 0 ∧
          m * uL ≤ (slotAttA hsL i r d).val / 10 ∧
          (slotAttA hsL i r d).val / 10 < m * uL + 3 * (m * t) := by
        dsimp [slotAttA]
        have := mul_add_lt_mul i.isLt r.isLt; have := d.isLt; omega
      simp only [hc, and_self, ↓reduceDIte, List.mem_singleton]
      congr 1; congr 1
      have hdiv : ((slotAttA hsL i r d).val / 10 - m * uL) / 3 = i.val * t + r.val := by
        dsimp [slotAttA]; have := d.isLt; omega
      ext
      · dsimp; rw [hdiv, Nat.mul_comm i.val t, Nat.mul_add_div (by omega), Nat.div_eq_of_lt r.isLt]; omega
      · dsimp; rw [hdiv, Nat.mul_comm i.val t, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
    · left; left
      rcases (cycAdj_iff_sub hq x wR).mp hadj with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨d, rfl, rfl⟩ := hadj
      right
      have hc : (slotBrR hsL d).val % 10 = 0 ∧
          m * uL + 3 * (m * t) ≤ (slotBrR hsL d).val / 10 ∧
          (slotBrR hsL d).val / 10 < m * uL + 3 * (m * t) + 3 := by
        dsimp [slotBrR]; have := d.isLt; omega
      simp only [hc, and_self, ↓reduceDIte, List.mem_singleton]
      congr 1; congr 1; congr 1; congr 1; apply Fin.ext; dsimp [slotBrR]; omega
    · exact False.elim hadj
    · exact False.elim hadj
    · exact False.elim hadj

lemma mem_nbrsWL_iff {n t uL uR m q0 : ℕ} (G : SimpleGraph (Fin n))
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (ht : 1 ≤ t) (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (wL : Fin (10 * q0)) (v : AmpV m t (10 * q0)) :
    v ∈ nbrsWL (m := m) (uR := uR) ht hq0 wL ↔
      ((ampGraph0 G eG hsL hsR).Adj (vWL wL) v ∧ ∀ wR, v ≠ vWR wR) := by
  have hq : 10 ≤ 10 * q0 := by omega
  unfold nbrsWL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((rfl | rfl | rfl) | h1)
    · exact ⟨Or.inl rfl, fun _ h => by simp [vY2, vWR] at h⟩
    · exact ⟨(cycAdj_iff_sub hq _ wL).mpr (Or.inr (Or.inl rfl)), fun _ h => by simp [vY2, vWR] at h⟩
    · exact ⟨(cycAdj_iff_sub hq _ wL).mpr (Or.inr (Or.inr rfl)), fun _ h => by simp [vY2, vWR] at h⟩
    · split_ifs at h1 with hc
      · simp only [List.mem_singleton] at h1
        subst h1
        refine ⟨?_, fun _ h => by simp [vB0, vWR] at h⟩
        let idx := (wL.val / 10 - m * uR) / 3
        let d : Fin 3 := ⟨(wL.val / 10 - m * uR) % 3, Nat.mod_lt _ (by omega)⟩
        refine ⟨d, ?_⟩
        apply Fin.ext; dsimp [slotAttB, d]
        have hdm := Nat.div_add_mod idx t
        have hdm3 := Nat.div_add_mod (wL.val / 10 - m * uR) 3
        have hdm10 := Nat.div_add_mod wL.val 10
        have hmul : idx / t * t = t * (idx / t) := Nat.mul_comm _ _
        dsimp [idx] at hdm hmul
        omega
      · simp at h1
  · rintro ⟨hadj, hnotWR⟩
    rcases v with (⟨i, r⟩ | x | wL') | (⟨i, r⟩ | wR | y)
    · exact False.elim hadj
    · exact False.elim hadj
    · exact False.elim hadj
    · obtain ⟨d, rfl⟩ := hadj
      right
      have hc : (slotAttB hsR i r d).val % 10 = 0 ∧
          m * uR ≤ (slotAttB hsR i r d).val / 10 ∧
          (slotAttB hsR i r d).val / 10 < m * uR + 3 * (m * t) := by
        dsimp [slotAttB]
        have := mul_add_lt_mul i.isLt r.isLt; have := d.isLt; omega
      simp only [hc, and_self, ↓reduceDIte, List.mem_singleton]
      congr 1; congr 1
      have hdiv : ((slotAttB hsR i r d).val / 10 - m * uR) / 3 = i.val * t + r.val := by
        dsimp [slotAttB]; have := d.isLt; omega
      ext
      · dsimp; rw [hdiv, Nat.mul_comm i.val t, Nat.mul_add_div (by omega), Nat.div_eq_of_lt r.isLt]; omega
      · dsimp; rw [hdiv, Nat.mul_comm i.val t, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
    · exact absurd rfl (hnotWR wR)
    · left
      rcases (cycAdj_iff_sub hq y wL).mp hadj with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

lemma list_sum_map_finRange {q : ℕ} (f : Fin q → ℕ) :
    ((List.finRange q).map f).sum = ∑ x : Fin q, f x := by
  have h1 : (Finset.univ : Finset (Fin q)) = (List.finRange q).toFinset := by
    ext x; simp
  rw [h1, List.sum_toFinset f (List.nodup_finRange q)]

lemma sum_nbrsWR_len {m t uL uR q0 : ℕ} (ht : 1 ≤ t) (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0) :
    ((List.finRange (10 * q0)).map fun wR =>
      (nbrsWR (m := m) (uL := uL) ht hq0 hsR wR).length).sum =
      3 * (10 * q0) + 3 * (m * t) + 3 := by
  classical
  rw [list_sum_map_finRange]
  let P1 (wR : Fin (10 * q0)) : Prop :=
    wR.val % 10 = 0 ∧ m * uL ≤ wR.val / 10 ∧ wR.val / 10 < m * uL + 3 * (m * t)
  let P2 (wR : Fin (10 * q0)) : Prop :=
    wR.val % 10 = 0 ∧ m * uL + 3 * (m * t) ≤ wR.val / 10 ∧ wR.val / 10 < m * uL + 3 * (m * t) + 3
  have hlen : ∀ wR : Fin (10 * q0),
      (nbrsWR (m := m) (uL := uL) ht hq0 hsR wR).length =
        3 + (if P1 wR then 1 else 0) + (if P2 wR then 1 else 0) := by
    intro wR
    unfold nbrsWR
    simp only [List.length_append, List.length_cons, List.length_nil]
    dsimp only [P1, P2]
    split_ifs <;> simp only [List.length_cons, List.length_nil]
  simp_rw [hlen, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Finset.sum_boole, Nat.cast_id]
  have hP1 : (Finset.univ.filter P1).card = 3 * (m * t) := by
    let f : (Fin m × Fin t) × Fin 3 → Fin (10 * q0) := fun ⟨⟨i, r⟩, d⟩ => slotAttA hsL i r d
    have hfinj : Function.Injective f := by
      rintro ⟨⟨i1, r1⟩, d1⟩ ⟨⟨i2, r2⟩, d2⟩ h
      obtain ⟨rfl, rfl, rfl⟩ := slotAttA_inj hsL h; rfl
    have himg : Finset.univ.image f = Finset.univ.filter P1 := by
      ext wR
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f, P1]
      constructor
      · rintro ⟨⟨⟨i, r⟩, d⟩, rfl⟩
        dsimp [slotAttA]; have := mul_add_lt_mul i.isLt r.isLt; have := d.isLt; omega
      · rintro ⟨hmod, hlo, hhi⟩
        let idx := (wR.val / 10 - m * uL) / 3
        have hidx : idx < m * t := by omega
        let i : Fin m := ⟨idx / t, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)⟩
        let r : Fin t := ⟨idx % t, Nat.mod_lt _ (by omega)⟩
        let d : Fin 3 := ⟨(wR.val / 10 - m * uL) % 3, Nat.mod_lt _ (by omega)⟩
        refine ⟨⟨⟨i, r⟩, d⟩, Fin.ext ?_⟩
        dsimp [slotAttA, i, r, d]
        have hdm : t * (idx / t) + idx % t = idx := Nat.div_add_mod idx t
        have hdm3 : 3 * idx + (wR.val / 10 - m * uL) % 3 = wR.val / 10 - m * uL := Nat.div_add_mod _ 3
        have hdm10 := Nat.div_add_mod wR.val 10
        have hmul : idx / t * t = t * (idx / t) := Nat.mul_comm _ _
        omega
    rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]; ring
  have hP2 : (Finset.univ.filter P2).card = 3 := by
    let f : Fin 3 → Fin (10 * q0) := fun d => slotBrR hsL d
    have hfinj : Function.Injective f := fun _ _ h => slotBrR_inj hsL h
    have himg : Finset.univ.image f = Finset.univ.filter P2 := by
      ext wR
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f, P2]
      constructor
      · rintro ⟨d, rfl⟩; dsimp [slotBrR]; have := d.isLt; omega
      · rintro ⟨hmod, hlo, hhi⟩
        refine ⟨⟨wR.val / 10 - (m * uL + 3 * (m * t)), by omega⟩, Fin.ext ?_⟩
        dsimp [slotBrR]
        have hdm10 := Nat.div_add_mod wR.val 10
        omega
    rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  rw [hP1, hP2]; omega

lemma sum_nbrsWL_len {m t uR q0 : ℕ} (ht : 1 ≤ t) (hq0 : 1 ≤ q0)
    (hsR : m * uR + 3 * (m * t) + 3 ≤ q0) :
    ((List.finRange (10 * q0)).map fun wL =>
      (nbrsWL (m := m) (uR := uR) ht hq0 wL).length).sum =
      3 * (10 * q0) + 3 * (m * t) := by
  classical
  rw [list_sum_map_finRange]
  let P1 (wL : Fin (10 * q0)) : Prop :=
    wL.val % 10 = 0 ∧ m * uR ≤ wL.val / 10 ∧ wL.val / 10 < m * uR + 3 * (m * t)
  have hlen : ∀ wL : Fin (10 * q0),
      (nbrsWL (m := m) (uR := uR) ht hq0 wL).length = 3 + (if P1 wL then 1 else 0) := by
    intro wL
    unfold nbrsWL
    simp only [List.length_append, List.length_cons, List.length_nil]
    dsimp only [P1]
    split_ifs <;> simp only [List.length_cons, List.length_nil]
  simp_rw [hlen, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Finset.sum_boole, Nat.cast_id]
  have hP1 : (Finset.univ.filter P1).card = 3 * (m * t) := by
    let f : (Fin m × Fin t) × Fin 3 → Fin (10 * q0) := fun ⟨⟨i, r⟩, d⟩ => slotAttB hsR i r d
    have hfinj : Function.Injective f := by
      rintro ⟨⟨i1, r1⟩, d1⟩ ⟨⟨i2, r2⟩, d2⟩ h
      obtain ⟨rfl, rfl, rfl⟩ := slotAttB_inj hsR h; rfl
    have himg : Finset.univ.image f = Finset.univ.filter P1 := by
      ext wL
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f, P1]
      constructor
      · rintro ⟨⟨⟨i, r⟩, d⟩, rfl⟩
        dsimp [slotAttB]; have := mul_add_lt_mul i.isLt r.isLt; have := d.isLt; omega
      · rintro ⟨hmod, hlo, hhi⟩
        let idx := (wL.val / 10 - m * uR) / 3
        have hidx : idx < m * t := by omega
        let i : Fin m := ⟨idx / t, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)⟩
        let r : Fin t := ⟨idx % t, Nat.mod_lt _ (by omega)⟩
        let d : Fin 3 := ⟨(wL.val / 10 - m * uR) % 3, Nat.mod_lt _ (by omega)⟩
        refine ⟨⟨⟨i, r⟩, d⟩, Fin.ext ?_⟩
        dsimp [slotAttB, i, r, d]
        have hdm : t * (idx / t) + idx % t = idx := Nat.div_add_mod idx t
        have hdm3 : 3 * idx + (wL.val / 10 - m * uR) % 3 = wL.val / 10 - m * uR := Nat.div_add_mod _ 3
        have hdm10 := Nat.div_add_mod wL.val 10
        have hmul : idx / t * t = t * (idx / t) := Nat.mul_comm _ _
        omega
    rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]; ring
  rw [hP1]; omega

lemma comap_ampGraph0_edgeCard {n t uL uR m q0 N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (eG : (Fin t ⊕ Fin uL) ⊕ (Fin t ⊕ Fin uR) ≃ Fin n)
    (hL : ∀ x y : Fin t ⊕ Fin uL, ¬G.Adj (eG (Sum.inl x)) (eG (Sum.inl y)))
    (hR : ∀ x y : Fin t ⊕ Fin uR, ¬G.Adj (eG (Sum.inr x)) (eG (Sum.inr y)))
    (hnoU : ∀ (j : Fin uL) (k : Fin uR),
      ¬G.Adj (eG (Sum.inl (Sum.inr j))) (eG (Sum.inr (Sum.inr k))))
    (hq0 : 1 ≤ q0)
    (hsL : m * uL + 3 * (m * t) + 3 ≤ q0) (hsR : m * uR + 3 * (m * t) + 3 ≤ q0)
    (equivV : AmpV m t (10 * q0) ≃ Fin N)
    [DecidableRel (SimpleGraph.comap equivV.symm (ampGraph0 G eG hsL hsR)).Adj] :
    (SimpleGraph.comap equivV.symm (ampGraph0 G eG hsL hsR)).edgeFinset.card =
      m * G.edgeFinset.card + 6 * (10 * q0) + 6 * (m * t) + 3 := by
  let H0 := ampGraph0 G eG hsL hsR
  let H := SimpleGraph.comap equivV.symm H0
  have hcard0 := ampGraph0_edgeCard G eG hL hR hnoU hq0 hsL hsR
  rw [← hcard0]
  have _ : DecidableRel H0.Adj := Classical.decRel _
  have himg : H0.edgeFinset.image (Sym2.map equivV) = H.edgeFinset := by
    ext ed
    induction ed using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨e', he', heq⟩
        induction e' using Sym2.ind with
        | _ a b =>
          change s(equivV a, equivV b) = s(u, v) at heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · change H0.Adj (equivV.symm (equivV a)) (equivV.symm (equivV b))
            simpa using he'
          · change H0.Adj (equivV.symm (equivV b)) (equivV.symm (equivV a))
            simpa using he'.symm
      · intro huv
        exact ⟨s(equivV.symm u, equivV.symm v), huv, by simp⟩
  rw [← himg, Finset.card_image_of_injective _ (Sym2.map.injective equivV.injective)]
  exact congrArg Finset.card (Finset.ext fun ed => by simp [SimpleGraph.mem_edgeFinset, H0])

lemma circuit_output_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcyc : ¬G.IsAcyclic) (hfun : circuitFun n C = graphFun G ∅) :
    C.output < n + C.size := by
  obtain ⟨u0, v0, huv0⟩ := has_edge_of_not_acyclic G hcyc
  by_contra! hge
  let x0 : Fin n → Bool := fun v => decide (v = u0 ∨ v = v0)
  have htrue : graphFun G ∅ x0 = true := by
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u0, v0, huv0, by simp [x0], by simp [x0]⟩
  have hev : C.eval (List.ofFn x0) = true := by
    have := congrFun hfun x0
    simpa [circuitFun, htrue] using this
  have hlen : (C.wires (List.ofFn x0)).length = n + C.size := by
    change (evalAll C.gates (List.ofFn x0)).length = n + C.gates.length
    rw [evalAll_length, List.length_ofFn]
  have hfalse : C.eval (List.ofFn x0) = false := by
    unfold Circuit.eval
    rw [List.getD_eq_default _ _ (by omega)]
  rw [hfalse] at hev
  exact Bool.false_ne_true hev

set_option maxHeartbeats 1200000 in
theorem main_proof (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hbip : G.IsBipartite) (hcyc : ¬G.IsAcyclic) (hno4 : NoFourCycle G)
    (hleast : IsLeastAO G C) :
    ∃ (m N : ℕ) (H : SimpleGraph (Fin N)) (_ : DecidableRel H.Adj) (D : Circuit),
      N < m ^ (2 : ℕ) ∧ H.IsBipartite ∧ NoFourCycle H ∧
      (∀ (S : Finset (Fin N)), S.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑S)ᶜ H).Connected) ∧
      (∃ (M : H.Subgraph), M.IsPerfectMatching) ∧
      ((2 : ℕ) * H.edgeFinset.card - (3 : ℕ) * N) ^ (3 : ℕ) ≤ N ^ (2 : ℕ) ∧
      IsAO2 N D ∧ circuitFun N D = graphFun H ∅ ∧
      m * (G.edgeFinset.card + G.vertexCoverNum.toNat) + (D.size + (1 : ℕ)) ≤
        H.edgeFinset.card + N / (2 : ℕ) + m * (C.size + (1 : ℕ)) := by
  classical
  obtain ⟨uL, uR, eG, htpos, hmatch, hL_indep, hR_indep, hnoU⟩ := konig_decomp G hbip hcyc
  let t : ℕ := G.vertexCoverNum.toNat
  let e : ℕ := G.edgeFinset.card
  have hn_eq : 2 * t + uL + uR = n := by
    have hcard := Fintype.card_congr eG
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  have ht_le : t ≤ n := by omega
  have huL_le : uL ≤ n := by omega
  have huR_le : uR ≤ n := by omega
  let P : ℕ := 2 * e + 6 * t + 6
  have hP6 : 6 ≤ P := by omega
  let B : ℕ := 50 * P ^ 2 + 30 * n + 100
  have hB100 : 100 ≤ B := by omega
  let m : ℕ := B ^ 2
  let q0 : ℕ := P ^ 2 * B ^ 3
  let q : ℕ := 10 * q0
  let N : ℕ := 2 * (m * t + 2 * q)
  have hm1 : 1 ≤ m := by
    have : 100 * 100 ≤ B * B := Nat.mul_le_mul hB100 hB100
    dsimp [m]; rw [sq]; omega
  have hP2pos : 1 ≤ P ^ 2 := by rw [sq]; nlinarith
  have hB3pos : 1 ≤ B ^ 3 := by rw [pow_three]; nlinarith
  have hq0_pos : 1 ≤ q0 := by dsimp [q0]; nlinarith
  have hsL : m * uL + 3 * (m * t) + 3 ≤ q0 := by
    have h1 : m * uL + 3 * (m * t) + 3 ≤ (3 * n + 3) * B ^ 2 := by
      dsimp [m]; nlinarith
    have h2 : (3 * n + 3) * B ^ 2 ≤ B * B ^ 2 :=
      Nat.mul_le_mul_right (B ^ 2) (by omega)
    have h3 : B * B ^ 2 = B ^ 3 := by ring
    have h4 : B ^ 3 ≤ P ^ 2 * B ^ 3 := Nat.le_mul_of_pos_left (B ^ 3) hP2pos
    omega
  have hsR : m * uR + 3 * (m * t) + 3 ≤ q0 := by
    have h1 : m * uR + 3 * (m * t) + 3 ≤ (3 * n + 3) * B ^ 2 := by
      dsimp [m]; nlinarith
    have h2 : (3 * n + 3) * B ^ 2 ≤ B * B ^ 2 :=
      Nat.mul_le_mul_right (B ^ 2) (by omega)
    have h3 : B * B ^ 2 = B ^ 3 := by ring
    have h4 : B ^ 3 ≤ P ^ 2 * B ^ 3 := Nat.le_mul_of_pos_left (B ^ 3) hP2pos
    omega
  have hcardN : Fintype.card (AmpV m t (10 * q0)) = N := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    dsimp [N, q]; ring
  let equivV : AmpV m t (10 * q0) ≃ Fin N := Fintype.equivFinOfCardEq hcardN
  let H0 : SimpleGraph (AmpV m t (10 * q0)) := ampGraph0 G eG hsL hsR
  let H : SimpleGraph (Fin N) := SimpleGraph.comap equivV.symm H0
  have : DecidableRel H.Adj := Classical.decRel H.Adj
  have : DecidableRel H0.Adj := Classical.decRel H0.Adj
  have hAO : IsAO2 n C := hleast.1
  have hCfun : circuitFun n C = graphFun G ∅ := hleast.2.1
  have hCout : C.output < n + C.size := circuit_output_lt G C hcyc hCfun
  let copyEmbs : List (Fin n → Fin N) :=
    (List.finRange m).map fun i v => equivV (copyEmb0 eG hsL hsR i v)
  let starsWR : List (Fin N × List (Fin N)) :=
    (List.finRange (10 * q0)).map fun wR =>
      (equivV (vWR wR), (nbrsWR (m := m) (uL := uL) htpos hq0_pos hsR wR).map equivV)
  let starsWL : List (Fin N × List (Fin N)) :=
    (List.finRange (10 * q0)).map fun wL =>
      (equivV (vWL wL), (nbrsWL (m := m) (uR := uR) htpos hq0_pos wL).map equivV)
  obtain ⟨gs1, fs1, outs1, hlen1, hol1, hv1, hws1, hany1⟩ :=
    push_copies C hAO hCout copyEmbs [] [] (valid_nil N)
  have hneWR : ∀ s ∈ starsWR, s.2 ≠ [] := by
    intro s hs
    obtain ⟨wR, _, rfl⟩ := List.mem_map.mp hs
    simp [nbrsWR]
  have hneWL : ∀ s ∈ starsWL, s.2 ≠ [] := by
    intro s hs
    obtain ⟨wL, _, rfl⟩ := List.mem_map.mp hs
    simp [nbrsWL]
  obtain ⟨gs2, fs2, outs2, hlen2, hol2, hv2, hws2, hany2⟩ :=
    push_stars starsWR gs1 fs1 (by simpa using hv1) hneWR
  obtain ⟨gs3, fs3, outs3, hlen3, hol3, hv3, hws3, hany3⟩ :=
    push_stars starsWL (gs1 ++ gs2) (fs1 ++ fs2) hv2 hneWL
  let allOuts := outs1 ++ outs2 ++ outs3
  have hall_len : allOuts.length = m + 2 * q := by
    simp only [allOuts, List.length_append, hol1, hol2, hol3, copyEmbs, starsWR, starsWL,
      List.length_map, List.length_finRange, q]; omega
  have hall_wires : ∀ p ∈ allOuts, Wire N (fs1 ++ fs2 ++ fs3) p.1 p.2 := by
    intro p hp
    simp only [allOuts, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · rw [List.append_assoc]; exact wire_mono (by simpa using hws1 p hp) (fs2 ++ fs3)
    · exact wire_mono (hws2 p hp) fs3
    · exact hws3 p hp
  cases hall_cases : allOuts with
  | nil =>
    have := congrArg List.length hall_cases
    rw [hall_len] at this; dsimp at this; omega
  | cons hd tl =>
    have hhd : Wire N (fs1 ++ fs2 ++ fs3) hd.1 hd.2 :=
      hall_wires hd (by rw [hall_cases]; exact List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, Wire N (fs1 ++ fs2 ++ fs3) p.1 p.2 :=
      fun p hp => hall_wires p (by rw [hall_cases]; exact List.mem_cons_of_mem hd hp)
    obtain ⟨gs4, fs4, outW, hlen4, hv4, hw4⟩ := push_or_chain tl _ _ hd.1 hd.2 hv3 hhd htl
    let D : Circuit := ⟨gs1 ++ gs2 ++ gs3 ++ gs4, outW⟩
    obtain ⟨hD_AO, hD_fun_raw⟩ := valid_to_isAO2 hv4 hw4
    have hD_size : D.size = m * C.size + (6 * q + 6 * (m * t) + 3) + (m + 2 * q - 1) := by
      have htl_len : tl.length = m + 2 * q - 1 := by
        have := congrArg List.length hall_cases
        rw [hall_len, List.length_cons] at this; omega
      have hlen2' : gs2.length = 3 * q + 3 * (m * t) + 3 := by
        rw [hlen2]
        have hm2 : (starsWR.map fun s => s.2.length) =
            (List.finRange (10 * q0)).map fun wR =>
              (nbrsWR (m := m) (uL := uL) htpos hq0_pos hsR wR).length := by
          simp [starsWR, List.map_map, Function.comp_def]
        rw [hm2]
        exact sum_nbrsWR_len htpos hq0_pos hsL hsR
      have hlen3' : gs3.length = 3 * q + 3 * (m * t) := by
        rw [hlen3]
        have hm3 : (starsWL.map fun s => s.2.length) =
            (List.finRange (10 * q0)).map fun wL =>
              (nbrsWL (m := m) (uR := uR) htpos hq0_pos wL).length := by
          simp [starsWL, List.map_map, Function.comp_def]
        rw [hm3]
        exact sum_nbrsWL_len htpos hq0_pos hsR
      have hlen1' : gs1.length = m * C.size := by
        rw [hlen1]; simp [copyEmbs]
      change (gs1 ++ gs2 ++ gs3 ++ gs4).length = _
      simp only [List.length_append, hlen1', hlen2', hlen3', hlen4, htl_len]
      omega
    have hD_fun : circuitFun N D = graphFun H ∅ := by
      rw [hD_fun_raw]
      funext x
      have hraw : (hd.2 x || tl.any fun p => p.2 x) = allOuts.any (fun p => p.2 x) := by
        rw [hall_cases]; rfl
      rw [hraw]
      apply Bool.eq_iff_iff.mpr
      simp only [allOuts, List.any_append, Bool.or_eq_true, hany1 x, hany2 x, hany3 x,
        graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq]
      constructor
      · rintro ((hc | hwr) | hwl)
        · simp only [copyEmbs, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
            Function.comp_def] at hc
          obtain ⟨i, hi⟩ := hc
          have hg := congrFun hCfun (fun v => x (equivV (copyEmb0 eG hsL hsR i v)))
          change C.eval (List.ofFn (fun v => x (equivV (copyEmb0 eG hsL hsR i v)))) = _ at hg
          rw [hi] at hg
          have hg' : graphFun G ∅ (fun v => x (equivV (copyEmb0 eG hsL hsR i v))) = true := hg.symm
          simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
            Bool.false_or, decide_eq_true_eq] at hg'
          obtain ⟨a, b, hab, hxa, hxb⟩ := hg'
          refine ⟨equivV (copyEmb0 eG hsL hsR i a), equivV (copyEmb0 eG hsL hsR i b), ?_, hxa, hxb⟩
          change H0.Adj (equivV.symm (equivV (copyEmb0 eG hsL hsR i a)))
            (equivV.symm (equivV (copyEmb0 eG hsL hsR i b)))
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          have hAB : ∀ (u v : Fin n), G.Adj u v →
              (∃ xL yR, eG.symm u = Sum.inl xL ∧ eG.symm v = Sum.inr yR) ∨
              (∃ xL yR, eG.symm v = Sum.inl xL ∧ eG.symm u = Sum.inr yR) := by
            intro u v huv
            cases hu : eG.symm u with
            | inl xL =>
              cases hv : eG.symm v with
              | inl yL =>
                exfalso
                have hu' : u = eG (Sum.inl xL) := (eG.symm_apply_eq.mp hu)
                have hv' : v = eG (Sum.inl yL) := (eG.symm_apply_eq.mp hv)
                rw [hu', hv'] at huv
                exact hL_indep xL yL huv
              | inr yR => exact Or.inl ⟨xL, yR, rfl, rfl⟩
            | inr xR =>
              cases hv : eG.symm v with
              | inl yL => exact Or.inr ⟨yL, xR, rfl, rfl⟩
              | inr yR =>
                exfalso
                have hu' : u = eG (Sum.inr xR) := (eG.symm_apply_eq.mp hu)
                have hv' : v = eG (Sum.inr yR) := (eG.symm_apply_eq.mp hv)
                rw [hu', hv'] at huv
                exact hR_indep xR yR huv
          have hdir : ∀ (xL : Fin t ⊕ Fin uL) (yR : Fin t ⊕ Fin uR),
              G.Adj (eG (Sum.inl xL)) (eG (Sum.inr yR)) →
              H0.Adj (copyEmb0 eG hsL hsR i (eG (Sum.inl xL)))
                (copyEmb0 eG hsL hsR i (eG (Sum.inr yR))) := by
            intro xL yR hxy
            simp only [copyEmb0, Equiv.symm_apply_apply]
            rcases xL with r | j <;> rcases yR with r' | k
            · exact ⟨rfl, hxy⟩
            · exact ⟨k, rfl, hxy⟩
            · exact ⟨j, rfl, hxy⟩
            · exact False.elim (hnoU j k hxy)
          rcases hAB a b hab with ⟨xL, yR, ha', hb'⟩ | ⟨xL, yR, hb', ha'⟩
          · have ha'' : a = eG (Sum.inl xL) := eG.symm_apply_eq.mp ha'
            have hb'' : b = eG (Sum.inr yR) := eG.symm_apply_eq.mp hb'
            rw [ha'', hb''] at hab ⊢
            exact hdir xL yR hab
          · have hb'' : b = eG (Sum.inl xL) := eG.symm_apply_eq.mp hb'
            have ha'' : a = eG (Sum.inr yR) := eG.symm_apply_eq.mp ha'
            rw [ha'', hb''] at hab ⊢
            exact (hdir xL yR hab.symm).symm
        · simp only [starsWR, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
            Function.comp_def, Bool.and_eq_true] at hwr
          obtain ⟨wR, hxwR, v, hvmem, hxv⟩ := hwr
          have hadj0 : H0.Adj v (vWR wR) :=
            (mem_nbrsWR_iff G eG htpos hq0_pos hsL hsR wR v).mp hvmem
          refine ⟨equivV v, equivV (vWR wR), ?_, hxv, hxwR⟩
          change H0.Adj (equivV.symm (equivV v)) (equivV.symm (equivV (vWR wR)))
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          exact hadj0
        · simp only [starsWL, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
            Function.comp_def, Bool.and_eq_true] at hwl
          obtain ⟨wL, hxwL, v, hvmem, hxv⟩ := hwl
          have hadj0 : H0.Adj (vWL wL) v :=
            ((mem_nbrsWL_iff G eG htpos hq0_pos hsL hsR wL v).mp hvmem).1
          refine ⟨equivV (vWL wL), equivV v, ?_, hxwL, hxv⟩
          change H0.Adj (equivV.symm (equivV (vWL wL))) (equivV.symm (equivV v))
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          exact hadj0
      · rintro ⟨u, v, huv, hxu, hxv⟩
        let u0 := equivV.symm u
        let v0 := equivV.symm v
        have huv0 : H0.Adj u0 v0 := huv
        have hxu0 : x (equivV u0) = true := by simpa [u0] using hxu
        have hxv0 : x (equivV v0) = true := by simpa [v0] using hxv
        have hfrom_dir : ∀ (l : LeftV m t (10 * q0)) (r : RightV m t (10 * q0)),
            dirAdj G eG hsL hsR l r → x (equivV (Sum.inl l)) = true → x (equivV (Sum.inr r)) = true →
            (copyEmbs.any fun emb => C.eval (List.ofFn (x ∘ emb))) = true ∨
            (starsWR.any fun s => x s.1 && s.2.any fun w => x w) = true ∨
            (starsWL.any fun s => x s.1 && s.2.any fun w => x w) = true := by
          intro l r hlr hxl hxr
          have hcopy_hit : ∀ (i : Fin m) (a b : Fin n), G.Adj a b →
              x (equivV (copyEmb0 eG hsL hsR i a)) = true →
              x (equivV (copyEmb0 eG hsL hsR i b)) = true →
              (copyEmbs.any fun emb => C.eval (List.ofFn (x ∘ emb))) = true := by
            intro i a b hab hxa hxb
            simp only [copyEmbs, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
              Function.comp_def]
            refine ⟨i, ?_⟩
            have hg := congrFun hCfun (fun v => x (equivV (copyEmb0 eG hsL hsR i v)))
            change C.eval (List.ofFn (fun v => x (equivV (copyEmb0 eG hsL hsR i v)))) = _ at hg
            rw [hg]
            simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
              Bool.false_or, decide_eq_true_eq]
            exact ⟨a, b, hab, hxa, hxb⟩
          have hWR_hit : ∀ (wR : Fin (10 * q0)), H0.Adj (Sum.inl l) (vWR wR) →
              x (equivV (vWR wR)) = true →
              (starsWR.any fun s => x s.1 && s.2.any fun w => x w) = true := by
            intro wR hadj hxwR
            simp only [starsWR, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
              Function.comp_def, Bool.and_eq_true]
            exact ⟨wR, hxwR, Sum.inl l,
              (mem_nbrsWR_iff G eG htpos hq0_pos hsL hsR wR (Sum.inl l)).mpr hadj, hxl⟩
          have hWL_hit : ∀ (wL : Fin (10 * q0)), H0.Adj (vWL wL) (Sum.inr r) →
              (∀ wR, Sum.inr r ≠ vWR wR) →
              x (equivV (vWL wL)) = true →
              (starsWL.any fun s => x s.1 && s.2.any fun w => x w) = true := by
            intro wL hadj hneWR' hxwL
            simp only [starsWL, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
              Function.comp_def, Bool.and_eq_true]
            exact ⟨wL, hxwL, Sum.inr r,
              (mem_nbrsWL_iff G eG htpos hq0_pos hsL hsR wL (Sum.inr r)).mpr ⟨hadj, hneWR'⟩, hxr⟩
          rcases l with ⟨i, p⟩ | x1 | wL <;> rcases r with ⟨i', p'⟩ | wR | y
          · obtain ⟨rfl, hg⟩ := hlr
            left
            refine hcopy_hit i (eG (Sum.inl (Sum.inl p))) (eG (Sum.inr (Sum.inl p'))) hg ?_ ?_
            · simpa [copyEmb0, vA0] using hxl
            · simpa [copyEmb0, vB0] using hxr
          · right; left; exact hWR_hit wR hlr hxr
          · obtain ⟨k, rfl, hg⟩ := hlr
            left
            refine hcopy_hit i (eG (Sum.inl (Sum.inl p))) (eG (Sum.inr (Sum.inr k))) hg ?_ ?_
            · simpa [copyEmb0, vA0] using hxl
            · simpa [copyEmb0, vY2] using hxr
          · obtain ⟨j, rfl, hg⟩ := hlr
            left
            refine hcopy_hit i' (eG (Sum.inl (Sum.inr j))) (eG (Sum.inr (Sum.inl p'))) hg ?_ ?_
            · simpa [copyEmb0, vX1] using hxl
            · simpa [copyEmb0, vB0] using hxr
          · right; left; exact hWR_hit wR hlr hxr
          · exact False.elim hlr
          · right; right; exact hWL_hit wL hlr (fun _ h => by simp [vWR] at h) hxl
          · right; left; exact hWR_hit wR hlr hxr
          · right; right; exact hWL_hit wL hlr (fun _ h => by simp [vWR] at h) hxl
        rcases u0 with l | r <;> rcases v0 with l' | r'
        · exact False.elim huv0
        · rcases hfrom_dir l r' huv0 hxu0 hxv0 with h | h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
        · rcases hfrom_dir l' r huv0 hxv0 hxu0 with h | h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
        · exact False.elim huv0
    have hH_edgeCard : H.edgeFinset.card = m * e + 6 * q + 6 * (m * t) + 3 :=
      comap_ampGraph0_edgeCard G eG hL_indep hR_indep hnoU hq0_pos hsL hsR equivV
    refine ⟨m, N, H, inferInstance, D, ?_, ?_, ?_, ?_, ?_, ?_, hD_AO, hD_fun, ?_⟩
    · have htB : t ≤ B := by omega
      have hP2_36 : 36 ≤ P ^ 2 := by rw [sq]; nlinarith
      have h1 : 2 * m * t ≤ 2 * B ^ 3 := by dsimp [m]; nlinarith
      have h2 : N = 2 * m * t + 40 * P ^ 2 * B ^ 3 := by dsimp [N, q, q0]; ring
      have h3 : m ^ 2 = B * B ^ 3 := by dsimp [m]; ring
      have h4 : 2 * B ^ 3 + 40 * P ^ 2 * B ^ 3 < 50 * P ^ 2 * B ^ 3 := by nlinarith
      have h5 : 50 * P ^ 2 * B ^ 3 ≤ B * B ^ 3 :=
        Nat.mul_le_mul_right (B ^ 3) (by dsimp [B]; omega)
      omega
    · obtain ⟨col0⟩ := ampGraph0_bipartite G eG hsL hsR
      exact ⟨SimpleGraph.Coloring.mk (fun v => col0 (equivV.symm v)) (fun h => col0.valid h)⟩
    · intro a b hne
      apply Finset.card_le_one.mpr
      intro w1 hw1 w2 hw2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
      have hne0 : equivV.symm a ≠ equivV.symm b := fun h => hne (equivV.symm.injective h)
      have heq0 := ampGraph0_noFourCycle G hno4 eG hq0_pos hsL hsR hne0 hw1.1 hw1.2 hw2.1 hw2.2
      exact equivV.symm.injective heq0
    · intro S hS
      let S0 : Finset (AmpV m t (10 * q0)) :=
        S.preimage equivV (fun _ _ _ _ h => equivV.injective h)
      have hS0 : S0.card ≤ 2 := by
        have himg : S0.image equivV ⊆ S := fun z hz => by
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz; exact Finset.mem_preimage.mp hp
        have := (Finset.card_image_of_injective S0 equivV.injective).symm.le.trans (Finset.card_le_card himg)
        omega
      have hconn0 := ampGraph0_threeConn G eG hq0_pos hsL hsR S0 hS0
      let f : (H0.induce (↑S0 : Set (AmpV m t (10 * q0)))ᶜ) →g (H.induce (↑S : Set (Fin N))ᶜ) := {
        toFun := fun u => ⟨equivV u.1, fun h => u.2 (Finset.mem_preimage.mpr (by simpa using h))⟩
        map_rel' := fun {u v} huv => by
          change H0.Adj (equivV.symm (equivV u.1)) (equivV.symm (equivV v.1))
          simpa using huv
      }
      have hf_surj : Function.Surjective f := by
        rintro ⟨v, hv⟩
        refine ⟨⟨equivV.symm v, fun h => hv (by
          have := Finset.mem_preimage.mp h; simpa using this)⟩, Subtype.ext (equivV.apply_symm_apply v)⟩
      obtain ⟨u0⟩ := hconn0.nonempty
      have : Nonempty ((↑S : Set (Fin N))ᶜ : Set (Fin N)) := ⟨f u0⟩
      refine ⟨fun x y => ?_⟩
      obtain ⟨x0, rfl⟩ := hf_surj x
      obtain ⟨y0, rfl⟩ := hf_surj y
      exact (hconn0.preconnected x0 y0).map f
    · obtain ⟨M0, hM0⟩ := ampGraph0_perfectMatching G eG hsL hsR hmatch
      let M : H.Subgraph := {
        verts := Set.univ
        Adj := fun u v => M0.Adj (equivV.symm u) (equivV.symm v)
        adj_sub := fun h => M0.adj_sub h
        edge_vert := fun _ => Set.mem_univ _
        symm := ⟨fun _ _ h => M0.adj_symm h⟩
      }
      refine ⟨M, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr fun v => ?_⟩
      obtain ⟨w0, hw0, huniq⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM0 (equivV.symm v)
      refine ⟨equivV w0, by simpa [M] using hw0, fun w hw => ?_⟩
      have := huniq (equivV.symm w) hw
      rw [← this, equivV.apply_symm_apply]
    · rw [hH_edgeCard]
      have hdiff : 2 * (m * e + 6 * q + 6 * (m * t) + 3) - 3 * N ≤ P * B ^ 2 := by
        have hN3 : 3 * N = 6 * (m * t) + 12 * q := by dsimp [N]; ring
        rw [hN3]
        have hsub : 2 * (m * e + 6 * q + 6 * (m * t) + 3) - (6 * (m * t) + 12 * q) =
            2 * (m * e) + 6 * (m * t) + 6 := by
          have : 2 * (m * e + 6 * q + 6 * (m * t) + 3) =
              (2 * (m * e) + 6 * (m * t) + 6) + (6 * (m * t) + 12 * q) := by ring
          rw [this, Nat.add_sub_cancel]
        rw [hsub]
        have hB2 : 1 ≤ B ^ 2 := hm1
        dsimp [P, m]; nlinarith
      have hcube : (2 * (m * e + 6 * q + 6 * (m * t) + 3) - 3 * N) ^ 3 ≤ (P * B ^ 2) ^ 3 :=
        Nat.pow_le_pow_left hdiff 3
      have hNge : 40 * P ^ 2 * B ^ 3 ≤ N := by
        have h40 : 40 * P ^ 2 * B ^ 3 = 4 * q := by dsimp [q, q0]; ring
        have hN4 : N = 2 * (m * t) + 4 * q := by dsimp [N]; ring
        rw [h40, hN4]; exact Nat.le_add_left _ _
      have hNsq : (40 * P ^ 2 * B ^ 3) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hNge 2
      have hcmp : (P * B ^ 2) ^ 3 ≤ (40 * P ^ 2 * B ^ 3) ^ 2 := by
        have hL1 : (P * B ^ 2) ^ 3 = P ^ 3 * B ^ 6 := by ring
        have hR1 : (40 * P ^ 2 * B ^ 3) ^ 2 = 1600 * P * (P ^ 3 * B ^ 6) := by ring
        rw [hL1, hR1]
        have hPpos : 0 < P := Nat.lt_of_lt_of_le (show 0 < 6 by decide) hP6
        have h1600 : 0 < 1600 * P := Nat.mul_pos (show 0 < 1600 by decide) hPpos
        exact Nat.le_mul_of_pos_left (P ^ 3 * B ^ 6) h1600
      exact hcube.trans (hcmp.trans hNsq)
    · rw [hH_edgeCard, hD_size]
      have hNhalf : N / 2 = m * t + 2 * q :=
        Nat.mul_div_cancel_left (m * t + 2 * q) (show 0 < 2 by decide)
      rw [hNhalf]
      change m * (e + t) + (m * C.size + (6 * q + 6 * (m * t) + 3) + (m + 2 * q - 1) + 1) ≤
        (m * e + 6 * q + 6 * (m * t) + 3) + (m * t + 2 * q) + m * (C.size + 1)
      have hsub1 : m + 2 * q - 1 + 1 = m + 2 * q :=
        Nat.sub_add_cancel (le_trans hm1 (Nat.le_add_right m (2 * q)))
      rw [Nat.add_assoc (m * C.size + (6 * q + 6 * (m * t) + 3)), hsub1]
      exact le_of_eq (by ring)

end PEqualNP.Outside.L_meta_18603

theorem PEqualNP.Outside.L_meta_18603 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → ∃ (x9 : ℕ) (x10 : ℕ) (x11 : SimpleGraph (Fin x10)) (_ : DecidableRel x11.Adj) (x13 : PEqualNP.CircuitLowerBounds.Circuit), x10 < x9 ^ (2 : ℕ) ∧ x11.IsBipartite ∧ PEqualNP.TopForm.NoFourCycle x11 ∧ (∀ (x14 : Finset (Fin x10)), x14.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x14)ᶜ x11).Connected) ∧ (∃ (x14 : x11.Subgraph), x14.IsPerfectMatching) ∧ ((2 : ℕ) * x11.edgeFinset.card - (3 : ℕ) * x10) ^ (3 : ℕ) ≤ x10 ^ (2 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x10 x13 ∧ PEqualNP.MetaComplexity.circuitFun x10 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x11 ∅ ∧ x9 * (x2.edgeFinset.card + x2.vertexCoverNum.toNat) + (x13.size + (1 : ℕ)) ≤ x11.edgeFinset.card + x10 / (2 : ℕ) + x9 * (x4.size + (1 : ℕ)) :=
  PEqualNP.Outside.L_meta_18603.main_proof
