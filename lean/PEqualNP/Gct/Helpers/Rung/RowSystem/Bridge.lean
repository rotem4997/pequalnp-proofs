import PEqualNP.Gct.Helpers.Rung.Statements
import PEqualNP.Gct.Helpers.Rung.RowSystem.Matching

/-!
# The sum of subpermanents is a matching sum

Helper for `PEqualNP.Gct.Rung.RowSystem`: `sumSubperm s Z` (sum of permanents of all `s × s`
submatrices) equals the sum over matchings of size `s` of the product of the entries on the
edges. Nothing here is a result until the lemma that rests on it is checked.
-/

namespace PEqualNP.Gct.Rung.RowSys

open Finset

variable {a b : ℕ}

/-- The edge set of the matching given by a row set, a column set and a permutation. -/
noncomputable def edge {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) : Finset (Fin a × Fin b) :=
  univ.image fun k : Fin s => (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k)

theorem edge_fun_injective {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) :
    Function.Injective fun k : Fin s =>
      (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k) := by
  intro k k' h
  exact (x.2.1.1.orderEmbOfFin x.2.1.2).injective (congrArg Prod.snd h)

theorem edge_image_snd {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) : (edge x).image Prod.snd = x.2.1.1 := by
  unfold edge
  rw [Finset.image_image]
  exact Finset.image_orderEmbOfFin_univ x.2.1.1 x.2.1.2

theorem edge_image_fst {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) : (edge x).image Prod.fst = x.1.1 := by
  unfold edge
  rw [Finset.image_image]
  have : (Prod.fst ∘ fun k : Fin s =>
      (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k))
      = (x.1.1.orderEmbOfFin x.1.2) ∘ x.2.2 := rfl
  rw [this, ← Finset.image_image, Finset.image_univ_equiv]
  exact Finset.image_orderEmbOfFin_univ x.1.1 x.1.2

theorem sumSubperm_eq_mpOn {R : Type} [CommRing R] (s : ℕ) (Z : Matrix (Fin a) (Fin b) R) :
    sumSubperm s Z = mpOn univ univ s (fun e => Z e.1 e.2) := by
  have h1 : sumSubperm s Z = ∑ x : ({S : Finset (Fin a) // S.card = s} ×
      {T : Finset (Fin b) // T.card = s} × Equiv.Perm (Fin s)),
      ∏ k, Z (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k)) (x.2.1.1.orderEmbOfFin x.2.1.2 k) := by
    simp only [sumSubperm, Matrix.permanent, Fintype.sum_prod_type, Matrix.of_apply]
  rw [h1]
  unfold mpOn
  refine Finset.sum_bij (fun x _ => edge x) ?_ ?_ ?_ ?_
  · intro x _
    rw [mem_matchings]
    refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
    · unfold edge
      rw [Finset.card_image_of_injective _ (edge_fun_injective x)]
      simp
    · intro e he e' he' h
      unfold edge at he he'
      obtain ⟨k, _, rfl⟩ := mem_image.mp he
      obtain ⟨k', _, rfl⟩ := mem_image.mp he'
      have : k = k' :=
        x.2.2.injective ((x.1.1.orderEmbOfFin x.1.2).injective h)
      rw [this]
    · intro e he e' he' h
      unfold edge at he he'
      obtain ⟨k, _, rfl⟩ := mem_image.mp he
      obtain ⟨k', _, rfl⟩ := mem_image.mp he'
      have : k = k' := (x.2.1.1.orderEmbOfFin x.2.1.2).injective h
      rw [this]
  · intro x _ x' _ h
    have hS : x.1.1 = x'.1.1 := by rw [← edge_image_fst x, ← edge_image_fst x', h]
    have hT : x.2.1.1 = x'.2.1.1 := by rw [← edge_image_snd x, ← edge_image_snd x', h]
    obtain ⟨⟨S, hS1⟩, ⟨T, hT1⟩, σ⟩ := x
    obtain ⟨⟨S', hS1'⟩, ⟨T', hT1'⟩, σ'⟩ := x'
    simp only at hS hT
    subst hS
    subst hT
    have hσ : σ = σ' := by
      ext k
      have hk : (S.orderEmbOfFin hS1 (σ k), T.orderEmbOfFin hT1 k) ∈
          edge (⟨⟨S, hS1'⟩, ⟨T, hT1'⟩, σ'⟩ :
            {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
              Equiv.Perm (Fin s)) := by
        rw [← h]
        exact mem_image.mpr ⟨k, mem_univ _, rfl⟩
      obtain ⟨k', _, hk'⟩ := mem_image.mp hk
      simp only [Prod.mk.injEq] at hk'
      have hkk : k' = k := (T.orderEmbOfFin hT1).injective hk'.2
      rw [hkk] at hk'
      have := (S.orderEmbOfFin hS1).injective hk'.1
      rw [this]
    rw [hσ]
  · intro M hM
    rw [mem_matchings] at hM
    obtain ⟨⟨_, hcard⟩, hm1, hm2⟩ := hM
    have hS : (M.image Prod.fst).card = s := by
      rw [Finset.card_image_of_injOn, hcard]
      intro e he e' he' h
      exact hm1 e he e' he' h
    have hT : (M.image Prod.snd).card = s := by
      rw [Finset.card_image_of_injOn, hcard]
      intro e he e' he' h
      exact hm2 e he e' he' h
    have hex : ∀ k : Fin s, ∃ e ∈ M, e.2 = (M.image Prod.snd).orderEmbOfFin hT k := by
      intro k
      have := Finset.orderEmbOfFin_mem (M.image Prod.snd) hT k
      obtain ⟨e, he, he2⟩ := mem_image.mp this
      exact ⟨e, he, he2⟩
    choose g hgM hg2 using hex
    have hginj : Function.Injective g := by
      intro k k' h
      have : (M.image Prod.snd).orderEmbOfFin hT k = (M.image Prod.snd).orderEmbOfFin hT k' := by
        rw [← hg2 k, ← hg2 k', h]
      exact ((M.image Prod.snd).orderEmbOfFin hT).injective this
    let φ : Fin s → Fin s := fun k =>
      ((M.image Prod.fst).orderIsoOfFin hS).symm ⟨(g k).1, mem_image_of_mem _ (hgM k)⟩
    have hφ : ∀ k, (M.image Prod.fst).orderEmbOfFin hS (φ k) = (g k).1 := by
      intro k
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [φ]
    have hφinj : Function.Injective φ := by
      intro k k' h
      have h1 : (g k).1 = (g k').1 := by rw [← hφ k, ← hφ k', h]
      exact hginj (hm1 _ (hgM k) _ (hgM k') h1)
    refine ⟨⟨⟨M.image Prod.fst, hS⟩, ⟨M.image Prod.snd, hT⟩,
      Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj)⟩, mem_univ _, ?_⟩
    have himg : (univ.image g) = M := by
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        obtain ⟨k, _, rfl⟩ := mem_image.mp he
        exact hgM k
      · rw [Finset.card_image_of_injective _ hginj, hcard]
        simp
    refine Eq.trans ?_ himg
    unfold edge
    refine Finset.image_congr fun k _ => ?_
    simp only [Equiv.ofBijective_apply]
    rw [hφ k, ← hg2 k]
  · intro x _
    unfold edge
    rw [Finset.prod_image]
    intro k _ k' _ h
    exact edge_fun_injective x h

end PEqualNP.Gct.Rung.RowSys
