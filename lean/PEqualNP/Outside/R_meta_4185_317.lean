import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.R_meta_4185_317
    (centres : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsLeastAO G C → ∃ K : Finset (Fin n),
        K.card ≤ (tops G C \ centreless G C).card ∧
        ∀ u v, G.Adj u v → s(u,v) ∉ Ustar G C → u ∈ K ∨ v ∈ K)
    (linear : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (∀ h ∈ centreless G C ∪ junk G C ∪ mixing G C,
        ((gammaE G C h) ∩ Ustar G C).card ≤ 1) →
      2 * (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card +
        (orN G C \ lam G C).card)
    (shared : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      let U := Ustar G C
      let b := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let t := (tops G C \ centreless G C).card
      b < 2 * U.card →
      (∃ h ∈ centreless G C ∪ junk G C ∪ mixing G C, 1 < (gammaE G C h ∩ U).card) →
      ∀ K : Finset (Fin n), K.card ≤ t →
      (∀ u v, G.Adj u v → s(u,v) ∉ U → u ∈ K ∨ v ∈ K) →
      let R := U.filter fun e => ∀ z ∈ e, z ∉ K
      ∀ M ⊆ R, (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ z ∈ e, z ∉ f) →
      2 * (t + b) + 1 < 2 * (K.card + U.card) + R.card + M.card →
      ∃ I J : Finset (Fin n), I ⊆ K ∧ Disjoint K J ∧
        (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) ∧
        (∀ u ∈ I, ∀ v ∈ J, ¬G.Adj u v) ∧
        (∀ u ∈ J, ∀ v ∈ J, s(u,v) ∉ U) ∧ n + U.card ≤ t + b + I.card + J.card) : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  intro n G inst C h4 _ least top
  classical
  have pairing : ∀ (n : ℕ) (R : Finset (Sym2 (Fin n))), ∃ (X : Finset (Fin n)) (M : Finset (Sym2 (Fin n))),
      M ⊆ R ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ z ∈ e, z ∉ f) ∧
      (∀ e ∈ R, ∃ z ∈ X, z ∈ e) ∧ 2 * X.card ≤ R.card + M.card := by
    intro n R
    classical
    induction R using Finset.strongInduction with
    | H R ih =>
      by_cases overlap : ∃ e ∈ R, ∃ f ∈ R, e ≠ f ∧ ∃ z : Fin n, z ∈ e ∧ z ∈ f
      · obtain ⟨e, he, f, hf, nef, z, hze, hzf⟩ := overlap
        let S := (R.erase e).erase f
        have f' : f ∈ R.erase e := Finset.mem_erase.mpr ⟨nef.symm, hf⟩
        have strict : S ⊂ R := Finset.ssubset_of_subset_of_ssubset
          (Finset.erase_subset ..) (Finset.erase_ssubset he)
        obtain ⟨X, M, ms, disj, cov, cost⟩ := ih S strict
        refine ⟨insert z X, M, ms.trans (le_of_lt strict), disj, ?_, ?_⟩
        · intro g hg
          by_cases ge : g = e
          · exact ⟨z, Finset.mem_insert_self .., ge ▸ hze⟩
          by_cases gf : g = f
          · exact ⟨z, Finset.mem_insert_self .., gf ▸ hzf⟩
          obtain ⟨a, ha, ag⟩ := cov g (Finset.mem_erase.mpr ⟨gf, Finset.mem_erase.mpr ⟨ge, hg⟩⟩)
          exact ⟨a, Finset.mem_insert_of_mem ha, ag⟩
        · have a := Finset.card_erase_add_one he
          have b := Finset.card_erase_add_one f'
          have c := Finset.card_insert_le z X
          dsimp only [S] at cost
          omega
      · have point (e : Sym2 (Fin n)) : ∃ z : Fin n, z ∈ e := by
          induction e using Sym2.inductionOn with
          | _ u v => exact ⟨u, by simp⟩
        let X := R.image fun e => (point e).choose
        refine ⟨X, R, fun _ h => h, ?_, ?_, ?_⟩
        · intro e he f hf ne z ze zf
          exact overlap ⟨e, he, f, hf, ne, z, ze, zf⟩
        · intro e he
          exact ⟨(point e).choose, Finset.mem_image_of_mem _ he, (point e).choose_spec⟩
        · have bound : X.card ≤ R.card := Finset.card_image_le
          omega
  obtain ⟨K, hk, hits⟩ := centres n G C h4 least
  let U := Ustar G C
  let b := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  let t := (tops G C \ centreless G C).card
  let R := U.filter fun e => ∀ z ∈ e, z ∉ K
  obtain ⟨X, M, ms, matching, covers, cost⟩ := pairing n R
  have cover : IsVertexCover G (K ∪ X) := by
    intro u v uv
    by_cases uk : u ∈ K
    · exact Or.inl (Finset.mem_union_left _ uk)
    by_cases vk : v ∈ K
    · exact Or.inr (Finset.mem_union_left _ vk)
    have mem : s(u,v) ∈ U := by
      by_contra ne
      exact (hits u v uv ne).elim uk vk
    have resid : s(u,v) ∈ R := Finset.mem_filter.mpr ⟨mem, fun z hz =>
      (Sym2.mem_iff.mp hz).elim (fun h => h.symm ▸ uk) (fun h => h.symm ▸ vk)⟩
    obtain ⟨z, hz, on⟩ := covers _ resid
    rcases Sym2.mem_iff.mp on with h | h
    · exact Or.inl (Finset.mem_union_right _ (h ▸ hz))
    · exact Or.inr (Finset.mem_union_right _ (h ▸ hz))
  change K.card ≤ t at hk
  by_cases enough : K.card + X.card + U.card ≤ t + b
  · refine ⟨K ∪ X, cover, ?_⟩
    have sum := Finset.card_union_le K X
    change (K ∪ X).card + U.card ≤ t + 2 * (centreless G C).card +
      (junk G C).card + (orN G C \ lam G C).card
    change K.card + X.card + U.card ≤ t + (2 * (centreless G C).card +
      (junk G C).card + (orN G C \ lam G C).card) at enough
    omega
  · have subR : R ⊆ U := Finset.filter_subset _ _
    have mcard := Finset.card_le_card ms
    have rcard := Finset.card_le_card subR
    have pressure : b < 2 * U.card := by omega
    have stress : 2 * (t+b) + 1 < 2 * (K.card + U.card) + R.card + M.card := by omega
    have collision : ∃ h ∈ centreless G C ∪ junk G C ∪ mixing G C,
          1 < (gammaE G C h ∩ U).card := by
      by_contra none
      apply (Nat.not_le_of_lt pressure)
      apply linear n G C least top
      intro h hh
      exact Nat.le_of_not_gt (fun hard => none ⟨h, hh, hard⟩)
    obtain ⟨I, J, sub, sep, ii, ij, jj, bound⟩ :=
      shared n G C h4 least top pressure collision K hk hits M ms matching stress
    have apart := Finset.disjoint_left.mp sep
    have disj : Disjoint I J := Finset.disjoint_left.mpr (fun x hx => apart (sub hx))
    refine ⟨(I ∪ J)ᶜ, ?_, ?_⟩
    · intro u v uv
      by_contra avoid
      have hu : u ∈ I ∨ u ∈ J := Finset.mem_union.mp (by
        by_contra hu
        exact avoid (Or.inl (Finset.mem_compl.mpr hu)))
      have hv : v ∈ I ∨ v ∈ J := Finset.mem_union.mp (by
        by_contra hv
        exact avoid (Or.inr (Finset.mem_compl.mpr hv)))
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact ii u hu v hv uv
      · exact ij u hu v hv uv
      · exact ij v hv u hu uv.symm
      · rcases hits u v uv (jj u hu v hv) with h | h
        · exact apart h hu
        · exact apart h hv
    · have total := Finset.card_compl_add_card (I ∪ J)
      rw [Finset.card_union_of_disjoint disj, Fintype.card_fin] at total
      change n + U.card ≤ t + (2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card) + I.card + J.card at bound
      change (I ∪ J)ᶜ.card + U.card ≤ t + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card
      omega
