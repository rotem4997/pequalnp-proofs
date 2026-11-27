import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3396_1
    (embedding : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)),
      (∀ p q l s, p ≠ q → l ≠ s →
        ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      M ⊆ E →
      (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) →
      (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
      (∀ e ∈ E, ¬ ((∀ d ∈ E, d.1 = e.1 → d = e) ∨
        (∀ d ∈ E, d.2 = e.2 → d = e))) →
      ∃ (G : SimpleGraph (Fin (n+m))) (T : Finset (Fin (n+m) × Fin (n+m))),
        ∀ [DecidableRel G.Adj],
        G.edgeFinset.card = E.card ∧ T.card = M.card ∧ NoFourCycle G ∧
        (∃ c : Fin (n+m) → Bool, ∀ u v, G.Adj u v → c u ≠ c v) ∧
        (∀ u, (G.neighborSet u).ncard ≠ 1) ∧
        (∀ e ∈ T, G.Adj e.1 e.2) ∧
        (∀ e ∈ T, ∀ d ∈ T, e.1 = d.1 → e = d) ∧
        (∀ e ∈ T, ∀ d ∈ T, e.2 = d.2 → e = d) ∧
        (∀ e ∈ T, ∀ d ∈ T, e.1 ≠ d.2) ∧
        ∀ z, graphFun G ∅ z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true))
    (normalization : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit),
      G.edgeFinset.Nonempty → IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size ∧
        ∀ D' : Circuit, IsLeastAO G D' → TopForm G D' →
          (Ustar G D).card ≤ (Ustar G D').card)
    (charging : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (D : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G D → TopForm G D →
      G.edgeFinset.card + (tops G D \ centreless G D).card +
        2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card ≤
        D.size + (Ustar G D).card + 1)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (D : Circuit) (T : Finset (Fin n × Fin n)),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G D → TopForm G D →
      (∀ D' : Circuit, IsLeastAO G D' → TopForm G D' →
        (Ustar G D).card ≤ (Ustar G D').card) →
      (∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) →
      (∀ u, (G.neighborSet u).ncard ≠ 1) →
      (∀ e ∈ T, G.Adj e.1 e.2) →
      (∀ e ∈ T, ∀ d ∈ T, e.1 = d.1 → e = d) →
      (∀ e ∈ T, ∀ d ∈ T, e.2 = d.2 → e = d) →
      (∀ e ∈ T, ∀ d ∈ T, e.1 ≠ d.2) →
      (Ustar G D).card + T.card ≤ (tops G D \ centreless G D).card +
        2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
        ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool),
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 =
          Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2),
            (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧
              x8 (Fin.natAdd x1 x10) = Bool.true)) →
      x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →
      (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →
      have x12 : Fin x1 × Fin x2 → Prop := fun x12 =>
        (∀ x13 ∈ x3, x13.1 = x12.1 → x13 = x12) ∨
        ∀ x13 ∈ x3, x13.2 = x12.2 → x13 = x12;
      (∀ x13 ∈ x3, ¬x12 x13) → x3.card + x4.card ≤ x5.size + 1 := by
  classical
  intro n m E M C h4 hAO hfun hME hrow hcol
  dsimp only
  intro hleaf
  by_cases hE : E.Nonempty
  · obtain ⟨G, T, hG⟩ := embedding n m E M h4 hME hrow hcol hleaf
    obtain ⟨hcard, hTcard, hNo4, hcolor, hdeg, hTE, hTr, hTc, hCross, hGF⟩ := hG
    have hne : G.edgeFinset.Nonempty := by
      rw [← Finset.card_pos, hcard]
      exact Finset.card_pos.mpr hE
    have hcompute : circuitFun (n+m) C = graphFun G ∅ := by
      funext z
      exact (hfun z).trans (hGF z).symm
    obtain ⟨D, hleast, htop, hsize, hmin⟩ := normalization (n+m) G C hne hAO hcompute
    have hcharge := charging (n+m) G D hNo4 hne hleast htop
    have hbudget := residual (n+m) G D T hNo4 hne hleast htop hmin
      hcolor hdeg hTE hTr hTc hCross
    omega
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have hm : M = ∅ := Finset.subset_empty.mp (he ▸ hME)
    simp [he, hm]
