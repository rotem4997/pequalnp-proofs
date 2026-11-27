import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2393_1
    (hleast : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C)
    (hbelow : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      PEqualNP.TopForm.junk G C = ∅ → ∀ j < C.gates.length,
        (gateAt C j).op = GateOp.and → PEqualNP.TopForm.BelowF G C j)
    : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (0 : ℕ) := by
  intro G inst C hadj hL hjunk
  have htop : PEqualNP.TopForm.TopForm G C := hleast G C hL
  unfold PEqualNP.TopForm.andPairs
  rw [Finset.card_eq_zero]
  apply Finset.ext
  rintro ⟨i, j⟩
  constructor
  · intro hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨hi, hj⟩, hopi, hopj, hcone⟩ := hp
    exact absurd hcone (htop i hi j hj hopi (hbelow G C hjunk i hi hopi) hopj)
  · intro hp
    simp at hp

