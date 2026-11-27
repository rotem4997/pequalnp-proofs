import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadTwo PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_19026_53
    (trim : ∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C → ∃ D : Circuit, Monotone2 D ∧ ComputesIncidence singerLines3 D ∧ D.size ≤ C.size ∧ D.output + 1 = 26 + D.size ∧ D.lineDeg 26 (Finset.Ico 13 26) = C.lineDeg 26 (Finset.Ico 13 26))
    (good : let pairClean := fun C : Circuit => ∀ j, isAnd C j → ∀ u v : Fin 26, gateVal 26 C j (pairInput u v) = true → ∃ p l : Fin 13, p ∈ singerLines3 l ∧ ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)); ∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C → pairClean C → 64 ≤ C.size)
    (bad : let pairClean := fun C : Circuit => ∀ j, isAnd C j → ∀ u v : Fin 26, gateVal 26 C j (pairInput u v) = true → ∃ p l : Fin 13, p ∈ singerLines3 l ∧ ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)); ∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C → HasLineDegree 26 (Finset.Ico 13 26) C 2 → C.output + 1 = 26 + C.size → C.size ≤ 63 → ¬pairClean C → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) → (64 : ℕ) ≤ x1.size) := by
  intro C hm hc hd
  obtain ⟨D, hmD, hcD, hsize, houtput, hdegree⟩ := trim C hm hc
  have hdD : HasLineDegree 26 (Finset.Ico 13 26) D 2 := by
    change D.lineDeg 26 (Finset.Ico 13 26) ≤ 2
    change C.lineDeg 26 (Finset.Ico 13 26) ≤ 2 at hd
    rwa [hdegree]
  by_cases hpair : ∀ j, isAnd D j → ∀ u v : Fin 26,
      gateVal 26 D j (pairInput u v) = true → ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l))
  · exact (good D hmD hcD hpair).trans hsize
  · by_contra hsmall
    exact bad D hmD hcD hdD houtput (by omega) hpair
