import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1845

theorem small (N q s : ℕ) (hN : N = q ^ 2 + q + 1) (hq : q < 200) (h : 2 * N ≤ s + 1) :
    N * q ≤ 100 * s := by
  have h1 : q ≤ N := by
    rw [hN]; exact le_trans (Nat.le_add_left q (q ^ 2)) (Nat.le_succ _)
  have h2 : 1 ≤ N := by
    rw [hN]; exact Nat.le_add_left 1 _
  have h3 : N * q + 100 ≤ 200 * N := by
    rcases Nat.lt_or_ge q 101 with h | h
    · have h5 : N * q ≤ N * 100 := Nat.mul_le_mul_left N (by omega)
      omega
    · have h5 : N * q ≤ N * 199 := Nat.mul_le_mul_left N (by omega)
      omega
  generalize N * q = t at h3 ⊢
  omega

end PEqualNP.Outside.L_meta_1845

theorem PEqualNP.Outside.L_meta_1845 : (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1) → (∀ (qlv18 Nlv18 klv18 mlv18 alv18 clv18 : ℕ) (Ilv18 : Fin Nlv18 → Fin Nlv18 → Prop) [DecidableRel Ilv18] (Clv18 : PEqualNP.CircuitLowerBounds.Circuit) (Rlv18 : ℕ → ℕ), 2 ≤ qlv18 → Nlv18 = qlv18 ^ 2 + qlv18 + 1 → (∀ llv18 : Fin Nlv18, (Finset.univ.filter (fun plv18 => Ilv18 plv18 llv18)).card = qlv18 + 1) → (∀ palv18 pblv18 : Fin Nlv18, palv18 ≠ pblv18 → ∃! lblv18 : Fin Nlv18, Ilv18 palv18 lblv18 ∧ Ilv18 pblv18 lblv18) → 1 ≤ klv18 → klv18 ≤ qlv18 → ((∀ glv18 ∈ Clv18.gates, (glv18.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv18.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv18.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv18 + Nlv18) Clv18) → Set.ncard {jlv18 : ℕ | jlv18 < Clv18.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv18x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.Ico Nlv18 (Nlv18 + Nlv18))).getD ilv18x3 0 = 0) ∨ (∀ hlv18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.range Nlv18)).getD hlv18 0 = 0))} ≤ mlv18 → (∀ plv18x1 llv18x1 : Fin Nlv18, Ilv18 plv18x1 llv18x1 → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 (fun klv18x1 => decide (klv18x1 = Fin.castAdd Nlv18 plv18x1 ∨ klv18x1 = Fin.natAdd Nlv18 llv18x1)) = true) → (∀ zlv18 : Fin (Nlv18 + Nlv18) → Bool, (Finset.univ.filter (fun llv18x2 : Fin Nlv18 => zlv18 (Fin.natAdd Nlv18 llv18x2) = true)).card ≤ klv18 → (¬ ∃ plv18x2 llv18x3 : Fin Nlv18, Ilv18 plv18x2 llv18x3 ∧ zlv18 (Fin.castAdd Nlv18 plv18x2) = true ∧ zlv18 (Fin.natAdd Nlv18 llv18x3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 zlv18 = false) → (∀ dlv18 < mlv18, 1 ≤ Rlv18 dlv18 ∧ Rlv18 dlv18 ≤ qlv18) → (∀ dlv18x1 elv18x1 : ℕ, dlv18x1 + elv18x1 = mlv18 → 2 ^ elv18x1 + dlv18x1 ≤ klv18 ∧ ∑ ilv18 ∈ Finset.range dlv18x1, (1 + Rlv18 ilv18 * (qlv18 + 1)) < Nlv18) → (∀ dlv18x2 elv18x2 : ℕ, dlv18x2 + elv18x2 + 1 = mlv18 → (alv18 : ℤ) * max ((Rlv18 dlv18x2 : ℤ) * max (2 * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ≤ (clv18 : ℤ) * ((Rlv18 dlv18x2 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1)) * ((Nlv18 : ℤ) - ∑ ilv18x1 ∈ Finset.range dlv18x2, (1 + (Rlv18 ilv18x1 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (dlv18x2 : ℤ)))) → (alv18 : ℤ) * max ((qlv18 : ℤ) * max (2 * ((klv18 : ℤ) - (mlv18 : ℤ))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ))) ≤ (clv18 : ℤ) * ((qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ)) * ((Nlv18 : ℤ) - ∑ ilv18x2 ∈ Finset.range mlv18, (1 + (Rlv18 ilv18x2 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (mlv18 : ℤ))) → alv18 ≤ clv18 * Clv18.size) → (∀ (N102 : ℕ) (C102 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C102 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N102 + N102) C102 → Set.ncard {j102 : ℕ | j102 < C102.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C102 j102).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i102 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C102 j102).inputs, (C102.lineDegrees (N102 + N102) (Finset.Ico N102 (N102 + N102))).getD i102 0 = 0) ∨ (∀ h102 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C102 j102).inputs, (C102.lineDegrees (N102 + N102) (Finset.range N102)).getD h102 0 = 0))} ≤ 7 → (∃ z102 z102a : Fin (N102 + N102) → Bool, PEqualNP.MetaComplexity.circuitFun (N102 + N102) C102 z102 ≠ PEqualNP.MetaComplexity.circuitFun (N102 + N102) C102 z102a) → ∃ D102 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g102 ∈ D102.gates, (g102.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g102.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g102.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N102 + N102) D102) ∧ Set.ncard {j102a : ℕ | j102a < D102.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D102 j102a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i102a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D102 j102a).inputs, (D102.lineDegrees (N102 + N102) (Finset.Ico N102 (N102 + N102))).getD i102a 0 = 0) ∨ (∀ h102a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D102 j102a).inputs, (D102.lineDegrees (N102 + N102) (Finset.range N102)).getD h102a 0 = 0))} ≤ 7 ∧ D102.size ≤ C102.size ∧ PEqualNP.MetaComplexity.circuitFun (N102 + N102) D102 = PEqualNP.MetaComplexity.circuitFun (N102 + N102) C102) → (∀ qsc7 : ℕ, 200 ≤ qsc7 → qsc7 < 3000 → ∃ Rsc7 : ℕ → ℕ, ((∀ dsc7 < 7, 1 ≤ Rsc7 dsc7 ∧ Rsc7 dsc7 ≤ qsc7) ∧ (∀ dsc7x1 esc7x1 : ℕ, dsc7x1 + esc7x1 = 7 → 2 ^ esc7x1 + dsc7x1 ≤ qsc7 ∧ ∑ isc7 ∈ Finset.range dsc7x1, (1 + Rsc7 isc7 * (qsc7 + 1)) < (qsc7 ^ 2 + qsc7 + 1)) ∧ (∀ dsc7x2 esc7x2 : ℕ, dsc7x2 + esc7x2 + 1 = 7 → ((qsc7 ^ 2 + qsc7 + 1) * qsc7 : ℤ) * max ((Rsc7 dsc7x2 : ℤ) * max (2 * ((qsc7 : ℤ) + 1 - (dsc7x2 : ℤ) - 2 ^ (esc7x2 + 1))) ((qsc7 : ℤ) + 1)) (3 * (qsc7 : ℤ) * ((qsc7 : ℤ) + 1 - (dsc7x2 : ℤ) - 2 ^ (esc7x2 + 1))) ≤ (100 : ℤ) * ((Rsc7 dsc7x2 : ℤ) * ((qsc7 : ℤ) + 1 - (dsc7x2 : ℤ) - 2 ^ (esc7x2 + 1)) * (((qsc7 ^ 2 + qsc7 + 1) : ℤ) - ∑ isc7x1 ∈ Finset.range dsc7x2, (1 + (Rsc7 isc7x1 : ℤ) * ((qsc7 : ℤ) + 1))) * ((qsc7 : ℤ) - (dsc7x2 : ℤ)))) ∧ ((qsc7 ^ 2 + qsc7 + 1) * qsc7 : ℤ) * max ((qsc7 : ℤ) * max (2 * ((qsc7 : ℤ) - (7 : ℤ))) ((qsc7 : ℤ) + 1)) (3 * (qsc7 : ℤ) * ((qsc7 : ℤ) - (7 : ℤ))) ≤ (100 : ℤ) * ((qsc7 : ℤ) * ((qsc7 : ℤ) - (7 : ℤ)) * (((qsc7 ^ 2 + qsc7 + 1) : ℤ) - ∑ isc7x2 ∈ Finset.range 7, (1 + (Rsc7 isc7x2 : ℤ) * ((qsc7 : ℤ) + 1))) * ((qsc7 : ℤ) - (7 : ℤ))))) → (∀ (qta7 : ℕ) (Rta7 : ℕ → ℕ), 3000 ≤ qta7 → Rta7 = (fun dta7 : ℕ => [41, 89, 49, 111, 131, 33, 247].getD dta7 0 * qta7 / [500, 1000, 500, 1000, 1000, 200, 1000].getD dta7 1) → ((∀ dta7x1 < 7, 1 ≤ Rta7 dta7x1 ∧ Rta7 dta7x1 ≤ qta7) ∧ (∀ dta7x2 eta7x1 : ℕ, dta7x2 + eta7x1 = 7 → 2 ^ eta7x1 + dta7x2 ≤ qta7 ∧ ∑ ita7 ∈ Finset.range dta7x2, (1 + Rta7 ita7 * (qta7 + 1)) < (qta7 ^ 2 + qta7 + 1)) ∧ (∀ dta7x3 eta7x2 : ℕ, dta7x3 + eta7x2 + 1 = 7 → ((qta7 ^ 2 + qta7 + 1) * qta7 : ℤ) * max ((Rta7 dta7x3 : ℤ) * max (2 * ((qta7 : ℤ) + 1 - (dta7x3 : ℤ) - 2 ^ (eta7x2 + 1))) ((qta7 : ℤ) + 1)) (3 * (qta7 : ℤ) * ((qta7 : ℤ) + 1 - (dta7x3 : ℤ) - 2 ^ (eta7x2 + 1))) ≤ (100 : ℤ) * ((Rta7 dta7x3 : ℤ) * ((qta7 : ℤ) + 1 - (dta7x3 : ℤ) - 2 ^ (eta7x2 + 1)) * (((qta7 ^ 2 + qta7 + 1) : ℤ) - ∑ ita7x1 ∈ Finset.range dta7x3, (1 + (Rta7 ita7x1 : ℤ) * ((qta7 : ℤ) + 1))) * ((qta7 : ℤ) - (dta7x3 : ℤ)))) ∧ ((qta7 ^ 2 + qta7 + 1) * qta7 : ℤ) * max ((qta7 : ℤ) * max (2 * ((qta7 : ℤ) - (7 : ℤ))) ((qta7 : ℤ) + 1)) (3 * (qta7 : ℤ) * ((qta7 : ℤ) - (7 : ℤ))) ≤ (100 : ℤ) * ((qta7 : ℤ) * ((qta7 : ℤ) - (7 : ℤ)) * (((qta7 ^ 2 + qta7 + 1) : ℤ) - ∑ ita7x2 ∈ Finset.range 7, (1 + (Rta7 ita7x2 : ℤ) * ((qta7 : ℤ) + 1))) * ((qta7 : ℤ) - (7 : ℤ))))) → ∀ (qlv19 Nlv19 : ℕ) (Ilv19 : Fin Nlv19 → Fin Nlv19 → Prop) [DecidableRel Ilv19] (Clv19 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ qlv19 → Nlv19 = qlv19 ^ 2 + qlv19 + 1 → (∀ llv19 : Fin Nlv19, (Finset.univ.filter (fun plv19 => Ilv19 plv19 llv19)).card = qlv19 + 1) → (∀ palv19 pblv19 : Fin Nlv19, palv19 ≠ pblv19 → ∃! lblv19 : Fin Nlv19, Ilv19 palv19 lblv19 ∧ Ilv19 pblv19 lblv19) → PEqualNP.MetaComplexity.Monotone2 Clv19 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv19 + Nlv19) Clv19 → Set.ncard {jlv19 : ℕ | jlv19 < Clv19.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv19 jlv19).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv19 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv19 jlv19).inputs, (Clv19.lineDegrees (Nlv19 + Nlv19) (Finset.Ico Nlv19 (Nlv19 + Nlv19))).getD ilv19 0 = 0) ∨ (∀ hlv19 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv19 jlv19).inputs, (Clv19.lineDegrees (Nlv19 + Nlv19) (Finset.range Nlv19)).getD hlv19 0 = 0))} ≤ 7 → (∀ plv19x1 llv19x1 : Fin Nlv19, Ilv19 plv19x1 llv19x1 → PEqualNP.MetaComplexity.circuitFun (Nlv19 + Nlv19) Clv19 (fun klv19 => decide (klv19 = Fin.castAdd Nlv19 plv19x1 ∨ klv19 = Fin.natAdd Nlv19 llv19x1)) = true) → (∀ zlv19 : Fin (Nlv19 + Nlv19) → Bool, (Finset.univ.filter (fun llv19x2 : Fin Nlv19 => zlv19 (Fin.natAdd Nlv19 llv19x2) = true)).card ≤ qlv19 → (¬ ∃ plv19x2 llv19x3 : Fin Nlv19, Ilv19 plv19x2 llv19x3 ∧ zlv19 (Fin.castAdd Nlv19 plv19x2) = true ∧ zlv19 (Fin.natAdd Nlv19 llv19x3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv19 + Nlv19) Clv19 zlv19 = false) → Nlv19 * qlv19 ≤ 100 * Clv19.size := by
  intro H1 H2 H3 H4 H5 q N I instI C hq hN hl hu hM hR hX hA hRj
  rcases Nat.lt_or_ge q 200 with hlt | hge
  · exact PEqualNP.Outside.L_meta_1845.small N q C.size hN hlt (H1 q N I C hq hN hl hu hM hR hA hRj)
  · subst hN
    have hpos : 0 < q ^ 2 + q + 1 := Nat.succ_pos _
    have hc := hl ⟨0, hpos⟩
    have hne : (Finset.univ.filter (fun p0 => I p0 ⟨0, hpos⟩)).Nonempty := by
      rw [← Finset.card_pos, hc]; exact Nat.succ_pos _
    obtain ⟨p0, hp0m⟩ := hne
    have hp0 : I p0 ⟨0, hpos⟩ := (Finset.mem_filter.mp hp0m).2
    have e1 := hA p0 ⟨0, hpos⟩ hp0
    have e2 := hRj (fun _ => false) (by simp) (by simp)
    obtain ⟨D, ⟨hDg, hDR⟩, hDX, hDs, hDf⟩ := H3 (q ^ 2 + q + 1) C hM hR hX
      ⟨_, _, fun h => absurd (e1.symm.trans (h.trans e2)) (by decide)⟩
    rcases Nat.lt_or_ge q 3000 with h3 | h3
    · obtain ⟨R, hRa, hRb, hRc, hRd⟩ := H4 q hge h3
      have key := H2 q (q ^ 2 + q + 1) q 7 ((q ^ 2 + q + 1) * q) 100 I D R hq rfl hl hu (by omega) le_rfl
        ⟨hDg, hDR⟩ hDX
        (by intro p l h; rw [hDf]; exact hA p l h)
        (by intro z h1 h2; rw [hDf]; exact hRj z h1 h2)
        hRa hRb
        (by
          intro d e hde
          have h7 := hRc d e hde
          push_cast at h7 ⊢
          exact h7)
        (by
          push_cast at hRd ⊢
          exact hRd)
      exact le_trans key (Nat.mul_le_mul_left _ hDs)
    · obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℕ, R = (fun dta7 : ℕ => [41, 89, 49, 111, 131, 33, 247].getD dta7 0 * q / [500, 1000, 500, 1000, 1000, 200, 1000].getD dta7 1) := ⟨_, rfl⟩
      obtain ⟨hRa, hRb, hRc, hRd⟩ := H5 q R h3 hRdef
      have key := H2 q (q ^ 2 + q + 1) q 7 ((q ^ 2 + q + 1) * q) 100 I D R hq rfl hl hu (by omega) le_rfl
        ⟨hDg, hDR⟩ hDX
        (by intro p l h; rw [hDf]; exact hA p l h)
        (by intro z h1 h2; rw [hDf]; exact hRj z h1 h2)
        hRa hRb
        (by
          intro d e hde
          have h7 := hRc d e hde
          push_cast at h7 ⊢
          exact h7)
        (by
          push_cast at hRd ⊢
          exact hRd)
      exact le_trans key (Nat.mul_le_mul_left _ hDs)
