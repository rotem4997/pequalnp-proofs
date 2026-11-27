import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Count edges assigned to a branching OR and one of its two operand positions.
theorem PEqualNP.Outside.R_meta_1735_7
    (branching : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (U : Finset (Sym2 (Fin n))), NoFourCycle G →
      (U.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
          (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v})).card ≤ 2 * C.size)
    (remaining : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ¬ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
          (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v})).card ≤ k * (C.size + 1)) :

    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k, hk⟩ := remaining
  refine ⟨2 + k, ?_⟩
  intro n G _ hg he C hl ht
  have h4 : NoFourCycle G := by
    intro a b hab
    by_contra hc
    rw [not_le] at hc
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hc
    rw [Finset.mem_filter] at hw1 hw2
    obtain ⟨-, ha1, hb1⟩ := hw1
    obtain ⟨-, ha2, hb2⟩ := hw2
    have e1 := G.ne_of_adj ha1
    have e2 := G.ne_of_adj hb1
    have e3 := G.ne_of_adj ha2
    have e4 := G.ne_of_adj hb2
    have hcyc : (SimpleGraph.Walk.cons ha1 (SimpleGraph.Walk.cons hb1.symm
        (SimpleGraph.Walk.cons hb2 (SimpleGraph.Walk.cons ha2.symm SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e4, hne, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm hab]
      · simp [e1, e3, hab, hne, Ne.symm e1, Ne.symm e2]
    have h5 := hg a _ hcyc
    simp at h5
  let P (e : Sym2 (Fin n)) := ∃ u v : Fin n, e = s(u, v) ∧
    ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
      (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧ orIn n C (opnd C h b) = {v}
  classical
  have hb : ((Ustar G C).filter P).card ≤ 2 * C.size := by
    refine (Finset.card_le_card ?_).trans (branching n G C (Ustar G C) h4)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  have hr : ((Ustar G C).filter (fun e => ¬ P e)).card ≤ k * (C.size + 1) := by
    refine (Finset.card_le_card ?_).trans (hk n G hg he C hl ht)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  calc
    (Ustar G C).card = ((Ustar G C).filter P).card + ((Ustar G C).filter (fun e => ¬ P e)).card :=
      (Finset.card_filter_add_card_filter_not (s := Ustar G C) P).symm
    _ ≤ 2 * C.size + k * (C.size + 1) := Nat.add_le_add hb hr
    _ ≤ 2 * (C.size + 1) + k * (C.size + 1) := Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    _ = (2 + k) * (C.size + 1) := (Nat.add_mul ..).symm
