import Mathlib
import PEqualNP.Defs

-- A cut of the open core along the number of junk AND gates.
-- baseFewJunk is the settled end of the induction: at most one junk AND gate.
-- amortisedStep is the surgery that drops one junk AND gate from a least top-form
-- circuit at a cost of a constant number of carried edges, keeping the size.
theorem PEqualNP.Outside.R_meta_5266_1
    (baseFewJunk : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C → (PEqualNP.TopForm.junk G C).card ≤ (1 : ℕ) →
      {e ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn n C (n + h)).card ∧ (∀ w ∈ PEqualNP.TopForm.orIn n C (n + h), G.Adj u w) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C h b) = {v}) ∧ ∃ u ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C, e ∈ PEqualNP.TopForm.gammaE G C u ∧ ∀ v ∈ PEqualNP.TopForm.side C u (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side C u (1 : Fin (2 : ℕ)), v ∉ e}.card ≤ k * (C.size + (1 : ℕ)))
    (amortisedStep : ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (Bad : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin n))),
      (∀ (C : PEqualNP.CircuitLowerBounds.Circuit), Bad C =
        {e ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn n C (n + h)).card ∧ (∀ w ∈ PEqualNP.TopForm.orIn n C (n + h), G.Adj u w) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C h b) = {v}) ∧ ∃ u ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C, e ∈ PEqualNP.TopForm.gammaE G C u ∧ ∀ v ∈ PEqualNP.TopForm.side C u (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side C u (1 : Fin (2 : ℕ)), v ∉ e}) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C → (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
        PEqualNP.TopForm.TopForm G D ∧ D.size = C.size ∧
        (PEqualNP.TopForm.junk G D).card < (PEqualNP.TopForm.junk G C).card ∧
        (Bad C).card ≤ (Bad D).card + c) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ∀ x12 ∈ PEqualNP.TopForm.side x7 x11 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x11 (1 : Fin (2 : ℕ)), x12 ∉ x10}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k, hk⟩ := baseFewJunk
  obtain ⟨c, hc⟩ := amortisedStep
  refine ⟨k + c, ?_⟩
  intro n G inst girth ne C least top
  have key : ∀ m : ℕ, ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (PEqualNP.TopForm.junk G C).card ≤ m →
      {e ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn n C (n + h)).card ∧ (∀ w ∈ PEqualNP.TopForm.orIn n C (n + h), G.Adj u w) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C h b) = {v}) ∧ ∃ u ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C, e ∈ PEqualNP.TopForm.gammaE G C u ∧ ∀ v ∈ PEqualNP.TopForm.side C u (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side C u (1 : Fin (2 : ℕ)), v ∉ e}.card ≤ k * (C.size + (1 : ℕ)) + c * m := by
    intro m
    induction m with
    | zero =>
      intro C hl ht hj
      exact (hk n G girth ne C hl ht (hj.trans (Nat.zero_le 1))).trans (Nat.le_add_right _ _)
    | succ m ih =>
      intro C hl ht hj
      by_cases h2 : (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card
      · obtain ⟨D, hl', ht', hs', hj', hb⟩ :=
          hc n G (fun C => {e ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn n C (n + h)).card ∧ (∀ w ∈ PEqualNP.TopForm.orIn n C (n + h), G.Adj u w) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C h b) = {v}) ∧ ∃ u ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C, e ∈ PEqualNP.TopForm.gammaE G C u ∧ ∀ v ∈ PEqualNP.TopForm.side C u (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side C u (1 : Fin (2 : ℕ)), v ∉ e}) (fun _ => rfl) girth ne C hl ht h2
        have hrec := ih D hl' ht' (Nat.lt_succ_iff.mp (lt_of_lt_of_le hj' hj))
        rw [hs'] at hrec
        have e : k * (C.size + (1 : ℕ)) + c * (m + 1)
            = (k * (C.size + (1 : ℕ)) + c * m) + c := by ring
        rw [e]
        exact hb.trans (Nat.add_le_add_right hrec c)
      · exact (hk n G girth ne C hl ht (Nat.le_of_lt_succ (Nat.not_le.mp h2))).trans (Nat.le_add_right _ _)
  have hjs : (PEqualNP.TopForm.junk G C).card ≤ C.size := by
    have hsub : PEqualNP.TopForm.junk G C ⊆ Finset.range C.gates.length :=
      Finset.filter_subset _ _
    have hcard : (Finset.range C.gates.length).card = C.size := Finset.card_range _
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)
  refine (key C.size C least top hjs).trans ?_
  have e : (k + c) * (C.size + (1 : ℕ))
      = k * (C.size + (1 : ℕ)) + (c * C.size + c) := by ring
  rw [e]
  exact Nat.add_le_add_left (Nat.le_add_right _ _) _
