import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- Split the junk edges by a witness with at most four leaves. Each operand of a top takes the
-- pair through an input, or through the two sides of one junk gate, or (when the other operand
-- holds the input a) through a junk gate k with a or b on one side that reaches, on its other
-- side, a junk gate h with the pair in its two sides.
-- The first part holds in every least top-form circuit; the second part is the open case:
-- the junk edges whose every witness has five or more leaves.
theorem PEqualNP.Outside.R_meta_3775_733
    (leaves : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ S : Finset (Sym2 (Fin n)), S ⊆ Ustar G C →
      (∀ e ∈ S, ∃ a b : Fin n, e = s(a, b) ∧ ∃ t ∈ tops G C, ∀ i : Fin 2,
        a ∈ side C t i ∨ b ∈ side C t i ∨ ∃ k ∈ junk G C, OrReaches n C (opnd C t i) k ∧
          ((∀ j : Fin 2, a ∈ side C k j ∨ b ∈ side C k j) ∨
            ∃ j : Fin 2, a ∈ side C t ((1 : Fin 2) - i) ∧ (a ∈ side C k j ∨ b ∈ side C k j) ∧
              ∃ h ∈ junk G C, OrReaches n C (opnd C k ((1 : Fin 2) - j)) h ∧
                ∀ m : Fin 2, a ∈ side C h m ∨ b ∈ side C h m)) →
      S.card ≤ c * (C.size + 1))
    (rest : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C → 2 ≤ (junk G C).card →
      (∃ x ∈ junk G C, ∃ y ∈ junk G C, InCone n C x y) →
      (¬ ∃ (X : Finset (Fin n)) (M : Finset (Sym2 (Fin n))), X.card ≤ 4 ∧ M.card ≤ C.size + 1 ∧
        ∀ e ∈ Ustar G C, e ∈ M ∨ ∃ a b : Fin n, e = s(a, b) ∧
          ((∃ c ∈ X, G.Adj a c) ∨ ∃ c ∈ X, G.Adj b c)) →
      ∀ S : Finset (Sym2 (Fin n)), S ⊆ Ustar G C →
      (∀ e ∈ S, ¬ ∃ a b : Fin n, e = s(a, b) ∧ ∃ t ∈ tops G C, ∀ i : Fin 2,
        a ∈ side C t i ∨ b ∈ side C t i ∨ ∃ k ∈ junk G C, OrReaches n C (opnd C t i) k ∧
          ((∀ j : Fin 2, a ∈ side C k j ∨ b ∈ side C k j) ∨
            ∃ j : Fin 2, a ∈ side C t ((1 : Fin 2) - i) ∧ (a ∈ side C k j ∨ b ∈ side C k j) ∧
              ∃ h ∈ junk G C, OrReaches n C (opnd C k ((1 : Fin 2) - j)) h ∧
                ∀ m : Fin 2, a ∈ side C h m ∨ b ∈ side C h m)) →
      S.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, h1⟩ := leaves
  obtain ⟨c2, h2⟩ := rest
  refine ⟨c1 + c2, ?_⟩
  intro n G _ hg he C hl ht hj hn hc
  have key : ∀ W : Sym2 (Fin n) → Prop,
      (∀ S : Finset (Sym2 (Fin n)), S ⊆ Ustar G C → (∀ e ∈ S, W e) →
        S.card ≤ c1 * (C.size + 1)) →
      (∀ S : Finset (Sym2 (Fin n)), S ⊆ Ustar G C → (∀ e ∈ S, ¬ W e) →
        S.card ≤ c2 * (C.size + 1)) →
      (Ustar G C).card ≤ (c1 + c2) * (C.size + 1) := by
    intro W p1 p2
    classical
    have b1 := p1 ((Ustar G C).filter W) (Finset.filter_subset _ _)
      (fun e hm => (Finset.mem_filter.mp hm).2)
    have b2 := p2 ((Ustar G C).filter (fun e => ¬ W e)) (Finset.filter_subset _ _)
      (fun e hm => (Finset.mem_filter.mp hm).2)
    have hs := Finset.card_filter_add_card_filter_not (s := Ustar G C) W
    have hm : (c1 + c2) * (C.size + 1) = c1 * (C.size + 1) + c2 * (C.size + 1) :=
      Nat.add_mul _ _ _
    omega
  exact key _ (h1 n G hg C hl ht) (h2 n G hg he C hl ht hj hn hc)
