import Mathlib
import PEqualNP.Defs

-- Cut: single output to multi output, then the classical bound for Boolean sums, in its two
-- classical halves.
-- h1 (transfer, the open core): a monotone circuit of least size for the bipartite graph
-- function f = OR over edges ij of (x_i AND y_j) gives, at linear cost, one monotone circuit
-- with a wire for each neighbourhood sum of one side: the sums S_i(y) = OR of y_j over the
-- neighbours j of the left vertex i, or the sums T_j(x) = OR of x_i over the neighbours i of
-- the right vertex j.
-- h2 (AND gates do not help; Lamagna and Savage, Tarjan: Boolean sums any two of which share
-- at most one variable): a monotone circuit for the left sums of a graph with no 4-cycle can
-- be replaced, at linear cost, by a circuit of OR gates only.
-- h3 (Nechiporuk: OR circuits): OR circuits for these sums cannot share a gate between two
-- sums except on single variables, so they need about |E| gates.
-- The proof passes to a least circuit, and applies h2 and h3 to the transposed graph when h1
-- gives the right sums (the edge count is the same on both sides).

theorem PEqualNP.Outside.R_meta_1999_103 (h1 : ∃ (c : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → x9.size ≤ x10.size) → PEqualNP.CircuitLowerBounds.JointSizeAtMost Set.univ (fun (x13 : Fin x2) (x12 : Fin x3 → Bool) => Decidable.decide (∃ (x14 : Fin x3), x4 x13 x14 ∧ x12 x14 = Bool.true)) Finset.univ (c * (x9.size + (1 : ℕ))) ∨ PEqualNP.CircuitLowerBounds.JointSizeAtMost Set.univ (fun (x14 : Fin x3) (x11 : Fin x2 → Bool) => Decidable.decide (∃ (x13 : Fin x2), x4 x13 x14 ∧ x11 x13 = Bool.true)) Finset.univ (c * (x9.size + (1 : ℕ))))
    (h2 : ∃ (c : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (s : ℕ), PEqualNP.CircuitLowerBounds.JointSizeAtMost Set.univ (fun (x13 : Fin x2) (x12 : Fin x3 → Bool) => Decidable.decide (∃ (x14 : Fin x3), x4 x13 x14 ∧ x12 x14 = Bool.true)) Finset.univ s → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Fin x2 → ℕ), (∀ g ∈ x9.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ (2 : ℕ)) ∧ x9.size ≤ c * (s + (1 : ℕ)) ∧ PEqualNP.CircuitLowerBounds.JointComputes Set.univ (fun (x13 : Fin x2) (x12 : Fin x3 → Bool) => Decidable.decide (∃ (x14 : Fin x3), x4 x13 x14 ∧ x12 x14 = Bool.true)) Finset.univ x9 x10)
    (h3 : ∃ (c : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Fin x2 → ℕ), (∀ g ∈ x9.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ (2 : ℕ)) → PEqualNP.CircuitLowerBounds.JointComputes Set.univ (fun (x13 : Fin x2) (x12 : Fin x3 → Bool) => Decidable.decide (∃ (x14 : Fin x3), x4 x13 x14 ∧ x12 x14 = Bool.true)) Finset.univ x9 x10 → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ c * (x9.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  obtain ⟨c3, hc3⟩ := h3
  refine ⟨c3 * (c2 * (c1 + 1) + 1), ?_⟩
  intro x2 x3 x4 x5 hL hR hC4 C hmono hfun
  -- a circuit of least size computing the same function
  have hex : ∃ s : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), D.eval (List.ofFn x11 ++ List.ofFn x12) =
        Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧
          x12 x14 = Bool.true)) ∧ D.size = s :=
    ⟨C.size, C, hmono, hfun, rfl⟩
  obtain ⟨D, hDm, hDf, hDs⟩ := @Nat.find_spec _ (Classical.decPred _) hex
  have hDmin : ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x10 →
      (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) =
        Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧
          x12 x14 = Bool.true)) → D.size ≤ x10.size := by
    intro D' h1' h2'
    rw [hDs]
    exact @Nat.find_min' _ (Classical.decPred _) hex _ ⟨D', h1', h2', rfl⟩
  have hDC : D.size ≤ C.size := hDmin C hmono hfun
  -- the edge count is the same from both sides
  have hdc : ∑ x12 : Fin x3, (Finset.filter (Function.swap x4 x12) Finset.univ).card =
      ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  -- the transposed graph has no 4-cycle either
  have hC4' : ∀ (x8 x9 : Fin x3) (x10 x11 : Fin x2), Function.swap x4 x8 x10 →
      Function.swap x4 x9 x10 → Function.swap x4 x8 x11 → Function.swap x4 x9 x11 →
      x8 = x9 ∨ x10 = x11 := by
    intro a b u v hau hbu hav hbv
    exact (hC4 u v a b hau hav hbu hbv).symm
  have key : ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤
      c3 * (c2 * (c1 * (D.size + 1) + 1) + 1) := by
    rcases hc1 x2 x3 x4 hL hR hC4 D hDm hDf hDmin with hJ | hJ
    · obtain ⟨E, out, hEor, hEsize, hEcomp⟩ := hc2 x2 x3 x4 hL hR hC4 _ hJ
      have h3' := hc3 x2 x3 x4 hL hR hC4 E out hEor hEcomp
      exact h3'.trans (Nat.mul_le_mul_left c3 (Nat.add_le_add_right hEsize 1))
    · obtain ⟨E, out, hEor, hEsize, hEcomp⟩ :=
        @hc2 x3 x2 (Function.swap x4) (fun a b => x5 b a) hR hL hC4' _ hJ
      have h3' := @hc3 x3 x2 (Function.swap x4) (fun a b => x5 b a) hR hL hC4' E out hEor hEcomp
      exact (le_of_eq hdc.symm).trans
        (h3'.trans (Nat.mul_le_mul_left c3 (Nat.add_le_add_right hEsize 1)))
  have e1 : c1 * (D.size + 1) ≤ c1 * (C.size + 1) :=
    Nat.mul_le_mul_left c1 (Nat.add_le_add_right hDC 1)
  have e2 : c2 * (c1 * (D.size + 1) + 1) ≤ c2 * (c1 * (C.size + 1) + 1) :=
    Nat.mul_le_mul_left c2 (Nat.add_le_add_right e1 1)
  have e3 : (c2 * (c1 + 1) + 1) * (C.size + 1) =
      c2 * (c1 * (C.size + 1) + 1) + 1 + (c2 * C.size + C.size) := by ring
  have hA : c2 * (c1 * (D.size + 1) + 1) + 1 ≤ (c2 * (c1 + 1) + 1) * (C.size + 1) := by
    omega
  calc ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card
        ≤ c3 * (c2 * (c1 * (D.size + 1) + 1) + 1) := key
    _ ≤ c3 * ((c2 * (c1 + 1) + 1) * (C.size + 1)) := Nat.mul_le_mul_left c3 hA
    _ = c3 * (c2 * (c1 + 1) + 1) * (C.size + 1) := by ring
