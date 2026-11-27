import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5018_1
    (hOther : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (a : Fin n) (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) →
      (∀ a b : Fin n, G.Adj a b → a ∉ A) →
      (∃ a b : Fin n, G.Adj a b) →
      (∀ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) → k ≤ T.card) →
      (∀ x : Fin n → Bool, f x = Bool.true ↔ (∃ a ∈ A, x a = Bool.true) ∨
        ∃ a b : Fin n, G.Adj a b ∧ x a = Bool.true ∧ x b = Bool.true) →
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
      ∀ v ∉ A, ∀ g : PEqualNP.CircuitLowerBounds.Gate,
        C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] →
        (∃ w : ℕ, w ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) ∧ w ≠ v.val ∧ w < n) →
        A.card + G.edgeSet.ncard + k ≤ C.size + 1)
    (hGateWires : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (a : Fin n) (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) →
      (∀ a b : Fin n, G.Adj a b → a ∉ A) →
      (∃ a b : Fin n, G.Adj a b) →
      (∀ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) → k ≤ T.card) →
      (∀ x : Fin n → Bool, f x = Bool.true ↔ (∃ a ∈ A, x a = Bool.true) ∨
        ∃ a b : Fin n, G.Adj a b ∧ x a = Bool.true ∧ x b = Bool.true) →
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
      ∀ v ∉ A, ∀ g : PEqualNP.CircuitLowerBounds.Gate,
        C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] →
        (∀ w : ℕ, w ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) → w = v.val ∨ n ≤ w) →
        A.card + G.edgeSet.ncard + k ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) → (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) → (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) → PEqualNP.MetaComplexity.FanInTwo x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 → (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) → (∃ x16 ∉ x4, (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x16) x6.gates).length = (1 : ℕ)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  intro n k G A f C hdeg hgirth hnoedge hedge hcover hspec hfan hfun hmin hread
  obtain ⟨v, hvA, hlen⟩ := hread
  obtain ⟨g, hfilter⟩ := List.length_eq_one_iff.mp hlen
  by_cases hcase : ∃ w : ℕ, w ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) ∧ w ≠ v.val ∧ w < n
  · exact hOther n k G A f C hdeg hgirth hnoedge hedge hcover hspec hfan hfun hmin v hvA g hfilter hcase
  · apply hGateWires n k G A f C hdeg hgirth hnoedge hedge hcover hspec hfan hfun hmin v hvA g hfilter
    intro w hw
    rcases eq_or_ne w v.val with rfl | hne
    · exact Or.inl rfl
    · rcases Nat.lt_or_ge w n with hlt | hge
      · exact absurd ⟨w, hw, hne, hlt⟩ hcase
      · exact Or.inr hge
