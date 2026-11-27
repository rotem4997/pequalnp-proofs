import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7382 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : DecidableRel x2.Adj) (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ⊆ x4ᶜ, (∀ x18 ∈ x16, ∀ x20 ∈ x16, ¬x2.Adj x18 x20) → x4ᶜ.card + (2 : ℕ) * x16.card ≤ (2 : ℕ) * {x19 ∉ x4 | (x7 x19).length = (2 : ℕ)}.card) → (¬∃ (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[(1 : ℕ)]? = Option.some x17) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  intro x1 x2 x3 x4 x5
  dsimp only
  intro hdeg hgirth hedge hex hfan hfun hmin hread hindep hone
  exfalso
  obtain ⟨a, b, hab⟩ := hex
  have ha : a ∉ x4 := hedge a b hab
  have h2 := (hread a ha).1
  have hlen : x5.gates.length ≤ 1 := by
    by_contra h
    push_neg at h
    exact hone ⟨x5.gates[1], List.getElem?_eq_getElem h⟩
  have h3 := List.length_filter_le (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains (a : ℕ)) x5.gates
  omega
