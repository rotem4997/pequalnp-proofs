import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Pinning an input turns each wire into a column of the restricted truth table.
-- Constant columns propagate through later gates and repeated columns can reuse an earlier wire.
theorem PEqualNP.Outside.R_meta_4117_17
    (compress : ∀ (n : ℕ) (C : Circuit) (v : Fin n),
      let V := Fin n
      let W := fun (i : ℕ) (x : V → Bool) =>
        PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update x v false)) i
      let dead := {j : ℕ | j < C.size ∧ (
        (∃ b : Bool, ∀ x, W (n+j) x = b) ∨ ∃ i < n+j, W (n+j) = W i)}
      FanInTwo C → (∃ x : V → Bool, circuitFun n C (Function.update x v false) = false) →
      ∃ s, s + dead.ncard ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s)
    (findFour : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let V := Fin n
      let gates := C.gates
      let reads := fun (i : ℕ) (g : Gate) =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
      let readers := fun v : V => gates.filter (reads v.val)
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → 7 ≤ G.egirth →
      (∀ u v, G.Adj u v → u ∉ A) → IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A, (readers v).length ≤ 3 ∧ ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length ≤ 1 ∧ ∀ g ∈ readers v, ∀ p : V, p ≠ v →
        g.inputs.Perm [v.val,p.val] → g.op ≠ .and ∧ g.op ≠ .or) →
      ∃ v ∉ A,
      let W := fun (i : ℕ) (x : V → Bool) =>
        PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update x v false)) i
      let dead := {j : ℕ | j < C.size ∧ (
        (∃ b : Bool, ∀ x, W (n+j) x = b) ∨ ∃ i < n+j, W (n+j) = W i)}
      4 ≤ dead.ncard) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20 := by
  intro n G inst A C f reads near readers degree girth marked _ minimal computes bound rare _
  obtain ⟨v, hv, four⟩ := findFour n G A C degree girth marked minimal computes bound rare
  have zero : circuitFun n C (Function.update (fun _ => false) v false) = false := by
    rw [computes]
    have eq : Function.update (fun _ : Fin n => false) v false = fun _ => false := by
      funext i
      by_cases h : i = v <;> simp [Function.update,h]
    rw [eq]
    change (decide (∃ a ∈ A, false = true) || decide (∃ u v, G.Adj u v ∧ false = true ∧ false = true)) = false
    simp
  obtain ⟨s, hs, cert⟩ := compress n C v minimal.1 ⟨_,zero⟩
  refine ⟨v, hv, s, le_trans (Nat.add_le_add_left four s) hs, ?_⟩
  simpa only [computes] using cert
