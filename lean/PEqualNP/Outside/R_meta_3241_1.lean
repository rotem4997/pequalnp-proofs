import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3241_1
    (h1 : ∀ (n : ℕ) (C C' : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → C.output < n + C.gates.length → PEqualNP.CircuitMoves.Lift n C C' → PEqualNP.TopForm.IsAO2 n C' ∧ C'.output < n + C'.gates.length ∧ C'.size = C.size ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C)
    (h2 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → C.output < n + C.gates.length → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift n) C C' ∧ (∀ m < C'.gates.length, ∀ a b : ℕ, C'.gates[m]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ → (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C' b → PEqualNP.CircuitMoves.WireBelowOutput n C' a) ∧ (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n C' a → PEqualNP.CircuitMoves.WireBelowOutput n C' b)))
    (h3 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 (x1 + x2) C → C.output < x1 + x2 + C.gates.length → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) C x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → (∀ m < C.gates.length, ∀ a b : ℕ, C.gates[m]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ → (x1 + x2 ≤ b → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) C b → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) C a) ∧ (x1 + x2 ≤ a → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) C a → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) C b)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < (x1 + x2)) ∨ x1 ≤ x11.1 ∧ x11.1 < (x1 + x2) ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   let x6 : ℕ := x1 + x2;   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 x6 x5 → (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size := by
  intro x1 x2 x3 x4 x5 x6 hno hC hF
  by_cases hout : x5.output < x1 + x2 + x5.gates.length
  · obtain ⟨C', hR, hNF⟩ := h2 (x1 + x2) x5 hC hout
    have key : ∀ C'' : PEqualNP.CircuitLowerBounds.Circuit,
        Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift (x1 + x2)) x5 C'' →
        PEqualNP.TopForm.IsAO2 (x1 + x2) C'' ∧ C''.output < x1 + x2 + C''.gates.length ∧
        C''.size = x5.size ∧
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) C'' =
          PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 := by
      intro C'' hR'
      induction hR' with
      | refl => exact ⟨hC, hout, rfl, rfl⟩
      | tail _ hL ih =>
        obtain ⟨a, b, c, d⟩ := ih
        obtain ⟨a', b', c', d'⟩ := h1 _ _ _ a b hL
        exact ⟨a', b', c'.trans c, d'.trans d⟩
    obtain ⟨a, b, c, d⟩ := key C' hR
    obtain ⟨L, hL1, hL2, hL3⟩ := h3 x1 x2 x3 C' hno a b (fun z => by rw [d]; exact hF z) hNF
    exact ⟨L, hL1, hL2, hL3.trans (le_of_eq c)⟩
  · have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
          w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp
        omega
    have hzero : ∀ z : Fin (x1 + x2) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 z = false := by
      intro z
      unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
        PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [List.getD_eq_default _ _ (by rw [hlen]; simp; omega)]
    have hnone : ∀ (p : Fin x1) (l : Fin x2), ¬ x3 p l := by
      intro p l hpl
      have h0 := hF (fun k => decide (k = Fin.castAdd x2 p ∨ k = Fin.natAdd x1 l))
      rw [hzero] at h0
      have : (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧
          decide (Fin.castAdd x2 x10 = Fin.castAdd x2 p ∨ Fin.castAdd x2 x10 = Fin.natAdd x1 l) = true ∧
          decide (Fin.natAdd x1 x11 = Fin.castAdd x2 p ∨ Fin.natAdd x1 x11 = Fin.natAdd x1 l) = true) :=
        ⟨p, l, hpl, by simp, by simp⟩
      exact absurd (decide_eq_true this) (by rw [← h0]; simp)
    refine ⟨[], by simp, fun p l => ⟨fun h => absurd h (hnone p l), by simp⟩, by simp⟩
