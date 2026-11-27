import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7557 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∃ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.not) →     ∀ (x3 : List ℕ),       PEqualNP.MetaComplexity.Monotone2 x1 →         x3.length ≤ (2 : ℕ) →           (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);             have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};             have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => (x1.wires (List.ofFn (x7 x9 x10))).getD x11 Bool.false) x3);             (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →             (63 : ℕ) ≤ x1.size := by
  intro x1 hnot x3 hmono _ _
  exfalso
  obtain ⟨g, hg, hop⟩ := hnot
  have h := (hmono g hg).1
  rw [hop] at h
  simp at h
