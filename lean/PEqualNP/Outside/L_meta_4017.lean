import Mathlib
import PEqualNP.Defs

/-!
L-meta-4017.

The marking `d` is carried along every step of the relation: at an OR gate the mark of either
operand marks the gate, and at an AND gate whose other operand is true on the unit input the mark
of this operand marks the gate.  So a mark on the first wire of a chain reaches the output.
-/

namespace PEqualNP.Outside.L_meta_4017

lemma carry (R : ℕ → ℕ → Prop) (d : ℕ → Bool)
    (hstep : ∀ a b, R a b → d a = true → d b = true)
    (w o : ℕ) (hw : d w = true) (h : Relation.ReflTransGen R w o) : d o = true := by
  induction h with
  | refl => exact hw
  | tail _ hbc ih => exact hstep _ _ hbc ih

end PEqualNP.Outside.L_meta_4017

theorem PEqualNP.Outside.L_meta_4017 :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ)) (x4 : ℕ) (x5 : ℕ → Bool),   have x6 : List Bool := x2.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x3));   x5 x4 = Bool.true → (∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate) (x10 x11 : ℕ), x2.gates[x8]? = Option.some x9 → x9.inputs = [x10, x11] → (x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x8) = (x6.getD x10 Bool.false && x5 x11 || x5 x10 && x6.getD x11 Bool.false)) ∧ (x9.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x8) = (x5 x10 || x5 x11))) → Relation.ReflTransGen (x1 x2 x3) x4 x2.output → x5 x2.output = Bool.true := by
  intro R C i w d W hd hrule hreach
  refine PEqualNP.Outside.L_meta_4017.carry _ d ?_ w C.output hd hreach
  rintro a b ⟨k, g, c, rfl, hg, hin, hop⟩ ha
  rcases hin with hin | hin
  · have h := hrule k g a c hg hin
    rcases hop with hor | ⟨hand, hc⟩
    · rw [h.2 hor, ha]
      simp
    · have hc' : W.getD c false = true := hc
      rw [h.1 hand, ha, hc']
      simp
  · have h := hrule k g c a hg hin
    rcases hop with hor | ⟨hand, hc⟩
    · rw [h.2 hor, ha]
      simp
    · have hc' : W.getD c false = true := hc
      rw [h.1 hand, ha, hc']
      simp
