import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2438
open PEqualNP.CircuitLowerBounds

theorem snoc {n : ℕ} (f : Fin n → Bool) (v : Bool) :
    List.ofFn (fun i : Fin (n + 1) => Fin.lastCases v f i) = List.ofFn f ++ [v] := by
  rw [List.ofFn_succ']
  simp

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem step (gs : List Gate) (o a b : ℕ) (x : List Bool) :
    Circuit.eval ⟨⟨GateOp.or, [a, b]⟩ :: gs, o⟩ x
      = Circuit.eval ⟨gs, o⟩ (x ++ [x.getD a false || x.getD b false]) := by
  simp [Circuit.eval, Circuit.wires, GateOp.eval]

end PEqualNP.Outside.L_meta_2438

theorem PEqualNP.Outside.L_meta_2438 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x7 ∧           x7.size ≤ x4.size + (2 : ℕ) ∧             ∀ (x8 : Fin (42 : ℕ) → Bool),               have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 (0 : Fin (42 : ℕ)) || x8 x1) x8 x9;               x7.eval (List.ofFn x8) = x4.eval (List.ofFn fun (x10 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 x2 || x9 x3) x9 x10) := by
  intro x1 x2 x3 x4 hm _
  refine ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, (x1 : ℕ)]⟩ ::
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(x2 : ℕ), (x3 : ℕ)]⟩ :: x4.gates, x4.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact hm g hg
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x8
    have h0 : (List.ofFn x8).getD 0 false = x8 0 :=
      PEqualNP.Outside.L_meta_2438.getD_ofFn x8 0
    have h1 := PEqualNP.Outside.L_meta_2438.getD_ofFn x8 x1
    have e1 := PEqualNP.Outside.L_meta_2438.snoc x8 (x8 0 || x8 x1)
    have h2 := PEqualNP.Outside.L_meta_2438.getD_ofFn
      (fun x9 : Fin (42 + 1) => Fin.lastCases (x8 0 || x8 x1) x8 x9) x2
    have h3 := PEqualNP.Outside.L_meta_2438.getD_ofFn
      (fun x9 : Fin (42 + 1) => Fin.lastCases (x8 0 || x8 x1) x8 x9) x3
    rw [e1] at h2 h3
    show _ = x4.eval (List.ofFn fun (x10 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases ((fun x9 : Fin (42 + 1) => Fin.lastCases (x8 0 || x8 x1) x8 x9) x2 || (fun x9 : Fin (42 + 1) => Fin.lastCases (x8 0 || x8 x1) x8 x9) x3) (fun x9 : Fin (42 + 1) => Fin.lastCases (x8 0 || x8 x1) x8 x9) x10)
    rw [PEqualNP.Outside.L_meta_2438.snoc, e1, PEqualNP.Outside.L_meta_2438.step,
      PEqualNP.Outside.L_meta_2438.step, h0, h1, h2, h3]
