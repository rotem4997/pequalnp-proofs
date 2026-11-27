import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4891
open PEqualNP.CircuitLowerBounds



def tg (t : Bool × Fin 89 × Fin 89) : Gate :=
  ⟨if t.1 = true then GateOp.and else GateOp.or, [t.2.1.1, t.2.2.1]⟩

theorem tg_step (w : List Bool) (t : Bool × Fin 89 × Fin 89) :
    (tg t).op.eval ((tg t).inputs.map fun i => w.getD i false)
      = (bif t.1 then w.getD t.2.1.1 false && w.getD t.2.2.1 false
          else w.getD t.2.1.1 false || w.getD t.2.2.1 false) := by
  obtain ⟨b, p, q⟩ := t
  cases b <;> simp [tg, GateOp.eval]

end PEqualNP.Outside.L_meta_4891

open PEqualNP.Outside.L_meta_4891 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4891 : ∀ (x1 : Fin (63 : ℕ) → Bool) (x2 x3 : Fin (63 : ℕ) → Fin (89 : ℕ)), (∀ (x4 : Fin (63 : ℕ)), ↑(x2 x4) < (26 : ℕ) + ↑x4 ∧ ↑(x3 x4) < (26 : ℕ) + ↑x4 ∧ x2 x4 ≤ x3 x4) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = (63 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), x5.eval (List.ofFn x6) = (fun (x7 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x8 : List Bool) (x9 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false]) (List.ofFn x7) (List.ofFn fun (x8 : Fin (63 : ℕ)) => (x1 x8, x2 x8, x3 x8))).getD (88 : ℕ) Bool.false) x6 := by
  intro x1 x2 x3 _
  refine ⟨⟨(List.ofFn fun k : Fin 63 => (x1 k, x2 k, x3 k)).map tg, 88⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hg
    refine ⟨?_, ?_⟩
    · unfold tg
      split <;> simp
    · show ([t.2.1.1, t.2.2.1] : List ℕ).length ≤ 2
      simp
  · show ((List.ofFn fun k : Fin 63 => (x1 k, x2 k, x3 k)).map tg).length = 63
    simp
  · intro x
    show (((List.ofFn fun k : Fin 63 => (x1 k, x2 k, x3 k)).map tg).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD 88 false = _
    rw [List.foldl_map]
    congr 2
    funext w t
    rw [tg_step]
