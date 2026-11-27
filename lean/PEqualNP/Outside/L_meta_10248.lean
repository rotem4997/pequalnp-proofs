import Mathlib
import PEqualNP.Defs

-- A circuit of 29 AND, OR and NOT gates for the test whether the number of true inputs among
-- six is divisible by three. Each half of three inputs gives its count modulo three, one-hot:
-- r0 is none or all, r1 is exactly one, r2 is exactly two. The output is
-- (r0 and s0) or (r1 and s2) or (r2 and s1). Correctness is checked on all 64 inputs.

namespace PEqualNP.Outside.L_meta_10248

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [8, 2]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [12, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [7, 14]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [11, 16]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [18, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [20, 5]⟩, ⟨GateOp.and, [5, 18]⟩, ⟨GateOp.or, [20, 22]⟩, ⟨GateOp.not, [19]⟩, ⟨GateOp.or, [24, 21]⟩, ⟨GateOp.not, [23]⟩, ⟨GateOp.and, [19, 26]⟩, ⟨GateOp.not, [21]⟩, ⟨GateOp.and, [23, 28]⟩, ⟨GateOp.and, [13, 25]⟩, ⟨GateOp.and, [15, 29]⟩, ⟨GateOp.and, [17, 27]⟩, ⟨GateOp.or, [30, 31]⟩, ⟨GateOp.or, [33, 32]⟩], 34⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

lemma okOp_mem (o : GateOp) (h : okOp o = true) :
    o ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
  cases o <;> simp_all [okOp]

lemma all_ok : ∀ g ∈ circ.gates, okOp g.op = true ∧ g.inputs.length ≤ 2 := by
  decide

lemma fan : FanInTwo circ := fun g hg => ⟨okOp_mem _ (all_ok g hg).1, (all_ok g hg).2⟩

lemma size_le : circ.size ≤ 37 := by
  decide

lemma correct : ∀ x : Fin 6 → Bool,
    circ.eval (List.ofFn x) = decide (((List.ofFn x).count true) % 3 = 0) := by
  decide

end PEqualNP.Outside.L_meta_10248

theorem PEqualNP.Outside.L_meta_10248 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide (((List.ofFn x).count true) % 3 = 0)) 37 :=
  ⟨PEqualNP.Outside.L_meta_10248.circ, PEqualNP.Outside.L_meta_10248.fan,
    PEqualNP.Outside.L_meta_10248.size_le, PEqualNP.Outside.L_meta_10248.correct⟩
