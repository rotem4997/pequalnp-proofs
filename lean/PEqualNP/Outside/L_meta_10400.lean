import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10400

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [7, 8]⟩,
    ⟨.or, [6, 9]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [11, 12]⟩,
    ⟨.and, [10, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [15, 16]⟩,
    ⟨.and, [6, 9]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [14, 19]⟩, ⟨.and, [17, 18]⟩,
    ⟨.and, [7, 8]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [21, 24]⟩,
    ⟨.not, [25]⟩, ⟨.and, [20, 26]⟩], 27⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma eval_all : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    witness.eval (List.ofFn ![a0, a1, a2, a3, a4, a5]) = (fun x : Fin 6 → Bool => decide (((List.ofFn x).count true) = 3)) ![a0, a1, a2, a3, a4, a5] := by
  decide

end PEqualNP.Outside.L_meta_10400

theorem PEqualNP.Outside.L_meta_10400 :
    PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide (((List.ofFn x).count true) = 3)) 23 := by
  open PEqualNP.Outside.L_meta_10400 PEqualNP.MetaComplexity in
  refine ⟨witness, by simp [FanInTwo, witness], by decide, ?_⟩
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact eval_all (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
