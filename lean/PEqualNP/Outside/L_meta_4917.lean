import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4917

open PEqualNP.CircuitLowerBounds

def circuit : Circuit := ⟨[
  ⟨.or, [26, 38]⟩,
  ⟨.or, [29, 41]⟩,
  ⟨.or, [32, 23]⟩,
  ⟨.or, [35, 26]⟩,
  ⟨.or, [38, 29]⟩,
  ⟨.or, [41, 32]⟩,
  ⟨.or, [23, 35]⟩,
  ⟨.or, [42, 41]⟩,
  ⟨.or, [43, 23]⟩,
  ⟨.or, [44, 26]⟩,
  ⟨.or, [45, 29]⟩,
  ⟨.or, [46, 32]⟩,
  ⟨.or, [47, 35]⟩,
  ⟨.or, [48, 38]⟩], 55⟩

lemma monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_4917

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_4917 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (14 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         x1.wires (List.ofFn x2) =           have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));           (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ) := by
  refine ⟨PEqualNP.Outside.L_meta_4917.circuit, PEqualNP.Outside.L_meta_4917.monotone, by decide, ?_⟩
  intro x
  simp [PEqualNP.Outside.L_meta_4917.circuit, PEqualNP.CircuitLowerBounds.Circuit.wires,
    PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ, Bool.or_assoc]
