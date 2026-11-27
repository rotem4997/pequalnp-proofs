import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_801

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fan : FanInTwo ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem evalB : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    Circuit.eval ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b2 && b3) || (b3 && b4)) := by
  decide +kernel

theorem ofFnN (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

theorem edges (x : Fin 6 → Bool) :
    (((x 0 && x 1) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((h | h) | h) | h) | h) | h)
    · exact ⟨0, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 4, by decide, h.1, h.2⟩
    · exact ⟨0, 5, by decide, h.1, h.2⟩
    · exact ⟨1, 2, by decide, h.1, h.2⟩
    · exact ⟨2, 3, by decide, h.1, h.2⟩
    · exact ⟨3, 4, by decide, h.1, h.2⟩
  · rintro ⟨u, v, hm, hu, hv⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 1 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 4 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 5 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 1 := Fin.ext h1
      obtain rfl : v = 2 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 2 := Fin.ext h1
      obtain rfl : v = 3 := Fin.ext h2
      simp [hu, hv]
    · obtain rfl : u = 3 := Fin.ext h1
      obtain rfl : v = 4 := Fin.ext h2
      simp [hu, hv]

end PEqualNP.Outside.L_meta_801

theorem PEqualNP.Outside.L_meta_801 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨PEqualNP.Outside.L_meta_801.fan, rfl, fun x => ?_⟩
  rw [PEqualNP.Outside.L_meta_801.ofFnN, PEqualNP.Outside.L_meta_801.evalB]
  exact PEqualNP.Outside.L_meta_801.edges x
