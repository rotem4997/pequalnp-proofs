import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8099

open PEqualNP.AndCount

-- Every gate true at fuel d leads to a gate whose two sides both meet U by bare variables.
theorem fuel_witness {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true →
      ∃ k : Fin C.size, (∃ v ∈ C.leftVars k, v ∈ U) ∧ (∃ v ∈ C.rightVars k, v ∈ U) := by
  intro d
  induction d with
  | zero =>
    intro i h
    simp [AndCountCircuit.gateValFuel] at h
  | succ d ih =>
    intro i h
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true,
      AndCountCircuit.sideTrue, decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := h
    rcases hl with hl | ⟨j, _, _, hj⟩
    · rcases hr with hr | ⟨j, _, _, hj⟩
      · exact ⟨i, hl, hr⟩
      · exact ih j hj
    · exact ih j hj

end PEqualNP.Outside.L_meta_8099

theorem PEqualNP.Outside.L_meta_8099 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : SimpleGraph (Fin x1)), x2.Computes x3 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) → ∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → ∃ (x10 : Fin x2.size), x7 ∈ x2.leftVars x10 ∧ x8 ∈ x2.rightVars x10 ∨ x8 ∈ x2.leftVars x10 ∧ x7 ∈ x2.rightVars x10 := by
  classical
  intro n C G hC hOut hDisj a b hab
  have hEv : C.eval {a, b} = true :=
    (hC {a, b}).mpr ⟨a, by simp, b, by simp, hab⟩
  rw [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq] at hEv
  rcases hEv with ⟨v, hv, _⟩ | ⟨j, _, hj⟩
  · rw [hOut] at hv
    simp at hv
  · obtain ⟨k, ⟨v, hvl, hvU⟩, ⟨w, hwr, hwU⟩⟩ :=
      PEqualNP.Outside.L_meta_8099.fuel_witness C {a, b} C.size j hj
    refine ⟨k, ?_⟩
    have hd := hDisj k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvU hwU
    rcases hvU with rfl | rfl <;> rcases hwU with rfl | rfl
    · exact absurd hwr (Finset.disjoint_left.mp hd hvl)
    · exact Or.inl ⟨hvl, hwr⟩
    · exact Or.inr ⟨hvl, hwr⟩
    · exact absurd hwr (Finset.disjoint_left.mp hd hvl)
