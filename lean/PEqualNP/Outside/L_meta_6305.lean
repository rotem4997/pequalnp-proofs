import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6305

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

def lv (S : Finset (Fin 26)) (B : Finset (Fin 27)) : Finset (Fin 26) :=
  Finset.univ.filter (fun v => v.succ ∈ B ∨ ((0 : Fin 27) ∈ B ∧ v ∈ S))

def restr (C : AndCountCircuit 27) (S : Finset (Fin 26)) : AndCountCircuit 26 where
  size := C.size
  leftVars i := lv S (C.leftVars i)
  leftGates := C.leftGates
  rightVars i := lv S (C.rightVars i)
  rightGates := C.rightGates
  outVars := lv S C.outVars
  outGates := C.outGates

theorem lv_spec (S : Finset (Fin 26)) (B : Finset (Fin 27)) (U : Finset (Fin 26))
    (hU : ∃ x ∈ S, x ∈ U) :
    (∃ v ∈ lv S B, v ∈ U) ↔ (∃ v ∈ B, v ∈ insert (0 : Fin 27) (U.image Fin.succ)) := by
  constructor
  · rintro ⟨v, hv, hvU⟩
    simp only [lv, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with h | ⟨h0, _⟩
    · exact ⟨v.succ, h, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hvU)⟩
    · exact ⟨0, h0, Finset.mem_insert_self _ _⟩
  · rintro ⟨v, hv, hvU⟩
    rw [Finset.mem_insert, Finset.mem_image] at hvU
    rcases hvU with rfl | ⟨w, hw, rfl⟩
    · obtain ⟨x, hx, hxU⟩ := hU
      refine ⟨x, ?_, hxU⟩
      simp only [lv, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨hv, hx⟩
    · refine ⟨w, ?_, hw⟩
      simp only [lv, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl hv

theorem side_eq {k : ℕ} (S : Finset (Fin 26)) (U : Finset (Fin 26)) (B : Finset (Fin 27))
    (F : Finset (Fin k)) (i : Fin k) (val val' : Fin k → Bool) (hv : val = val')
    (hU : ∃ x ∈ S, x ∈ U) :
    sideTrue U (lv S B) F i val = sideTrue (insert (0 : Fin 27) (U.image Fin.succ)) B F i val' := by
  subst hv
  unfold sideTrue
  rw [decide_eq_decide]
  exact or_congr (lv_spec S B U hU) Iff.rfl

theorem fuel_eq (C : AndCountCircuit 27) (S : Finset (Fin 26)) (U : Finset (Fin 26))
    (hU : ∃ x ∈ S, x ∈ U) (d : ℕ) :
    ∀ i : Fin C.size, gateValFuel (restr C S) U d i
      = gateValFuel C (insert (0 : Fin 27) (U.image Fin.succ)) d i := by
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    have hf : gateValFuel (restr C S) U d
        = gateValFuel C (insert (0 : Fin 27) (U.image Fin.succ)) d := funext ih
    show (sideTrue U (lv S (C.leftVars i)) (C.leftGates i) i (gateValFuel (restr C S) U d) &&
        sideTrue U (lv S (C.rightVars i)) (C.rightGates i) i (gateValFuel (restr C S) U d)) =
      (sideTrue (insert (0 : Fin 27) (U.image Fin.succ)) (C.leftVars i) (C.leftGates i) i
          (gateValFuel C (insert (0 : Fin 27) (U.image Fin.succ)) d) &&
        sideTrue (insert (0 : Fin 27) (U.image Fin.succ)) (C.rightVars i) (C.rightGates i) i
          (gateValFuel C (insert (0 : Fin 27) (U.image Fin.succ)) d))
    rw [side_eq S U (C.leftVars i) (C.leftGates i) i _ _ hf hU,
      side_eq S U (C.rightVars i) (C.rightGates i) i _ _ hf hU]

theorem eval_eq (C : AndCountCircuit 27) (S : Finset (Fin 26)) (U : Finset (Fin 26))
    (hU : ∃ x ∈ S, x ∈ U) :
    (restr C S).eval U = C.eval (insert (0 : Fin 27) (U.image Fin.succ)) := by
  have hg : ∀ j : Fin C.size, (restr C S).gateVal U j
      = C.gateVal (insert (0 : Fin 27) (U.image Fin.succ)) j :=
    fun j => fuel_eq C S U hU C.size j
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  constructor
  · rintro (h | ⟨j, hj, hv⟩)
    · exact Or.inl ((lv_spec S C.outVars U hU).mp h)
    · exact Or.inr ⟨j, hj, (hg j) ▸ hv⟩
  · rintro (h | ⟨j, hj, hv⟩)
    · exact Or.inl ((lv_spec S C.outVars U hU).mpr h)
    · exact Or.inr ⟨j, hj, (hg j).symm ▸ hv⟩

end PEqualNP.Outside.L_meta_6305

theorem PEqualNP.Outside.L_meta_6305 : ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)) (x2 : Finset (Fin (26 : ℕ))), x1.WellFormed → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit (26 : ℕ)), x4.WellFormed ∧ x4.size = x1.size ∧ ∀ (x5 : Finset (Fin (26 : ℕ))), (∃ x6 ∈ x2, x6 ∈ x5) → x4.eval x5 = x1.eval (Insert.insert (0 : Fin (27 : ℕ)) (Finset.image Fin.succ x5)) := by
  intro C S hW
  refine ⟨PEqualNP.Outside.L_meta_6305.restr C S, fun i => hW i, rfl, ?_⟩
  intro U hU
  exact PEqualNP.Outside.L_meta_6305.eval_eq C S U hU
