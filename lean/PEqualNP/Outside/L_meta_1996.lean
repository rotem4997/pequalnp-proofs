import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1996_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

theorem gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

end PEqualNP.Outside.L_meta_1996_aux

theorem PEqualNP.Outside.L_meta_1996 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 x4 : Finset (Fin x1)), x3 ⊆ x4 → x2.eval x3 = Bool.true → x2.eval x4 = Bool.true := by
  intro n C S T hST h
  unfold PEqualNP.AndCount.AndCountCircuit.eval at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  rcases h with ⟨v, hv, hvS⟩ | ⟨j, hj, hjv⟩
  · exact Or.inl ⟨v, hv, hST hvS⟩
  · exact Or.inr ⟨j, hj, PEqualNP.Outside.L_meta_1996_aux.gateValFuel_mono_U C hST C.size j hjv⟩
