import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8608

open PEqualNP.CircuitLowerBounds

theorem aux (f : ℕ → Bool) : ∀ (gs : List Gate) (w : List Bool),
    (∀ i, i < w.length → w.getD i false = f i) →
    (∀ k (hk : k < gs.length), (∀ j ∈ (gs[k]).inputs, j < w.length + k) ∧
        (gs[k]).op.eval ((gs[k]).inputs.map f) = f (w.length + k)) →
    ∀ i, i < w.length + gs.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
        false = f i := by
  intro gs
  induction gs with
  | nil =>
    intro w hw _ i hi
    simp only [List.length_nil, Nat.add_zero] at hi
    simpa using hw i hi
  | cons g gs ih =>
    intro w hw hg i hi
    rw [List.foldl_cons]
    have h0 := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    obtain ⟨hin, hev⟩ := h0
    apply ih
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [List.getD_append _ _ _ _ hj]
        exact hw j hj
      · subst hj
        rw [List.getD_eq_getElem?_getD]
        simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
        rw [← hev]
        congr 1
        apply List.map_congr_left
        intro a ha
        exact hw a (hin a ha)
    · intro k hk
      have h := hg (k + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at h
      obtain ⟨h1, h2⟩ := h
      simp only [List.length_append, List.length_singleton]
      refine ⟨fun j hj => by have := h1 j hj; omega, ?_⟩
      rw [h2]
      congr 1
      omega
    · simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hi
      omega

end PEqualNP.Outside.L_meta_8608

theorem PEqualNP.Outside.L_meta_8608 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List Bool) (x3 : ℕ → Bool), (∀ (x4 : Fin x2.length), x2.get x4 = x3 ↑x4) → (∀ (x5 : Fin x1.length), (∀ x6 ∈ (x1.get x5).inputs, x6 < x2.length + ↑x5) ∧ (x1.get x5).op.eval (List.map x3 (x1.get x5).inputs) = x3 (x2.length + ↑x5)) → ∀ (x6 : Fin (x2.length + x1.length)), ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x2).getD (↑x6) Bool.false = x3 ↑x6 := by
  intro gs w f hw hg i
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  apply PEqualNP.Outside.L_meta_8608.aux f gs w
  · intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hw ⟨j, hj⟩
  · intro k hk
    exact hg ⟨k, hk⟩
  · exact i.isLt
