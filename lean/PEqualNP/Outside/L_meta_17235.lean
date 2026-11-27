import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17235
open PEqualNP.CircuitLowerBounds



def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ev_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (U V : List Bool)
    (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    g.op.eval (g.inputs.map fun i => U.getD i false) = true →
      g.op.eval (g.inputs.map fun i => V.getD i false) = true := by
  rcases hg with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.all_eq_true, List.any_eq_true,
    List.mem_map, id_eq]
  · intro hu x ⟨i, hi, hx⟩
    subst hx
    exact h i (hu _ ⟨i, hi, rfl⟩)
  · rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

theorem key : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (gs.foldl stp U).getD i false = true → (gs.foldl stp V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g gs ih =>
    intro hgs U V hl h i
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [stp, hl]
    · intro k hk
      unfold stp at hk ⊢
      rcases Nat.lt_trichotomy k U.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hk
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h k hk
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hk
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
        exact ev_mono g (hgs g (List.mem_cons_self ..)) U V h hk
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        exact absurd hk (by simp)

end PEqualNP.Outside.L_meta_17235

open PEqualNP.Outside.L_meta_17235 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_17235 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) → ∀ (x7 : ℕ), (x2.wires (List.ofFn x4)).getD x7 Bool.false = Bool.true → (x2.wires (List.ofFn x5)).getD x7 Bool.false = Bool.true := by
  intro n C hC x y hxy w hw
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact key C.gates hgs (List.ofFn x) (List.ofFn y) (by simp) (fun i hi => by
    by_cases h : i < n
    · have e1 : (List.ofFn x).getD i false = x ⟨i, h⟩ := by simp [List.getD_eq_getElem?_getD, h]
      have e2 : (List.ofFn y).getD i false = y ⟨i, h⟩ := by simp [List.getD_eq_getElem?_getD, h]
      rw [e1] at hi; rw [e2]; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)) w hw
