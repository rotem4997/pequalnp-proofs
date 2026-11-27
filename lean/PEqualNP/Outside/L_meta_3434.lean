import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3434_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (x1 : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map x1⟩

lemma step_inv (x1 : ℕ → ℕ) (L M : ℕ) (W Y : List Bool) (g : Gate) (hl : W.length = Y.length)
    (hL : L ≤ Y.length) (hM : Y.length + 1 ≤ M) (h1 : ∀ k, L ≤ k → x1 k = k)
    (h2 : ∀ k, k < L → x1 k < L ∨ M ≤ x1 k)
    (hv : ∀ k, W.getD (x1 k) false = Y.getD k false) :
    ∀ k, (stepW W (reGate x1 g)).getD (x1 k) false = (stepW Y g).getD k false := by
  intro k
  have hm : (g.inputs.map x1).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hv i)
  show (W ++ [g.op.eval ((g.inputs.map x1).map fun i => W.getD i false)]).getD (x1 k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  by_cases hk : k < L
  · rcases h2 k hk with h | h
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hv k]
    · have e := hv k
      rw [List.getD_eq_default _ _ (by omega)] at e
      rw [List.getD_append _ _ _ _ (by omega : k < Y.length), ← e]
      exact List.getD_eq_default _ _ (by simp; omega)
  · have hrk := h1 k (by omega)
    have e := hv k
    rw [hrk] at e
    rw [hrk]
    by_cases hk2 : k < Y.length
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hk2, e]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

lemma fold_inv (x1 : ℕ → ℕ) (L M : ℕ) (h1 : ∀ k, L ≤ k → x1 k = k)
    (h2 : ∀ k, k < L → x1 k < L ∨ M ≤ x1 k) (gs : List Gate) :
    ∀ (W Y : List Bool), W.length = Y.length →
    L ≤ Y.length → Y.length + gs.length ≤ M → (∀ k, W.getD (x1 k) false = Y.getD k false) →
    ∀ k, ((gs.map (reGate x1)).foldl stepW W).getD (x1 k) false = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro W Y _ _ _ hv; exact hv
  | cons g gs ih =>
    intro W Y hl hL hM hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hM2 : Y.length + (gs.length + 1) ≤ M := by simpa using hM
    refine ih _ _ ?_ ?_ ?_ (step_inv x1 L M W Y g hl hL (by omega) h1 h2 hv)
    · simp [stepW, hl]
    · simp [stepW]; omega
    · simp [stepW]; omega

end PEqualNP.Outside.L_meta_3434_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3434_aux in
theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  intro x1 C x3 x4 hl h1 h2 hv
  exact fold_inv x1 x3.length (x3.length + C.size) h1 h2 C.gates x4 x3 hl.symm le_rfl (by simp [Circuit.size]) hv C.output
