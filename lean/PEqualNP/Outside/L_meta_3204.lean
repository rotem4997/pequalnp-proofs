import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3204_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def r {n : ℕ} (x1 : Fin n → Fin n) (k : ℕ) : ℕ := if h : k < n then (x1 ⟨k, h⟩).val else k

def reGate {n : ℕ} (x1 : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op, g.inputs.map (r x1)⟩

lemma step_inv {n : ℕ} (x1 : Fin n → Fin n) (W Y : List Bool) (g : Gate) (hl : W.length = Y.length)
    (h9 : n ≤ Y.length) (hv : ∀ k, W.getD (r x1 k) false = Y.getD k false) :
    ∀ k, (stepW W (reGate x1 g)).getD (r x1 k) false = (stepW Y g).getD k false := by
  intro k
  have hm : (g.inputs.map (r x1)).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hv i)
  show (W ++ [g.op.eval ((g.inputs.map (r x1)).map fun i => W.getD i false)]).getD (r x1 k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  have hr : r x1 k < W.length ↔ k < Y.length := by
    unfold r
    split_ifs with h
    · have := (x1 ⟨k, h⟩).isLt
      constructor <;> intro <;> omega
    · omega
  by_cases hk : k < Y.length
  · rw [List.getD_append _ _ _ _ (hr.mpr hk), List.getD_append _ _ _ _ hk, hv k]
  · have hrk : r x1 k = k := by
      unfold r
      rw [dif_neg (by omega)]
    rw [hrk, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

lemma fold_inv {n : ℕ} (x1 : Fin n → Fin n) (gs : List Gate) : ∀ (W Y : List Bool), W.length = Y.length →
    n ≤ Y.length → (∀ k, W.getD (r x1 k) false = Y.getD k false) →
    ∀ k, ((gs.map (reGate x1)).foldl stepW W).getD (r x1 k) false = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro W Y _ _ hv; exact hv
  | cons g gs ih =>
    intro W Y hl h9 hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ (step_inv x1 W Y g hl h9 hv)
    · simp [stepW, hl]
    · simp [stepW]; omega

lemma base {n : ℕ} (x2 : Fin n → Fin n) (x6 : Fin n → Bool) (x7 : List Bool) (k : ℕ) :
    (List.ofFn x6 ++ x7).getD (r x2 k) false
      = ((List.ofFn fun (x8 : Fin n) => x6 (x2 x8)) ++ x7).getD k false := by
  unfold r
  split_ifs with h
  · have h2 := (x2 ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by simpa using h2), List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h, h2]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

end PEqualNP.Outside.L_meta_3204_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3204_aux in
theorem PEqualNP.Outside.L_meta_3204 : ∀ (x1 : ℕ) (x2 : Equiv.Perm (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : List Bool), x5.eval (List.ofFn x6 ++ x7) = x3.eval ((List.ofFn fun (x8 : Fin x1) => x6 (x2 x8)) ++ x7) := by
  intro x1 x2 C hC
  refine ⟨⟨C.gates.map (reGate x2), r x2 C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hC g0 hg0
    simpa [reGate] using this
  · simp [Circuit.size]
  · intro x6 x7
    exact fold_inv x2 C.gates _ _ (by simp) (by simp) (base x2 x6 x7) C.output
