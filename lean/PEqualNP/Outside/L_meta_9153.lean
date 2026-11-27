import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9153
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem monoW : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g t ih =>
    intro hop U V hlen hUV i
    rw [wf_cons, wf_cons]
    refine ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen]) ?_ i
    intro j hj
    rcases Nat.lt_trichotomy j U.length with hj' | hj' | hj'
    · rw [getD_snoc_lt _ _ _ hj'] at hj
      rw [getD_snoc_lt _ _ _ (by omega)]
      exact hUV j hj
    · rw [hj', getD_snoc_eq] at hj
      rw [hj', hlen, getD_snoc_eq]
      exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs U V hUV hj
    · rw [getD_snoc_gt _ _ _ hj'] at hj
      exact absurd hj (by simp)

end PEqualNP.Outside.L_meta_9153

open PEqualNP.Outside.L_meta_9153 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9153 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 : ℕ), Monotone fun (x4 : Fin (26 : ℕ) → Bool) => (x1.wires (List.ofFn x4)).getD x3 Bool.false := by
  intro C hop w a b hab
  show (wf C.gates (List.ofFn a)).getD w false ≤ (wf C.gates (List.ofFn b)).getD w false
  cases h : (wf C.gates (List.ofFn a)).getD w false with
  | false => exact Bool.false_le _
  | true =>
    rw [monoW C.gates hop _ _ (by simp) (ofFn_mono 26 a b hab) w h]
