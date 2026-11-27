import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7171

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp only [W, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton l a ih =>
    rw [W_snoc, List.length_append, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem W_ext (gs : List Gate) (x : List Bool) : ∀ hs : List Gate, ∃ r, W (gs ++ hs) x = W gs x ++ r := by
  intro hs
  induction hs using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton l a ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r ++ [a.op.eval (a.inputs.map fun i => (W (gs ++ l) x).getD i false)], ?_⟩
    rw [← List.append_assoc, W_snoc, hr, List.append_assoc]

theorem W_pre (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) (hk : k ≤ gs.length) :
    (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  obtain ⟨r, hr⟩ := W_ext (gs.take k) x (gs.drop k)
  rw [List.take_append_drop] at hr
  have hl := W_len (gs.take k) x
  rw [List.length_take, Nat.min_eq_left hk] at hl
  rw [hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]

theorem any_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l) (hf : f a = true) :
    GateOp.or.eval (l.map f) = true := by
  simp only [GateOp.eval, List.any_map, List.any_eq_true]
  exact ⟨a, ha, hf⟩

theorem main (C : Circuit) (x y : List Bool) (hxy : x.length = 9 ∧ y.length = 9)
    (h : ∀ i, i ≠ 4 → x.getD i false = y.getD i false)
    (hg : ∀ k : Fin C.gates.length, 4 ∈ (C.gates.get k).inputs → (C.gates.get k).op = GateOp.or ∧
      ∃ j ∈ (C.gates.get k).inputs, j ≠ 4 ∧ j < 9 + (k : ℕ) ∧ (W C.gates x).getD j false = true) :
    ∀ k, k ≤ C.gates.length → ∀ i, i ≠ 4 →
      (W (C.gates.take k) x).getD i false = (W (C.gates.take k) y).getD i false := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    simpa [W] using h i hi
  | succ k ih =>
    intro hk i hi
    have hk' : k < C.gates.length := hk
    have ih' := ih (Nat.le_of_lt hk')
    rw [List.take_succ_eq_append_getElem hk', W_snoc, W_snoc]
    have lx := W_len (C.gates.take k) x
    have ly := W_len (C.gates.take k) y
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk')] at lx ly
    have hval : (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => (W (C.gates.take k) x).getD i false)
        = (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => (W (C.gates.take k) y).getD i false) := by
      by_cases h4 : 4 ∈ (C.gates[k]).inputs
      · obtain ⟨hop, j, hj, hj4, hjlt, hjv⟩ := hg ⟨k, hk'⟩ h4
        have hop' : (C.gates[k]).op = GateOp.or := hop
        have hj' : j ∈ (C.gates[k]).inputs := hj
        have hjlt' : j < 9 + k := hjlt
        rw [W_pre C.gates x k j (by omega) (Nat.le_of_lt hk')] at hjv
        rw [hop', any_true _ _ j hj' hjv, any_true _ _ j hj' (by rw [← ih' j hj4]; exact hjv)]
      · congr 1
        apply List.map_congr_left
        intro a ha
        exact ih' a (fun e => h4 (e ▸ ha))
    rw [hval]
    simp only [List.getD_eq_getElem?_getD]
    by_cases hlt : i < 9 + k
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      have := ih' i hi
      simpa [List.getD_eq_getElem?_getD] using this
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), lx, ly, hxy.1, hxy.2]

end PEqualNP.Outside.L_meta_7171

theorem PEqualNP.Outside.L_meta_7171 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (9 : ℕ) → Bool),   x1.output ≠ (4 : ℕ) →     (∀ (x5 : Fin (9 : ℕ)), x5 ≠ (4 : Fin (9 : ℕ)) → x2 x5 = x3 x5) →       (∀ (x6 : Fin x1.size),           have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.gates.get x6;           (4 : ℕ) ∈ x7.inputs → x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ x9 ∈ x7.inputs, x9 ≠ (4 : ℕ) ∧ x9 < (9 : ℕ) + ↑x6 ∧ (x1.wires (List.ofFn x2)).getD x9 Bool.false = Bool.true) →         PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x2 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x3 := by
  intro C x y hout hxy hg
  have key := PEqualNP.Outside.L_meta_7171.main C (List.ofFn x) (List.ofFn y) (by simp)
    (by
      intro i hi
      by_cases hlt : i < 9
      · have := hxy ⟨i, hlt⟩ (by intro e; apply hi; exact congrArg Fin.val e)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
        exact this
      · simp [List.getD_eq_getElem?_getD, hlt])
    hg C.gates.length (Nat.le_refl _) C.output hout
  rw [List.take_length] at key
  exact key
