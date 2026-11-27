import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6456

theorem PEqualNP.Outside.L_meta_6456 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : Fin (26 : ℕ) → Bool), x2 ≠ [] → x2.length ≤ (2 : ℕ) → (∀ (x7 : Fin (26 : ℕ)), x3 x7 = Bool.false ∨ x4 x7 = Bool.false) → (∀ x8 ∈ [x3, x4], PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn x8)).getD x10 Bool.false) x2) = Bool.true) → ∃ (x9 : Fin x1.size) (x10 : Fin x1.size), x9 ≤ x10 ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x12 : ℕ) => (x1.wires (List.ofFn x11)).getD x12 Bool.false) x2) = ((x1.wires (List.ofFn x11)).getD ((26 : ℕ) + ↑x9) Bool.false && (x1.wires (List.ofFn x11)).getD ((26 : ℕ) + ↑x10) Bool.false) := by
  intro C l x y hne hl hdis hxy
  have hx := hxy x (by simp)
  have hy := hxy y (by simp)
  let V : (Fin 26 → Bool) → ℕ → Bool := fun z w => (PEqualNP.Outside.L_meta_6456.run C.gates (List.ofFn z)).getD w false
  have hw : ∀ w, V x w = true → V y w = true → ∃ j : Fin C.size, w = 26 + j := by
    intro w h1 h2
    by_cases h9 : w < 26
    · exfalso
      have e1 : V x w = x ⟨w, h9⟩ := by
        simp only [V]
        rw [PEqualNP.Outside.L_meta_6456.run_input _ _ _ (by simpa using h9)]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h9]; rfl
      have e2 : V y w = y ⟨w, h9⟩ := by
        simp only [V]
        rw [PEqualNP.Outside.L_meta_6456.run_input _ _ _ (by simpa using h9)]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h9]; rfl
      rw [e1] at h1
      rw [e2] at h2
      rcases hdis ⟨w, h9⟩ with h | h
      · rw [h] at h1; cases h1
      · rw [h] at h2; cases h2
    · by_cases h8 : w < 26 + C.gates.length
      · exact ⟨⟨w - 26, by show w - 26 < C.gates.length; omega⟩, by simp; omega⟩
      · simp only [V] at h1
        rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6456.run_length]; simp; omega)] at h1
        cases h1
  have all : ∀ z w, w ∈ l → PEqualNP.CircuitLowerBounds.GateOp.and.eval (l.map fun w => V z w) = true → V z w = true := by
    intro z w hwl h
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at h
    exact h w hwl
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact absurd rfl hne
  · obtain ⟨j, rfl⟩ := hw a (all x a (by simp) hx) (all y a (by simp) hy)
    refine ⟨j, j, le_rfl, fun z => ?_⟩
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · obtain ⟨j, rfl⟩ := hw a (all x a (by simp) hx) (all y a (by simp) hy)
    obtain ⟨j', rfl⟩ := hw b (all x b (by simp) hx) (all y b (by simp) hy)
    rcases le_total j j' with h | h
    · refine ⟨j, j', h, fun z => ?_⟩
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    · refine ⟨j', j, h, fun z => ?_⟩
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_comm]
  · simp at hl
