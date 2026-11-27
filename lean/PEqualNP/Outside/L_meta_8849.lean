import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8849

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

end PEqualNP.Outside.L_meta_8849

theorem PEqualNP.Outside.L_meta_8849 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → ∀ (x4 x5 x6 x7 : Finset (Fin x1)), x4 ⊆ x6 → x5 ⊆ x7 → x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true → x2.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true := by
  intro n C hC X Y X' Y' hX hY h
  let x : List Bool := PEqualNP.GenericRejection.incidenceInput X Y
  let y : List Bool := PEqualNP.GenericRejection.incidenceInput X' Y'
  have lx : x.length = n + n := by simp [x, PEqualNP.GenericRejection.incidenceInput]
  have ly : y.length = n + n := by simp [y, PEqualNP.GenericRejection.incidenceInput]
  have hxy : ∀ i, x.getD i false = true → y.getD i false = true := by
    intro i hi
    simp only [x, y, PEqualNP.GenericRejection.incidenceInput] at hi ⊢
    by_cases h1 : i < n
    · rw [List.getD_append _ _ _ _ (by simpa using h1), List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_ofFn] at hi ⊢
      rw [decide_eq_true_eq] at hi ⊢
      exact hX hi
    · by_cases h2 : i < n + n
      · have h3 : i - n < n := by omega
        rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn, List.getD_eq_getElem _ _ (by simpa using h3), List.getElem_ofFn] at hi ⊢
        rw [decide_eq_true_eq] at hi ⊢
        exact hY hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi
  have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ i,
      (PEqualNP.Outside.L_meta_8849.run gs x).getD i false = true → (PEqualNP.Outside.L_meta_8849.run gs y).getD i false = true := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ i h
      exact hxy i h
    | append_singleton gs g ih =>
      intro hg i h
      have ih := ih fun g' hg' => hg g' (List.mem_append_left _ hg')
      have hop := hg g (by simp)
      rw [PEqualNP.Outside.L_meta_8849.run_snoc] at h ⊢
      have l1 : (PEqualNP.Outside.L_meta_8849.run gs x).length = (n + n) + gs.length := by rw [PEqualNP.Outside.L_meta_8849.run_length]; omega
      have l2 : (PEqualNP.Outside.L_meta_8849.run gs y).length = (n + n) + gs.length := by rw [PEqualNP.Outside.L_meta_8849.run_length]; omega
      rcases Nat.lt_trichotomy i ((n + n) + gs.length) with h1 | h1 | h1
      · rw [PEqualNP.Outside.L_meta_8849.getD_lt _ _ _ (by omega)] at h ⊢
        exact ih i h
      · have e1 : i = (PEqualNP.Outside.L_meta_8849.run gs x).length := by omega
        have e2 : i = (PEqualNP.Outside.L_meta_8849.run gs y).length := by omega
        rw [e1, PEqualNP.Outside.L_meta_8849.getD_at] at h
        rw [e2, PEqualNP.Outside.L_meta_8849.getD_at]
        rcases hop with ho | ho
        · rw [ho] at h ⊢
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at h ⊢
          exact fun k hk => ih k (h k hk)
        · rw [ho] at h ⊢
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at h ⊢
          obtain ⟨k, hk, h⟩ := h
          exact ⟨k, hk, ih k h⟩
      · rw [List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega)] at h
        cases h
  exact key C.gates hC.1 C.output h
