import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9065

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

end PEqualNP.Outside.L_meta_9065

theorem PEqualNP.Outside.L_meta_9065 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly x1 → Monotone fun (x3 : Fin (26 : ℕ) → Bool) => x1.eval (List.ofFn x3 ++ [x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ))]) := by
  intro C hC x y hxy
  have hb : ∀ a b : Bool, a ≤ b ↔ (a = true → b = true) := by decide
  have hxy' : ∀ i, x i = true → y i = true := fun i => (hb _ _).1 (hxy i)
  obtain ⟨X, hX⟩ : ∃ X, X = List.ofFn x ++ [x (1 : Fin 26) || x (2 : Fin 26)] := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = List.ofFn y ++ [y (1 : Fin 26) || y (2 : Fin 26)] := ⟨_, rfl⟩
  have lX : X.length = 27 := by rw [hX, List.length_append, List.length_ofFn]; rfl
  have lY : Y.length = 27 := by rw [hY, List.length_append, List.length_ofFn]; rfl
  have base : ∀ i, X.getD i false = true → Y.getD i false = true := by
    intro i h
    rcases Nat.lt_trichotomy i 26 with hi | hi | hi
    · rw [hX, PEqualNP.Outside.L_meta_9065.getD_lt _ _ _ (by rw [List.length_ofFn]; exact hi), List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn] at h
      rw [hY, PEqualNP.Outside.L_meta_9065.getD_lt _ _ _ (by rw [List.length_ofFn]; exact hi), List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
      exact hxy' _ h
    · have ex : i = (List.ofFn x).length := by rw [List.length_ofFn]; exact hi
      have ey : i = (List.ofFn y).length := by rw [List.length_ofFn]; exact hi
      rw [hX, ex, PEqualNP.Outside.L_meta_9065.getD_at] at h
      rw [hY, ey, PEqualNP.Outside.L_meta_9065.getD_at]
      rw [Bool.or_eq_true] at h ⊢
      exact h.imp (hxy' _) (hxy' _)
    · rw [List.getD_eq_default _ _ (by omega)] at h
      cases h
  have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ i,
      (PEqualNP.Outside.L_meta_9065.run gs X).getD i false = true → (PEqualNP.Outside.L_meta_9065.run gs Y).getD i false = true := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => exact fun _ i h => base i h
    | append_singleton gs g ih =>
      intro hg i h
      have ih := ih fun g' hg' => hg g' (List.mem_append_left _ hg')
      have hop := hg g (by simp)
      rw [PEqualNP.Outside.L_meta_9065.run_snoc] at h ⊢
      have l1 : (PEqualNP.Outside.L_meta_9065.run gs X).length = 27 + gs.length := by rw [PEqualNP.Outside.L_meta_9065.run_length, lX]
      have l2 : (PEqualNP.Outside.L_meta_9065.run gs Y).length = 27 + gs.length := by rw [PEqualNP.Outside.L_meta_9065.run_length, lY]
      rcases Nat.lt_trichotomy i (27 + gs.length) with h1 | h1 | h1
      · rw [PEqualNP.Outside.L_meta_9065.getD_lt _ _ _ (by omega)] at h ⊢
        exact ih i h
      · have e1 : i = (PEqualNP.Outside.L_meta_9065.run gs X).length := by omega
        have e2 : i = (PEqualNP.Outside.L_meta_9065.run gs Y).length := by omega
        rw [e1, PEqualNP.Outside.L_meta_9065.getD_at] at h
        rw [e2, PEqualNP.Outside.L_meta_9065.getD_at]
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
  refine (hb _ _).2 fun h => ?_
  have h : (PEqualNP.Outside.L_meta_9065.run C.gates (List.ofFn x ++ [x (1 : Fin 26) || x (2 : Fin 26)])).getD C.output false = true := h
  show (PEqualNP.Outside.L_meta_9065.run C.gates (List.ofFn y ++ [y (1 : Fin 26) || y (2 : Fin 26)])).getD C.output false = true
  rw [← hX] at h
  rw [← hY]
  exact key C.gates hC C.output h
