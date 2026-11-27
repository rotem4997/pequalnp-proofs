import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8827

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




def rn (n m : ℕ) (π : Fin n → Fin m) (i : ℕ) : ℕ := if h : i < n then (π ⟨i, h⟩ : ℕ) else i - n + m

theorem ren (n m : ℕ) (π : Fin n → Fin m) (y : Fin m → Bool) : ∀ hs : List Gate,
    ∀ i, (run (hs.map fun g => (⟨g.op, g.inputs.map (rn n m π)⟩ : Gate)) (List.ofFn y)).getD (rn n m π i) false =
      (run hs (List.ofFn (y ∘ π))).getD i false := by
  intro hs
  induction hs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [List.map_nil]
    by_cases hi : i < n
    · have e : rn n m π i = (π ⟨i, hi⟩ : ℕ) := dif_pos hi
      rw [e, run_input [] (List.ofFn y) (π ⟨i, hi⟩ : ℕ) (by simp),
        run_input [] (List.ofFn (y ∘ π)) i (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, hi]
    · have e : rn n m π i = i - n + m := dif_neg hi
      rw [e, List.getD_eq_default _ _ (by rw [run_length]; simp),
        List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  | append_singleton hs g ih =>
    intro i
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc]
    have l1 : (run (hs.map fun g => (⟨g.op, g.inputs.map (rn n m π)⟩ : Gate)) (List.ofFn y)).length = m + hs.length := by
      rw [run_length]; simp
    have l2 : (run hs (List.ofFn (y ∘ π))).length = n + hs.length := by rw [run_length]; simp
    have hrn : i < n → rn n m π i < m := by
      intro h
      have e : rn n m π i = (π ⟨i, h⟩ : ℕ) := dif_pos h
      rw [e]; exact (π ⟨i, h⟩).isLt
    have hrn2 : ¬ i < n → rn n m π i = i - n + m := fun h => dif_neg h
    rcases Nat.lt_trichotomy i (n + hs.length) with h | h | h
    · have : rn n m π i < m + hs.length := by
        by_cases hi : i < n
        · have := hrn hi; omega
        · rw [hrn2 hi]; omega
      rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega), ih i]
    · have hi : ¬ i < n := by omega
      have e1 : rn n m π i = (run (hs.map fun g => (⟨g.op, g.inputs.map (rn n m π)⟩ : Gate)) (List.ofFn y)).length := by
        rw [l1, hrn2 hi]; omega
      have e2 : i = (run hs (List.ofFn (y ∘ π))).length := by omega
      rw [e1, getD_at]
      conv_rhs => rw [e2, getD_at]
      rw [List.map_map]
      congr 1
      exact List.map_congr_left fun k _ => ih k
    · have hi : ¬ i < n := by omega
      rw [List.getD_eq_default _ _ (by rw [List.length_append, l1, hrn2 hi]; simp; omega),
        List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8827

theorem PEqualNP.Outside.L_meta_8827 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : Equiv.Perm (Fin x1)), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x2.size ∧ ∀ (x6 : ℕ) (x7 : Fin x1 → Bool), x1 ≤ x6 → (x5.wires (List.ofFn x7)).getD x6 Bool.false = (x2.wires (List.ofFn (x7 ∘ ⇑x4))).getD x6 Bool.false := by
  intro n C hC π
  refine ⟨⟨C.gates.map fun g => ⟨g.op, g.inputs.map (PEqualNP.Outside.L_meta_8827.rn n n π)⟩, C.output⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := hC g' hg'
    exact ⟨h1, by simpa using h2⟩
  · intro w y hw
    have h := PEqualNP.Outside.L_meta_8827.ren n n π y C.gates w
    have e : PEqualNP.Outside.L_meta_8827.rn n n π w = w := by rw [PEqualNP.Outside.L_meta_8827.rn, dif_neg (by omega)]; omega
    rw [e] at h
    exact h
