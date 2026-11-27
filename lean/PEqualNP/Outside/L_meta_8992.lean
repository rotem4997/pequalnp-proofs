import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8992

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

end PEqualNP.Outside.L_meta_8992

theorem PEqualNP.Outside.L_meta_8992 : ∀ (x1 : ℕ) (x2 : Fin (x1 + (1 : ℕ))) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x3.size ∧ ∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x5 x6 = PEqualNP.MetaComplexity.circuitFun (x1 + (1 : ℕ)) x3 (x2.insertNth Bool.false x6) := by
  intro n p C hC
  let T := C.gates.length
  let ρ : ℕ → ℕ := fun i => if i < (p : ℕ) then i else if i = (p : ℕ) then n + T else i - 1
  refine ⟨⟨C.gates.map fun g => ⟨g.op, g.inputs.map ρ⟩, ρ C.output⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], fun y => ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ⟨(hC g' hg').1, by simpa using (hC g' hg').2⟩
  · let x : Fin (n + 1) → Bool := p.insertNth (α := fun _ => Bool) false y
    have hp := p.isLt
    have xv : ∀ i (hi : i < n + 1), (List.ofFn x).getD i false = x ⟨i, hi⟩ := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    have yv : ∀ i (hi : i < n), (List.ofFn y).getD i false = y ⟨i, hi⟩ := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    have base : ∀ i, (List.ofFn y).getD (ρ i) false = (List.ofFn x).getD i false := by
      intro i
      by_cases h1 : i < (p : ℕ)
      · have e : ρ i = i := if_pos h1
        rw [e, yv i (by omega), xv i (by omega)]
        have : (⟨i, by omega⟩ : Fin (n + 1)) = p.succAbove ⟨i, by omega⟩ := by
          rw [Fin.succAbove_of_castSucc_lt _ _ (by exact h1)]
          rfl
        simp only [x, this, Fin.insertNth_apply_succAbove]
      · by_cases h2 : i = (p : ℕ)
        · have e : ρ i = n + T := by simp only [ρ]; rw [if_neg h1, if_pos h2]
          rw [e, List.getD_eq_default _ _ (by simp), xv i (by omega)]
          have : (⟨i, by omega⟩ : Fin (n + 1)) = p := Fin.ext h2
          simp only [x, this, Fin.insertNth_apply_same]
        · have e : ρ i = i - 1 := by simp only [ρ]; rw [if_neg h1, if_neg h2]
          rw [e]
          by_cases h3 : i < n + 1
          · rw [yv (i - 1) (by omega), xv i h3]
            have : (⟨i, h3⟩ : Fin (n + 1)) = p.succAbove ⟨i - 1, by omega⟩ := by
              rw [Fin.succAbove_of_le_castSucc _ _ (by show (p : ℕ) ≤ i - 1; omega)]
              exact Fin.ext (by simp; omega)
            simp only [x, this, Fin.insertNth_apply_succAbove]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, gs.length ≤ T → ∀ i, (PEqualNP.Outside.L_meta_8992.run (gs.map fun g => ⟨g.op, g.inputs.map ρ⟩) (List.ofFn y)).getD (ρ i) false = (PEqualNP.Outside.L_meta_8992.run gs (List.ofFn x)).getD i false := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => intro _ i; exact base i
      | append_singleton gs g ih =>
        intro hT i
        have hT : gs.length + 1 ≤ T := by simpa using hT
        have ih := ih (by omega)
        rw [List.map_append, List.map_singleton, PEqualNP.Outside.L_meta_8992.run_snoc, PEqualNP.Outside.L_meta_8992.run_snoc]
        have l1 : (PEqualNP.Outside.L_meta_8992.run (gs.map fun g => (⟨g.op, g.inputs.map ρ⟩ : PEqualNP.CircuitLowerBounds.Gate)) (List.ofFn y)).length = n + gs.length := by
          rw [PEqualNP.Outside.L_meta_8992.run_length, List.length_ofFn, List.length_map]
        have l2 : (PEqualNP.Outside.L_meta_8992.run gs (List.ofFn x)).length = n + 1 + gs.length := by rw [PEqualNP.Outside.L_meta_8992.run_length, List.length_ofFn]
        rcases Nat.lt_trichotomy i (n + 1 + gs.length) with h | h | h
        · rw [PEqualNP.Outside.L_meta_8992.getD_lt (PEqualNP.Outside.L_meta_8992.run gs (List.ofFn x)) _ _ (by omega), ← ih i]
          by_cases h2 : i = (p : ℕ)
          · have e : ρ i = n + T := by simp only [ρ]; rw [if_neg (by omega), if_pos h2]
            rw [e, List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega), List.getD_eq_default _ _ (by rw [l1]; omega)]
          · have : ρ i < n + gs.length := by
              simp only [ρ]
              split_ifs <;> omega
            rw [PEqualNP.Outside.L_meta_8992.getD_lt _ _ _ (by omega)]
        · have e : ρ i = (PEqualNP.Outside.L_meta_8992.run (gs.map fun g => (⟨g.op, g.inputs.map ρ⟩ : PEqualNP.CircuitLowerBounds.Gate)) (List.ofFn y)).length := by
            rw [l1]
            simp only [ρ]
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          have e2 : i = (PEqualNP.Outside.L_meta_8992.run gs (List.ofFn x)).length := by omega
          rw [e, PEqualNP.Outside.L_meta_8992.getD_at]
          conv_rhs => rw [e2, PEqualNP.Outside.L_meta_8992.getD_at]
          rw [List.map_map]
          congr 1
          exact List.map_congr_left fun k _ => ih k
        · have e : ρ i = i - 1 := by simp only [ρ]; rw [if_neg (by omega), if_neg (by omega)]
          rw [e, List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega), List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]
    exact key C.gates le_rfl C.output
