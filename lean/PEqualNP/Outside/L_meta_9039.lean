import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9039

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




def ptf : (Fin 10 → Bool) → Bool := (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))
def eg : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def inp (e : Fin 10 × Fin 10) : Fin 10 → Bool := fun i => decide (i = e.1) || decide (i = e.2)

theorem far : ∀ u v : Fin 10, ∃ e ∈ eg, ptf (inp e) = true ∧ inp e u = false ∧ inp e v = false := by decide +kernel
theorem zero : ptf (fun _ => false) = false := by decide +kernel

theorem fin (C : Circuit) (h : ∀ x, C.eval (List.ofFn x) = ptf x)
    (dep : ∃ u v : Fin 10, ∀ x y : Fin 10 → Bool, x u = y u → x v = y v → C.eval (List.ofFn x) = C.eval (List.ofFn y)) : False := by
  obtain ⟨u, v, hd⟩ := dep
  obtain ⟨e, _, h1, h2, h3⟩ := far u v
  have := hd (inp e) (fun _ => false) h2 h3
  rw [h, h, h1, zero] at this
  cases this

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9039

theorem PEqualNP.Outside.L_meta_9039 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (10 : ℕ) ≤ x1.output → (∀ x5 ∈ x1.gates, ∀ x7 ∈ x5.inputs, x7 < (10 : ℕ)) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C hC _ ho hin
  by_contra hcon
  push Not at hcon
  refine PEqualNP.Outside.L_meta_9039.fin C hcon ?_
  have ev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (PEqualNP.Outside.L_meta_9039.run C.gates (List.ofFn x)).getD C.output false := fun _ => rfl
  by_cases hlt : C.output < 10 + C.gates.length
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le ho
    have hjl : j < C.gates.length := by omega
    have e1 : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = C.gates[j].op.eval (C.gates[j].inputs.map fun i => (List.ofFn x).getD i false) := by
      intro x
      have h := PEqualNP.Outside.L_meta_9039.run_gate C.gates (List.ofFn x) j hjl
      rw [List.length_ofFn] at h
      rw [ev, hj, h]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      have hi10 := hin _ (List.getElem_mem hjl) i hi
      rw [if_pos (by omega), PEqualNP.Outside.L_meta_9039.run_input _ _ _ (by rw [List.length_ofFn]; exact hi10)]
    have g : ∀ (x : Fin 10 → Bool) i (hi : i < 10), (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
      intro x i hi
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
    have hl := (hC _ (List.getElem_mem hjl)).2
    have hi := hin _ (List.getElem_mem hjl)
    rcases hm : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact ⟨0, 0, fun x y _ _ => by rw [e1, e1, hm]; rfl⟩
    · rw [hm] at hi
      have ha := hi a (by simp)
      refine ⟨⟨a, ha⟩, ⟨a, ha⟩, fun x y h1 _ => ?_⟩
      rw [e1, e1, hm]
      simp only [List.map_cons, List.map_nil, g _ a ha, h1]
    · rw [hm] at hi
      have ha := hi a (by simp)
      have hb := hi b (by simp)
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun x y h1 h2 => ?_⟩
      rw [e1, e1, hm]
      simp only [List.map_cons, List.map_nil, g _ a ha, g _ b hb, h1, h2]
    · rw [hm] at hl; simp at hl
  · refine ⟨0, 0, fun x y _ _ => ?_⟩
    rw [ev, ev, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_9039.run_length, List.length_ofFn]; omega), List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_9039.run_length, List.length_ofFn]; omega)]
