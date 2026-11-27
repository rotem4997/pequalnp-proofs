import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9113

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




def pf (x : Fin 14 → Bool) : Prop := ∃ (p : Fin 7) (l : Fin 7), (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
def inp (p l : Fin 7) : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p) || decide (i = Fin.natAdd 7 l)

theorem far : ∀ u v : Fin 14, ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ inp p l u = false ∧ inp p l v = false := by decide +kernel
theorem inpt (p l : Fin 7) : inp p l (Fin.castAdd 7 p) = true ∧ inp p l (Fin.natAdd 7 l) = true := by simp [inp]

theorem fin (C : Circuit) (h : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ pf x)
    (dep : ∃ u v : Fin 14, ∀ x y : Fin 14 → Bool, x u = y u → x v = y v → C.eval (List.ofFn x) = C.eval (List.ofFn y)) : False := by
  obtain ⟨u, v, hd⟩ := dep
  obtain ⟨p, l, h1, h2, h3⟩ := far u v
  have e := hd (inp p l) (fun _ => false) h2 h3
  have t1 : C.eval (List.ofFn (inp p l)) = true := (h _).2 ⟨p, l, h1, (inpt p l).1, (inpt p l).2⟩
  rw [e] at t1
  obtain ⟨_, _, _, h4, _⟩ := (h _).1 t1
  cases h4

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9113

theorem PEqualNP.Outside.L_meta_9113 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));               have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));               Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min x7 x8 + Max.max x7 x8) = Bool.true) →               (¬∃ (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x8) → ∃ (x9 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x10 : ℕ) => x10 == if x9 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true := by
  intro C _ hA _ _ hF _ hno
  exfalso
  have hlen : C.gates.length ≤ 1 := by
    by_contra h
    exact hno ⟨C.gates[1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  refine PEqualNP.Outside.L_meta_9113.fin C hF ?_
  have ev : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = (PEqualNP.Outside.L_meta_9113.run C.gates (List.ofFn x)).getD C.output false := fun _ => rfl
  have g : ∀ (x : Fin 14 → Bool) i (hi : i < 14), (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
  rcases Nat.lt_or_ge C.output 14 with ho | ho
  · refine ⟨⟨C.output, ho⟩, ⟨C.output, ho⟩, fun x y h _ => ?_⟩
    rw [ev, ev, PEqualNP.Outside.L_meta_9113.run_input _ _ _ (by rw [List.length_ofFn]; exact ho), PEqualNP.Outside.L_meta_9113.run_input _ _ _ (by rw [List.length_ofFn]; exact ho), g x _ ho, g y _ ho, h]
  by_cases hlt : C.output < 14 + C.gates.length
  · have hj0 : C.output = 14 + 0 := by omega
    have h0 : 0 < C.gates.length := by omega
    obtain ⟨_, hR, hL⟩ := hA
    have hl := hL _ (List.getElem_mem h0)
    have hi := hR 0 h0
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C 0 = C.gates[0] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, h0]
    rw [hga] at hi
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
    have ha : a < 14 := hi a (by rw [hab]; simp)
    have hb : b < 14 := hi b (by rw [hab]; simp)
    have e1 : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = C.gates[0].op.eval [x ⟨a, ha⟩, x ⟨b, hb⟩] := by
      intro x
      have h := PEqualNP.Outside.L_meta_9113.run_gate C.gates (List.ofFn x) 0 h0
      rw [List.length_ofFn] at h
      rw [ev, hj0, h, hab]
      simp only [List.map_cons, List.map_nil]
      rw [if_pos (by omega), if_pos (by omega), PEqualNP.Outside.L_meta_9113.run_input _ _ _ (by rw [List.length_ofFn]; exact ha), PEqualNP.Outside.L_meta_9113.run_input _ _ _ (by rw [List.length_ofFn]; exact hb), g x a ha, g x b hb]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun x y h1 h2 => by rw [e1, e1, h1, h2]⟩
  · refine ⟨0, 0, fun x y _ _ => ?_⟩
    rw [ev, ev, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_9113.run_length, List.length_ofFn]; omega), List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_9113.run_length, List.length_ofFn]; omega)]
