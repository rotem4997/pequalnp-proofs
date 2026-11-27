import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- With vertex 0 false the Petersen function is the twelve-edge function of the other nine
-- vertices, and the given wire (vertex 0 OR vertex 2) is vertex 2 itself. That function needs
-- 15 gates even with one extra false input: base is the statement of the checked L_meta_2317,
-- after renaming the vertices. fixZero: every gate that reads an input wire carrying vertex 0
-- goes away and none is added. So four such gates among 18 would leave at most 14.
-- What remains is fewReaders: at most three gates read a wire carrying vertex 0.
theorem PEqualNP.Outside.R_meta_1888_386
    (base : ∀ (C : Circuit), FanInTwo C →
      (∀ (x : Fin 9 → Bool), C.eval (List.ofFn x ++ [false]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 15 ≤ C.size)
    (fixZero : ∀ (C : Circuit) (s : Fin 10 → Fin 10), FanInTwo C →
      (∃ c : Bool, ∀ x : Fin 10 → Bool, x 0 = false →
        C.eval (List.ofFn (x ∘ s) ++ [x 0 || x 2]) = c) ∨
      ∃ E : Circuit, FanInTwo E ∧
        E.size + (C.gates.filter (fun g : Gate => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any (fun i => (List.ofFn s).getD i 1 == 0))).length ≤ C.size ∧
        ∀ x : Fin 10 → Bool, x 0 = false →
          E.eval (List.ofFn (fun j : Fin 9 => x (([2, 3, 8, 6, 1, 7, 4, 5, 9] : List (Fin 10)).getD j.val 0)) ++ [false]) =
            C.eval (List.ofFn (x ∘ s) ++ [x 0 || x 2]))
    (fewReaders : ∀ (C : Circuit) (s : Fin 10 → Fin 10), FanInTwo C → C.size ≤ 18 →
      (C.gates.filter (fun g : Gate => g.inputs.any (fun i => (List.ofFn s).getD i 1 == 0))).length ≤ 3 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ s) ++ [x 0 || x 2]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C s hfan hsize
  by_contra hne
  have hall : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ s) ++ [x 0 || x 2]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  have hgate : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      ∀ Fv : ℕ → Bool,
      g.op.eval ((if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).map Fv)
        = g.op.eval (g.inputs.map Fv) := by
    intro g hg Fv
    obtain ⟨op, inputs⟩ := g
    rcases hg with h | h | h
    · have e : op = GateOp.and := h
      subst e
      rfl
    · have e : op = GateOp.or := h
      subst e
      rfl
    · have e : op = GateOp.not := h
      subst e
      cases inputs <;> rfl
  have hw : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
      ∀ w : List Bool,
      (gs.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    intro gs
    induction gs with
    | nil => intro _ w; rfl
    | cons g gs ih =>
      intro hg w
      have e : w ++ [g.op.eval ((if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).map
          fun i => w.getD i false)] = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] :=
        congrArg (fun v => w ++ [v]) (hgate g (hg g List.mem_cons_self) (fun i => w.getD i false))
      exact (congrArg (fun u => (gs.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u) e).trans
        (ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _)
  have key : ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size ∧
      (∀ w : List Bool, C'.eval w = C.eval w) ∧
      (C'.gates.filter (fun g : Gate => g.inputs.any (fun i => (List.ofFn s).getD i 1 == 0))).length = (C.gates.filter (fun g : Gate => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any (fun i => (List.ofFn s).getD i 1 == 0))).length := by
    refine ⟨⟨C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate)), C.output⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      refine ⟨(hfan g0 hg0).1, ?_⟩
      show (if g0.op.eval [false] = true then g0.inputs.take 1 else g0.inputs).length ≤ 2
      split_ifs
      · simp only [List.length_take]
        omega
      · exact (hfan g0 hg0).2
    · exact List.length_map _
    · intro w
      show ((C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD C.output false
        = (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD C.output false
      rw [hw C.gates (fun g hg => (hfan g hg).1) w]
    · show ((C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).filter (fun g : Gate => g.inputs.any (fun i => (List.ofFn s).getD i 1 == 0))).length = _
      rw [List.filter_map, List.length_map]
      rfl
  obtain ⟨C', hfan', hsize', heval', hcount⟩ := key
  by_cases hr : (C'.gates.filter (fun g : Gate => g.inputs.any (fun i => (List.ofFn s).getD i 1 == 0))).length ≤ 3
  · obtain ⟨x, hx⟩ := fewReaders C' s hfan' (by omega) hr
    exact hx ((heval' _).trans (hall x))
  · rw [hcount] at hr
    rcases fixZero C s hfan with ⟨c, hc⟩ | ⟨E, hE, hEs, hEf⟩
    · have h0 : c = false := by
        rw [← hc (fun _ => false) rfl, hall (fun _ => false)]
        rfl
      have h1 : c = true := by
        rw [← hc (fun i => decide (i ≠ 0)) rfl, hall (fun i => decide (i ≠ 0))]
        rfl
      exact absurd (h0.symm.trans h1) (by decide)
    · have h15 := base E hE (fun y => by
        have hx0 : (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0)) 0 = false := rfl
        have hin : (fun j : Fin 9 => (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0)) (([2, 3, 8, 6, 1, 7, 4, 5, 9] : List (Fin 10)).getD j.val 0)) = y := by
          funext j
          fin_cases j <;> rfl
        have h1 := hEf (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0)) hx0
        rw [hin] at h1
        rw [h1, hall (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0))]
        have taut : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
            (false && b4 || b4 && b0 || b0 && b1 || b1 && b6 || b6 && false || false && b7 || b4 && b3 || b0 && b5 || b1 && b2 || b6 && b8 || b7 && b5 || b5 && b8 || b8 && b3 || b3 && b2 || b2 && b7)
            = (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by decide
        exact taut (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))
      omega
