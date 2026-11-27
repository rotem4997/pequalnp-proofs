import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2181_aux

private abbrev F := (Fin 9 → Bool) → Bool

private def low : F := fun _ => false
private def high : F := fun _ => true

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

private def next (g : Gate) (w : List F) : F :=
  fun x => g.op.eval (g.inputs.map (fun i => w.getD i low x))

private def generate (w : List F) : List Gate → List F
  | [] => []
  | g :: gs => next g w :: generate (w ++ [next g w]) gs

private theorem generate_length (w : List F) (gs : List Gate) :
    (generate w gs).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [generate, ih]

private def shape (w : List F) (v : F) : Prop :=
  ∃ a ∈ low :: high :: w, ∃ b ∈ low :: high :: w,
    (v = fun x => a x && b x) ∨
    (v = fun x => a x || b x) ∨
    (v = fun x => !a x)

private theorem get_mem (w : List F) (i : ℕ) :
    w.getD i low ∈ low :: w := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    exact List.mem_cons_self

private theorem next_shape (g : Gate) (w : List F)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2) :
    shape w (next g w) := by
  have hm (i : ℕ) : w.getD i low ∈ low :: high :: w := by
    rcases List.mem_cons.mp (get_mem w i) with h | h
    · rw [h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  obtain ⟨op, ins⟩ := g
  change op = .and ∨ op = .or ∨ op = .not at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact ⟨high, by simp, high, by simp, Or.inl rfl⟩
    · refine ⟨_, hm i, _, hm i, Or.inl ?_⟩
      funext x
      simp [next, GateOp.eval]
    · refine ⟨_, hm i, _, hm j, Or.inl ?_⟩
      funext x
      simp [next, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact ⟨low, by simp, low, by simp, Or.inr (Or.inl rfl)⟩
    · refine ⟨_, hm i, _, hm i, Or.inr (Or.inl ?_)⟩
      funext x
      simp [next, GateOp.eval]
    · refine ⟨_, hm i, _, hm j, Or.inr (Or.inl ?_)⟩
      funext x
      simp [next, GateOp.eval]
    · simp at hlen
  · cases ins with
    | nil => exact ⟨low, by simp, low, by simp, Or.inr (Or.inr rfl)⟩
    | cons i rest => exact ⟨_, hm i, low, by simp, Or.inr (Or.inr rfl)⟩

private theorem generate_shape (w : List F) (gs : List Gate)
    (h : FanInTwo ⟨gs, 0⟩) (j : ℕ) (hj : j < (generate w gs).length) :
    shape (w ++ (generate w gs).take j) (generate w gs)[j] := by
  induction gs generalizing w j with
  | nil => simp [generate] at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have hg := h g List.mem_cons_self
      simpa [generate] using next_shape g w (by simpa using hg.1) hg.2
    | succ j =>
      have hj' : j < (generate (w ++ [next g w]) gs).length := by
        simpa [generate] using hj
      have ht : FanInTwo ⟨gs, 0⟩ := fun a ha => h a (List.mem_cons_of_mem _ ha)
      simpa [generate, List.take_succ_cons, List.append_assoc] using
        ih (w ++ [next g w]) ht j hj'

private theorem next_eval (g : Gate) (w : List F) (x : Fin 9 → Bool) :
    next g w x = g.op.eval (g.inputs.map (fun i => (w.map (fun a => a x)).getD i false)) := by
  unfold next
  congr 1
  apply List.map_congr_left
  intro i _
  exact (List.getD_map w low (fun a => a x)).symm

private theorem generate_eval (w : List F) (gs : List Gate) (x : Fin 9 → Bool) :
    (w ++ generate w gs).map (fun a => a x) = run gs (w.map (fun a => a x)) := by
  induction gs generalizing w with
  | nil => simp [generate, run, Circuit.wires]
  | cons g gs ih =>
    calc
      (w ++ generate w (g :: gs)).map (fun a => a x) =
          ((w ++ [next g w]) ++ generate (w ++ [next g w]) gs).map (fun a => a x) := by
        simp [generate, List.append_assoc]
      _ = run gs ((w ++ [next g w]).map (fun a => a x)) := ih _
      _ = run (g :: gs) (w.map (fun a => a x)) := by
        rw [List.map_append]
        simp only [List.map_cons, List.map_nil, next_eval]
        rfl

private theorem result (C : Circuit) (w : List F) (h : FanInTwo C) :
    ∃ gs : List F, gs.length = C.size ∧
      (∀ j : Fin gs.length, shape (w ++ gs.take j.val) (gs.get j)) ∧
      (fun x => C.eval (w.map (fun f => f x))) ∈ low :: (w ++ gs) := by
  refine ⟨generate w C.gates, generate_length w C.gates, ?_, ?_⟩
  · intro j
    exact generate_shape w C.gates h j.val j.isLt
  · have he : (fun x => C.eval (w.map (fun f => f x))) =
        (w ++ generate w C.gates).getD C.output low := by
      funext x
      change (run C.gates (w.map (fun f => f x))).getD C.output false = _
      rw [← generate_eval]
      exact List.getD_map _ low _
    rw [he]
    exact get_mem _ _

end PEqualNP.Outside.L_meta_2181_aux

theorem PEqualNP.Outside.L_meta_2181 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ((Fin (9 : ℕ) → Bool) → Bool)),   PEqualNP.MetaComplexity.FanInTwo x1 →     ∃ (x4 : List ((Fin (9 : ℕ) → Bool) → Bool)),       x4.length = x1.size ∧         (∀ (x5 : Fin x4.length),             have x6 : List ((Fin (9 : ℕ) → Bool) → Bool) := (fun (x6 : Fin (9 : ℕ) → Bool) => Bool.false) :: (fun (x6 : Fin (9 : ℕ) → Bool) => Bool.true) :: (x2 ++ List.take (↑x5) x4);             ∃ x7 ∈ x6, ∃ x8 ∈ x6, (x4.get x5 = fun (x9 : Fin (9 : ℕ) → Bool) => x7 x9 && x8 x9) ∨ (x4.get x5 = fun (x9 : Fin (9 : ℕ) → Bool) => x7 x9 || x8 x9) ∨ x4.get x5 = fun (x9 : Fin (9 : ℕ) → Bool) => !x7 x9) ∧           (fun (x5 : Fin (9 : ℕ) → Bool) => x1.eval (List.map (fun (x6 : (Fin (9 : ℕ) → Bool) → Bool) => x6 x5) x2)) ∈ (fun (x5 : Fin (9 : ℕ) → Bool) => Bool.false) :: (x2 ++ x4) := by
  intro C w hC
  exact L_meta_2181_aux.result C w hC

