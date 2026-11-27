import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3626
open PEqualNP.CircuitLowerBounds

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

def EV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem fl_snoc (F : List Bool → Gate → Bool) (l : List Gate) (g : Gate) (w : List Bool) :
    fl F (l ++ [g]) w = fl F l w ++ [F (fl F l w) g] := by
  rw [fl_append]; rfl

theorem notonly (m : ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.op = GateOp.not) → ∀ i : ℕ,
    (∃ b : Bool, ∀ l : List Bool, l.length = m → (fl EV gs l).getD i false = b) ∨
    (∃ p, p < m ∧ ∃ c : Bool, ∀ l : List Bool, l.length = m →
      (fl EV gs l).getD i false = (c != l.getD p false)) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i
    by_cases hi : i < m
    · right
      refine ⟨i, hi, false, ?_⟩
      intro l _
      show l.getD i false = (false != l.getD i false)
      cases l.getD i false <;> rfl
    · left
      refine ⟨false, ?_⟩
      intro l hl
      show l.getD i false = false
      exact List.getD_eq_default _ _ (by omega)
  | append_singleton gs g ih =>
    intro hall i
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.not := fun g' h => hall g' (List.mem_append_left _ h)
    have hg : g.op = GateOp.not := hall g (List.mem_append_right _ (List.mem_singleton.2 rfl))
    have ih' := ih hgs
    have hlen : ∀ l : List Bool, l.length = m → (fl EV gs l).length = m + gs.length := by
      intro l hl; rw [fl_len, hl]
    rcases Nat.lt_trichotomy i (m + gs.length) with hi | hi | hi
    · rcases ih' i with ⟨b, hb⟩ | ⟨p, hp, c, hc⟩
      · left
        refine ⟨b, ?_⟩
        intro l hl
        rw [fl_snoc, getD_snoc_lt _ _ _ (by rw [hlen l hl]; exact hi)]
        exact hb l hl
      · right
        refine ⟨p, hp, c, ?_⟩
        intro l hl
        rw [fl_snoc, getD_snoc_lt _ _ _ (by rw [hlen l hl]; exact hi)]
        exact hc l hl
    · have hval : ∀ l : List Bool, l.length = m →
          (fl EV (gs ++ [g]) l).getD i false = EV (fl EV gs l) g := by
        intro l hl
        rw [fl_snoc, hi, ← hlen l hl]
        exact getD_snoc_eq _ _
      cases hin : g.inputs with
      | nil =>
        left
        refine ⟨true, ?_⟩
        intro l hl
        rw [hval l hl]
        unfold EV
        rw [hg, hin]
        rfl
      | cons a t =>
        have hev : ∀ l : List Bool, EV (fl EV gs l) g = !(fl EV gs l).getD a false := by
          intro l
          unfold EV
          rw [hg, hin]
          rfl
        rcases ih' a with ⟨b, hb⟩ | ⟨p, hp, c, hc⟩
        · left
          refine ⟨!b, ?_⟩
          intro l hl
          rw [hval l hl, hev l, hb l hl]
        · right
          refine ⟨p, hp, !c, ?_⟩
          intro l hl
          rw [hval l hl, hev l, hc l hl]
          cases c <;> cases l.getD p false <;> rfl
    · left
      refine ⟨false, ?_⟩
      intro l hl
      rw [fl_snoc, getD_snoc_gt _ _ _ (by rw [hlen l hl]; exact hi)]

end PEqualNP.Outside.L_meta_3626

open PEqualNP.Outside.L_meta_3626 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3626 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates := by
  intro cnt n z C xs hF f h1 h2
  by_cases hc : 1 ≤ cnt C.gates
  · exact ⟨⟨[], 0⟩, fun g hg => absurd hg List.not_mem_nil, hc⟩
  · exfalso
    have h0 : cnt C.gates = 0 := by omega
    have h0' := List.countP_eq_zero.1 (show List.countP _ C.gates = 0 from h0)
    have key : ∀ op : GateOp, ¬ (GateOp.rec (motive := fun _ => Bool) true true false
        (fun _ => true) true op) = true → op = GateOp.not := by
      intro op h
      cases op <;> first | rfl | exact absurd rfl h
    have hall : ∀ g ∈ C.gates, g.op = GateOp.not := fun g hg => key g.op (h0' g hg)
    have hf : ∀ y : Fin (n + 1) → Bool,
        f y = (fl EV C.gates (List.map y xs)).getD C.output false := fun _ => rfl
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, w, hvw⟩ := h2
    rw [hf, hf] at hu
    rw [hf, hf] at hvw
    rcases notonly xs.length C.gates hall C.output with ⟨b, hb⟩ | ⟨p, hp, c, hcc⟩
    · apply hu
      rw [hb _ (by simp), hb _ (by simp)]
    · have hget : ∀ y : Fin (n + 1) → Bool, (List.map y xs).getD p false = y xs[p] := by
        intro y
        rw [List.getD_eq_getElem _ _ (by simp; exact hp)]
        simp
      rw [hcc _ (by simp), hcc _ (by simp), hget, hget] at hu
      rw [hcc _ (by simp), hcc _ (by simp), hget, hget] at hvw
      by_cases hz : xs[p] = z
      · apply hvw
        rw [hz, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
      · apply hu
        rw [Function.update_of_ne hz, Function.update_of_ne hz]
