import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6539

open PEqualNP.CircuitLowerBounds

def Step (n : ℕ) (P : List (Fin n → Bool)) (v : Fin n → Bool) : Prop :=
  ∃ (x8 : ℕ) (x9 : ℕ),
    have x10 : Fin n → Bool := P.getD x8 fun (x10 : Fin n) => Bool.false;
    have x11 : Fin n → Bool := P.getD x9 fun (x11 : Fin n) => Bool.false;
    (v = fun (x13 : Fin n) => x10 x13 && x11 x13) ∨ (v = fun (x13 : Fin n) => x10 x13 || x11 x13) ∨ v = fun (x13 : Fin n) => !x10 x13

theorem getD_col {n : ℕ} (P : List (Fin n → Bool)) (i : ℕ) (j : Fin n) :
    (P.map fun x => x j).getD i false = P.getD i (fun _ => false) j := by
  induction P generalizing i with
  | nil => simp
  | cons a P ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem opt_col {n : ℕ} (o : Option (Fin n → Bool)) (t : Fin n) :
    (Option.map (fun x => x t) o).getD false = o.getD (fun _ => false) t := by
  cases o <;> rfl

theorem getD_out {n : ℕ} (P : List (Fin n → Bool)) (j : Fin n) :
    P.getD P.length (fun _ => false) j = false := by
  rw [List.getD_eq_default _ _ (le_refl _)]

theorem gate_step (n : ℕ) (P : List (Fin n → Bool)) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Step n P (fun j => g.op.eval (g.inputs.map fun i => (P.map fun x => x j).getD i false)) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨P.length, P.length, Or.inr (Or.inr ?_)⟩
      funext t; simp [GateOp.eval, getD_out]
    · refine ⟨P.length, P.length, Or.inl ?_⟩
      funext t; simp [GateOp.eval, getD_out]
    · refine ⟨P.length, P.length, Or.inr (Or.inr ?_)⟩
      funext t; simp [GateOp.eval, getD_out]
  | [a], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨a, a, Or.inl ?_⟩
      funext t; simp [GateOp.eval, opt_col]
    · refine ⟨a, a, Or.inr (Or.inl ?_)⟩
      funext t; simp [GateOp.eval, opt_col]
    · refine ⟨a, a, Or.inr (Or.inr ?_)⟩
      funext t; simp [GateOp.eval, opt_col]
  | [a, b], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨a, b, Or.inl ?_⟩
      funext t; simp [GateOp.eval, opt_col]
    · refine ⟨a, b, Or.inr (Or.inl ?_)⟩
      funext t; simp [GateOp.eval, opt_col]
    · refine ⟨a, a, Or.inr (Or.inr ?_)⟩
      funext t; simp [GateOp.eval, opt_col]
  | _ :: _ :: _ :: _, h => simp at h

theorem core (n : ℕ) : ∀ (gs : List Gate) (W : List (Fin n → Bool)),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∃ x5 : List (Fin n → Bool), x5.length = gs.length ∧
      (∀ x6 < x5.length, Step n (W ++ x5.take x6) (x5.getD x6 fun _ => false)) ∧
      ∀ j : Fin n, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map fun x => x j) = (W ++ x5).map fun x => x j := by
  intro gs
  induction gs with
  | nil =>
    intro W _
    exact ⟨[], rfl, fun x6 h => absurd h (by simp), fun j => by simp⟩
  | cons g gs ih =>
    intro W hall
    let v : Fin n → Bool := fun j => g.op.eval (g.inputs.map fun i => (W.map fun x => x j).getD i false)
    obtain ⟨x5, hlen, hstep, hw⟩ := ih (W ++ [v]) (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
    refine ⟨v :: x5, by simp [hlen], ?_, ?_⟩
    · intro x6 hx6
      cases x6 with
      | zero =>
        rw [List.take_zero, List.append_nil, List.getD_cons_zero]
        exact gate_step n W g (hall g (List.mem_cons_self))
      | succ k =>
        have e : W ++ List.take (k + 1) (v :: x5) = (W ++ [v]) ++ List.take k x5 := by
          simp [List.take_succ_cons]
        rw [e, List.getD_cons_succ]
        exact hstep k (by simp at hx6; omega)
    · intro j
      rw [List.foldl_cons]
      have e : (W.map fun x => x j) ++ [g.op.eval (g.inputs.map fun i => (W.map fun x => x j).getD i false)]
          = (W ++ [v]).map fun x => x j := by simp [v]
      rw [e, hw j]
      simp

end PEqualNP.Outside.L_meta_6539

theorem PEqualNP.Outside.L_meta_6539 : ∀ (x1 : ℕ) (x2 : List (Fin x1 → Bool)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x3 →     ∃ (x5 : List (Fin x1 → Bool)),       x5.length = x3.size ∧         (∀ x6 < x5.length,             ∃ (x8 : ℕ) (x9 : ℕ),               have x10 : Fin x1 → Bool := (x2 ++ List.take x6 x5).getD x8 fun (x10 : Fin x1) => Bool.false;               have x11 : Fin x1 → Bool := (x2 ++ List.take x6 x5).getD x9 fun (x11 : Fin x1) => Bool.false;               have x12 : Fin x1 → Bool := x5.getD x6 fun (x12 : Fin x1) => Bool.false;               (x12 = fun (x13 : Fin x1) => x10 x13 && x11 x13) ∨ (x12 = fun (x13 : Fin x1) => x10 x13 || x11 x13) ∨ x12 = fun (x13 : Fin x1) => !x10 x13) ∧           ∀ (x6 : Fin x1), x3.eval (List.map (fun (x7 : Fin x1 → Bool) => x7 x6) x2) = (x2 ++ x5).getD x3.output (fun (x7 : Fin x1) => Bool.false) x6 := by
  intro x1 x2 x3 hF
  obtain ⟨x5, h1, h2, h3⟩ := PEqualNP.Outside.L_meta_6539.core x1 x3.gates x2 hF
  refine ⟨x5, h1, ?_, ?_⟩
  · intro x6 hx6
    exact h2 x6 hx6
  · intro x6
    show (x3.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (x2.map fun x7 => x7 x6)).getD x3.output false = _
    rw [h3 x6, PEqualNP.Outside.L_meta_6539.getD_col]
