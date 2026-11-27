import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4909
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

def clipg (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (fun i => min i 24) }

theorem clip_get (X : List Bool) (hX : X.length ≤ 24) (i : ℕ) :
    X.getD (min i 24) false = X.getD i false := by
  by_cases h : i ≤ 24
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ hX,
      List.getD_eq_default _ _ (by omega)]

theorem clipw : ∀ (gs : List Gate) (X : List Bool), X.length + gs.length ≤ 24 →
    wf (gs.map clipg) X = wf gs X := by
  intro gs
  induction gs with
  | nil => intro X _; rfl
  | cons g gs ih =>
    intro X hX
    rw [List.length_cons] at hX
    have hv : (clipg g).op.eval ((clipg g).inputs.map fun i => X.getD i false)
        = g.op.eval (g.inputs.map fun i => X.getD i false) := by
      show g.op.eval ((g.inputs.map (fun i => min i 24)).map fun i => X.getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact clip_get X (by omega) i
    show wf (gs.map clipg) (X ++ [(clipg g).op.eval ((clipg g).inputs.map fun i => X.getD i false)])
      = wf gs (X ++ [g.op.eval (g.inputs.map fun i => X.getD i false)])
    rw [hv]
    apply ih
    rw [List.length_append]
    simp
    omega

def opc (o : GateOp) : Fin 3 :=
  match o with
  | GateOp.and => 0
  | GateOp.or => 1
  | _ => 2

def code (g : Gate) : Fin 3 × Fin 3 × Fin 25 × Fin 25 :=
  (opc g.op, ⟨min g.inputs.length 2, by omega⟩, ⟨min (g.inputs.getD 0 0) 24, by omega⟩,
    ⟨min (g.inputs.getD 1 0) 24, by omega⟩)

def dec (t : Fin 3 × Fin 3 × Fin 25 × Fin 25) : Gate :=
  { op := if t.1 = 0 then GateOp.and else if t.1 = 1 then GateOp.or else GateOp.not,
    inputs := List.take t.2.1.1 [t.2.2.1.1, t.2.2.2.1] }

theorem dec_code (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hl : g.inputs.length ≤ 2) :
    dec (code g) = clipg g := by
  obtain ⟨op, ins⟩ := g
  have hop' : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := hop
  have hins : List.take (min ins.length 2) [min (ins.getD 0 0) 24, min (ins.getD 1 0) 24]
      = ins.map (fun i => min i 24) := by
    match ins, hl with
    | [], _ => rfl
    | [a], _ => rfl
    | [a, b], _ => rfl
    | _ :: _ :: _ :: _, h => exact absurd h (by simp)
  have hopc : (if opc op = 0 then GateOp.and else if opc op = 1 then GateOp.or else GateOp.not) = op := by
    rcases hop' with h | h | h <;> rw [h] <;> rfl
  show Gate.mk (if opc op = 0 then GateOp.and else if opc op = 1 then GateOp.or else GateOp.not)
      (List.take (min ins.length 2) [min (ins.getD 0 0) 24, min (ins.getD 1 0) 24])
    = Gate.mk op (ins.map (fun i => min i 24))
  rw [hins, hopc]

end PEqualNP.Outside.L_meta_4909

open PEqualNP.Outside.L_meta_4909 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4909 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (13 : ℕ) →       ∃ (x4 : Fin (13 : ℕ) → Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)),         have x6 : Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ) → PEqualNP.CircuitLowerBounds.Gate := fun (x6 : Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) => { op := if x6.1 = (0 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.and else if x6.1 = (1 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not, inputs := List.take ↑x6.2.1 [↑x6.2.2.1, ↑x6.2.2.2] : PEqualNP.CircuitLowerBounds.Gate };         have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin (13 : ℕ)) => x6 (x4 x7), output := ↑x5 : PEqualNP.CircuitLowerBounds.Circuit };         ∀ (x8 : List Bool), x8.length = (11 : ℕ) → x7.eval x8 = x1.eval x8 := by
  intro C hF hsz
  have hlen : C.gates.length = 13 := hsz
  refine ⟨fun j => code (C.gates[j.1]'(by rw [hlen]; exact j.2)), ⟨min C.output 24, by omega⟩, ?_⟩
  intro _ _ X hX
  have hgs : List.ofFn (fun j : Fin 13 => dec (code (C.gates[j.1]'(by rw [hlen]; exact j.2))))
      = C.gates.map clipg := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_map]
    have hi : i < C.gates.length := by rw [List.length_map] at h2; exact h2
    exact dec_code _ (hF _ (List.getElem_mem hi)).1 (hF _ (List.getElem_mem hi)).2
  show (wf (List.ofFn (fun j : Fin 13 => dec (code (C.gates[j.1]'(by rw [hlen]; exact j.2))))) X).getD
    (min C.output 24) false = (wf C.gates X).getD C.output false
  rw [hgs, clipw C.gates X (by omega)]
  exact clip_get _ (by rw [wf_len]; omega) _
