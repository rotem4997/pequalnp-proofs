import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4680_aux

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp; omega

def sw : GateOp → GateOp
  | GateOp.and => GateOp.or
  | GateOp.or => GateOp.and
  | o => o

def rr (m w : ℕ) : ℕ := if w < m then w + 1 else 0

def dl : ℕ → List Gate → List Gate
  | _, [] => []
  | m, g :: gs => ⟨sw g.op, g.inputs.map (rr m)⟩ :: dl (m + 1) gs

theorem dl_length (m : ℕ) (gs : List Gate) : (dl m gs).length = gs.length := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih => simp [dl, ih]

theorem dl_get (gs : List Gate) (m i : ℕ) (h1 : i < (dl m gs).length) (h2 : i < gs.length) :
    ((dl m gs).get ⟨i, h1⟩).op = sw (gs.get ⟨i, h2⟩).op := by
  induction gs generalizing m i with
  | nil => simp at h2
  | cons g gs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (m + 1) i _ (by simpa using h2)

theorem sw_and (o : GateOp) : sw o = GateOp.and ↔ o = GateOp.or := by
  cases o <;> simp [sw]

theorem dl_mono (m : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ dl m gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing m with
  | nil => simp [dl]
  | cons g gs ih =>
    intro g' hg'
    simp only [dl, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · obtain ⟨h1, h2⟩ := h g (by simp)
      refine ⟨?_, by simpa using h2⟩
      simp at h1
      rcases h1 with h1 | h1 <;> simp [h1, sw]
    · exact ih (m + 1) (fun g hg => h g (by simp [hg])) g' hg'

def Inv (m : ℕ) (W W' : List Bool) : Prop :=
  W.length = m ∧ W'.length = m + 1 ∧ ∀ w, W'.getD (rr m w) false = !W.getD w false

theorem demorgan (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (l : List Bool) :
    (sw o).eval (l.map not) = !o.eval l := by
  rcases ho with rfl | rfl <;> simp only [sw, GateOp.eval, List.any_map, List.all_map] <;>
    induction l <;> simp_all

theorem inv_step (m : ℕ) (W W' : List Bool) (hI : Inv m W W') (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Inv (m + 1) (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
      (W' ++ [(sw g.op).eval ((g.inputs.map (rr m)).map fun i => W'.getD i false)]) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hv : (sw g.op).eval ((g.inputs.map (rr m)).map fun i => W'.getD i false)
      = !g.op.eval (g.inputs.map fun i => W.getD i false) := by
    rw [← demorgan g.op hg, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h3 i
  refine ⟨by simp [h1], by simp [h2], ?_⟩
  intro w
  rw [hv]
  unfold rr
  rcases lt_trichotomy w m with hw | rfl | hw
  · have := h3 w
    unfold rr at this
    rw [if_pos hw] at this
    rw [if_pos (by omega), List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
      this]
  · rw [if_pos (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp [h1, h2]
  · have := h3 m
    unfold rr at this
    rw [if_neg (lt_irrefl m), List.getD_eq_default W false (by omega)] at this
    rw [if_neg (by omega), List.getD_append W' _ false 0 (by omega), this,
      List.getD_eq_default (W ++ _) false (by simp; omega)]

theorem inv_run (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (m : ℕ) (W W' : List Bool) (hI : Inv m W W') :
    Inv (m + gs.length) (run gs W) (run (dl m gs) W') := by
  induction gs generalizing m W W' with
  | nil => simpa [run, Circuit.wires, dl] using hI
  | cons g gs ih =>
    rw [run_cons]
    simp only [dl]
    rw [run_cons]
    have := ih (fun g hg' => hg g (by simp [hg'])) (m + 1) _ _
      (inv_step m W W' hI g (hg g (by simp)))
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem inv_init (W : List Bool) : Inv W.length W (true :: W.map not) := by
  refine ⟨rfl, by simp, ?_⟩
  intro w
  unfold rr
  split_ifs with hw
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show W.length ≤ w by omega)]

end PEqualNP.Outside.L_meta_4680_aux

open PEqualNP.Outside.L_meta_4680_aux

theorem PEqualNP.Outside.L_meta_4680 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ Nat.card { x4 : Fin x3.gates.length // (x3.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and } ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x5 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.cases Bool.true (fun (x6 : Fin (26 : ℕ)) => !x4 x6) x5) = !PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 := by
  intro x1 hm
  have hg : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => by
    simpa using (hm g h).1
  refine ⟨⟨dl 26 x1.gates, rr (26 + x1.gates.length) x1.output⟩, dl_mono 26 _ hm, ?_, ?_⟩
  · apply le_of_eq
    rw [← Nat.card_coe_set_eq]
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (finCongr (dl_length 26 x1.gates)) (fun i => by
      show _ ↔ (x1.gates.get _).op = GateOp.or
      rw [← sw_and]
      exact Iff.of_eq (congrArg (· = GateOp.and) (dl_get x1.gates 26 i.1 i.2 _)))
  · intro x4
    have hW : List.ofFn (fun x5 : Fin (26 + 1) => Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5)
        = true :: (List.ofFn x4).map not := by
      rw [List.ofFn_succ]
      simp
    have h0 : Inv 26 (List.ofFn x4) (true :: (List.ofFn x4).map not) := by
      have := inv_init (List.ofFn x4)
      rwa [List.length_ofFn] at this
    obtain ⟨-, -, h3⟩ := inv_run x1.gates hg 26 _ _ h0
    have := h3 x1.output
    unfold circuitFun Circuit.eval
    rw [hW]
    exact this
