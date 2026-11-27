import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6009

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- A missing wire reads as false.
def read (w : List Bool) (i : Option ℕ) : Bool :=
  i.elim false (fun j => w.getD j false)

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih]; simp; omega

theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

-- An OR gate ignores missing inputs. An AND gate with a missing input becomes an empty OR.
def mapGate (f : ℕ → Option ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.any (fun i => (f i).isNone) then ⟨.or, []⟩
            else ⟨.and, g.inputs.filterMap f⟩
  | op => ⟨op, g.inputs.filterMap f⟩

theorem mapped_inputs (f : ℕ → Option ℕ) (g : Gate) :
    (mapGate f g).inputs = [] ∨ (mapGate f g).inputs = g.inputs.filterMap f := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases h : ins.any (fun i => (f i).isNone) <;> simp [mapGate, h]

theorem mapGate_valid (f : ℕ → Option ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (mapGate f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (mapGate f g).inputs.length ≤ 2 := by
  constructor
  · rcases g with ⟨op, ins⟩
    have hop : op = .and ∨ op = .or := by simpa using hg.1
    rcases hop with rfl | rfl
    · cases h : ins.any (fun i => (f i).isNone) <;> simp [mapGate, h]
    · simp [mapGate]
  · rcases mapped_inputs f g with h | h
    · simp [h]
    · rw [h]
      exact (List.length_filterMap_le ..).trans hg.2

theorem any_project (f : ℕ → Option ℕ) (p : ℕ → Bool) (xs : List ℕ) :
    (xs.filterMap f).any p = xs.any (fun i => (f i).elim false p) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : f i <;> simp [h, ih]

theorem all_project (f : ℕ → Option ℕ) (p : ℕ → Bool) (xs : List ℕ) :
    ((xs.filterMap f).all p && !(xs.any (fun i => (f i).isNone))) =
      xs.all (fun i => (f i).elim false p) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : f i <;> simp [h, ← ih, Bool.and_assoc]

theorem mapGate_value (f : ℕ → Option ℕ) (g : Gate) (v : List Bool)
    (hop : g.op = .and ∨ g.op = .or) :
    value (mapGate f g) v = g.op.eval (g.inputs.map (fun i => read v (f i))) := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hop
  rcases hop with rfl | rfl
  · cases h : ins.any (fun i => (f i).isNone) <;>
      simpa [value, mapGate, h, GateOp.eval, List.all_map, Function.comp_def, read]
        using all_project f (fun i => v.getD i false) ins
  · simpa [value, mapGate, GateOp.eval, List.any_map, Function.comp_def, read]
      using any_project f (fun i => v.getD i false) ins

theorem bool_flow (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem gate_flow (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (p q : ℕ → Bool) (h : ∀ i, p i = t → q i = t) :
    op.eval (ins.map p) = t → op.eval (ins.map q) = t := by
  induction ins with
  | nil => exact id
  | cons i ins ih =>
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).2

def drop2 (a b : ℕ) (i : ℕ) : Option ℕ := if i = a ∨ i = b then none else some i

theorem drop2_spec (a b i : ℕ) : drop2 a b i = none ∨ drop2 a b i = some i := by
  unfold drop2; split_ifs <;> simp

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then x else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

-- Forcing wires to false only lowers the values of a monotone circuit.
theorem mono_run (f : ℕ → Option ℕ) (hf : ∀ i, f i = none ∨ f i = some i)
    (gs : List Gate) (w v : List Bool) (hlen : w.length = v.length)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h : ∀ i, v.getD i false = true → w.getD i false = true) :
    ∀ i, (run (gs.map (mapGate f)) v).getD i false = true →
      (run gs w).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, run_cons]
    have hg := hops g List.mem_cons_self
    have hstep : value (mapGate f g) v = true → value g w = true := by
      rw [mapGate_value f g v hg]
      apply gate_flow true g.op hg g.inputs
      intro i hi
      rcases hf i with h1 | h1
      · simp [h1, read] at hi
      · rw [h1] at hi; exact h i hi
    apply ih _ _ (by simp [hlen]) (fun a ha => hops a (List.mem_cons_of_mem _ ha))
    intro i hi
    rw [getD_snoc] at hi ⊢
    rw [← hlen] at hi
    split_ifs at hi ⊢ with h1 h2
    · exact h i hi
    · exact hstep hi

-- Below a bound where every forced wire is already false, nothing changes.
theorem eq_run (f : ℕ → Option ℕ) (hf : ∀ i, f i = none ∨ f i = some i) (B : ℕ)
    (gs : List Gate) (w v : List Bool) (hlen : w.length = v.length)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w.length + j)
    (hF : ∀ i < B, f i = none → (run gs w).getD i false = false)
    (h0 : ∀ i < w.length, i ≤ B → v.getD i false = w.getD i false) :
    ∀ i ≤ B, (run (gs.map (mapGate f)) v).getD i false = (run gs w).getD i false := by
  induction gs generalizing w v with
  | nil =>
    intro i hi
    by_cases hl : i < w.length
    · exact h0 i hl hi
    · change v.getD i false = w.getD i false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons g gs ih =>
    simp only [List.map_cons, run_cons]
    have hg := hops g List.mem_cons_self
    have hstep : w.length ≤ B → value (mapGate f g) v = value g w := by
      intro hB
      rw [mapGate_value f g v hg]
      unfold value
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' : i < w.length := by
        have := hrb 0 (by simp) i (by simpa using hi)
        simpa using this
      rcases hf i with h1 | h1
      · rw [h1]
        simp only [read, Option.elim_none]
        have := hF i (by omega) h1
        rw [run_cons, run_preserves _ _ _ (by simp; omega),
          List.getD_append _ _ _ _ hi'] at this
        exact this.symm
      · rw [h1]
        simp only [read, Option.elim_some]
        exact h0 i hi' (by omega)
    apply ih (w ++ [value g w]) (v ++ [value (mapGate f g) v]) (by simp [hlen])
      (fun a ha => hops a (List.mem_cons_of_mem _ ha))
    · intro j hj i hi
      have := hrb (j + 1) (by simp; omega) i (by simpa using hi)
      simp
      omega
    · intro i hi hn
      exact hF i hi hn
    · intro i hi hiB
      rw [getD_snoc, getD_snoc, ← hlen]
      simp only [List.length_append, List.length_singleton] at hi
      split_ifs with h1 h2
      · exact h0 i h1 hiB
      · exact hstep (by omega)
      · omega

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         x7.size = x2.size ∧           PEqualNP.MetaComplexity.Monotone2 x7 ∧             PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧               (∀ x8 ∈ x7.gates, x3 ∉ x8.inputs ∧ x4 ∉ x8.inputs) ∧                 ∀ (x8 : List Bool),                   x8.length = x1 →                     have x10 : Bool := (x2.wires x8).getD x3 Bool.false;                     have x11 : Bool := (x2.wires x8).getD x4 Bool.false;                     have x12 : Bool := (x7.wires x8).getD x3 Bool.false;                     have x13 : Bool := (x7.wires x8).getD x4 Bool.false;                     (x12 || x13) = (x10 || x11) ∧ (x10 = Bool.true → x11 = Bool.false → x12 = Bool.true ∧ x13 = Bool.false) ∧ (x11 = Bool.true → x10 = Bool.false → x13 = Bool.true ∧ x12 = Bool.false) := by
  intro x1 x2 x3 x4 hm hb
  let f := drop2 x3 x4
  have hf : ∀ i, f i = none ∨ f i = some i := drop2_spec x3 x4
  have hops : ∀ g ∈ x2.gates, g.op = .and ∨ g.op = .or := fun g hg => by
    simpa using (hm g hg).1
  refine ⟨⟨x2.gates.map (mapGate f), x2.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    exact mapGate_valid f q (hm q hq)
  · intro j hj i hi
    change j < (x2.gates.map (mapGate f)).length at hj
    rw [List.length_map] at hj
    unfold gateAt at hi
    change i ∈ ((x2.gates.map (mapGate f)).getD j ⟨GateOp.or, []⟩).inputs at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map] at hi
    apply hb j hj
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    rcases mapped_inputs f x2.gates[j] with h | h
    · simp [h] at hi
    · rw [h] at hi
      obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hi
      rcases hf a with h1 | h1
      · rw [h1] at hfa; cases hfa
      · rw [h1] at hfa; cases hfa; exact ha
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    have key : ∀ z, z ∈ (mapGate f q).inputs → z ≠ x3 ∧ z ≠ x4 := by
      intro z hz
      rcases mapped_inputs f q with h | h
      · simp [h] at hz
      · rw [h] at hz
        obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hz
        simp only [f, drop2] at hfa
        split_ifs at hfa with hc
        all_goals (cases hfa; exact not_or.mp hc)
    exact ⟨fun h => (key x3 h).1 rfl, fun h => (key x4 h).2 rfl⟩
  · intro x8 hx8
    dsimp only
    have hW : x2.wires x8 = run x2.gates x8 := rfl
    have hV : (Circuit.mk (x2.gates.map (mapGate f)) x2.output).wires x8 =
        run (x2.gates.map (mapGate f)) x8 := rfl
    rw [hW, hV]
    have hrb : ∀ j < x2.gates.length, ∀ i ∈ (x2.gates.getD j ⟨GateOp.or, []⟩).inputs,
        i < x8.length + j := by
      rw [hx8]; exact hb
    have mono := mono_run f hf x2.gates x8 x8 rfl hops (fun i h => h)
    have eqr := fun B hF => eq_run f hf B x2.gates x8 x8 rfl hops hrb hF (fun i _ _ => rfl)
    have E1 : ∀ i ≤ min x3 x4, (run (x2.gates.map (mapGate f)) x8).getD i false =
        (run x2.gates x8).getD i false := by
      apply eqr
      intro i hi hn
      exfalso
      simp only [f, drop2] at hn
      split_ifs at hn with hc
      · omega
    have E2 : (run x2.gates x8).getD (min x3 x4) false = false →
        ∀ i ≤ max x3 x4, (run (x2.gates.map (mapGate f)) x8).getD i false =
          (run x2.gates x8).getD i false := by
      intro h0
      apply eqr
      intro i hi hn
      simp only [f, drop2] at hn
      split_ifs at hn with hc
      · have : i = min x3 x4 := by omega
        rw [this]; exact h0
    rcases le_total x3 x4 with h | h
    · rw [min_eq_left h] at E1 E2
      rw [max_eq_right h] at E2
      have e1 := E1 x3 le_rfl
      have e2 := fun h0 => E2 h0 x4 le_rfl
      have m4 := mono x4
      revert e1 e2 m4
      generalize (run x2.gates x8).getD x3 false = a
      generalize (run x2.gates x8).getD x4 false = b
      generalize (run (x2.gates.map (mapGate f)) x8).getD x3 false = c
      generalize (run (x2.gates.map (mapGate f)) x8).getD x4 false = d
      cases a <;> cases b <;> cases c <;> cases d <;> simp
    · rw [min_eq_right h] at E1 E2
      rw [max_eq_left h] at E2
      have e1 := E1 x4 le_rfl
      have e2 := fun h0 => E2 h0 x3 le_rfl
      have m3 := mono x3
      revert e1 e2 m3
      generalize (run x2.gates x8).getD x3 false = a
      generalize (run x2.gates x8).getD x4 false = b
      generalize (run (x2.gates.map (mapGate f)) x8).getD x3 false = c
      generalize (run (x2.gates.map (mapGate f)) x8).getD x4 false = d
      cases a <;> cases b <;> cases c <;> cases d <;> simp

end PEqualNP.Outside.L_meta_6009

theorem PEqualNP.Outside.L_meta_6009 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         x7.size = x2.size ∧           PEqualNP.MetaComplexity.Monotone2 x7 ∧             PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧               (∀ x8 ∈ x7.gates, x3 ∉ x8.inputs ∧ x4 ∉ x8.inputs) ∧                 ∀ (x8 : List Bool),                   x8.length = x1 →                     have x10 : Bool := (x2.wires x8).getD x3 Bool.false;                     have x11 : Bool := (x2.wires x8).getD x4 Bool.false;                     have x12 : Bool := (x7.wires x8).getD x3 Bool.false;                     have x13 : Bool := (x7.wires x8).getD x4 Bool.false;                     (x12 || x13) = (x10 || x11) ∧ (x10 = Bool.true → x11 = Bool.false → x12 = Bool.true ∧ x13 = Bool.false) ∧ (x11 = Bool.true → x10 = Bool.false → x13 = Bool.true ∧ x12 = Bool.false) := by
  exact PEqualNP.Outside.L_meta_6009.main
