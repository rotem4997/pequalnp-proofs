import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6957

open PEqualNP.CircuitLowerBounds

def X1 (x1 : Bool) (x2 : Bool × Bool × ℕ) : Gate :=
  if x1 = x2.1 then { op := if x2.2.1 = Bool.true then GateOp.and else GateOp.or, inputs := [] }
  else { op := GateOp.or, inputs := [x2.2.2] }

noncomputable def touched (x6 : Gate) : Bool :=
  (GateOp.rec (motive := fun _ => List ℕ) x6.inputs x6.inputs (List.take 1 x6.inputs)
    (fun _ => x6.inputs) x6.inputs x6.op).contains 0 ||
  (GateOp.rec (motive := fun _ => List ℕ) x6.inputs x6.inputs (List.take 1 x6.inputs)
    (fun _ => x6.inputs) x6.inputs x6.op).contains 10

def dn (i : ℕ) : ℕ := if i < 10 then i - 1 else i - 2
def up (j : ℕ) : ℕ := if j < 9 then j + 1 else j + 2

def oth (g : Gate) : ℕ := (g.inputs.filter (fun i => !(i == 0) && !(i == 10))).headD 0

def val (g : Gate) (x wv : Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => if i = 0 then x else if i = 10 then !x else wv)

def choice (g : Gate) : Gate ⊕ (Bool × Bool × ℕ) :=
  if val g false false = val g false true then
    if val g true false = val g true true then
      if val g false false = val g true false then
        Sum.inl ⟨if val g false false then GateOp.and else GateOp.or, []⟩
      else Sum.inr (val g true false, true, 100)
    else Sum.inr (false, val g false false, dn (oth g))
  else Sum.inr (true, val g true false, dn (oth g))

noncomputable def tr (g : Gate) : Gate ⊕ (Bool × Bool × ℕ) :=
  if touched g then choice g else Sum.inl ⟨g.op, g.inputs.map dn⟩

def ev (V : List Bool) (G : Gate) : Bool := G.op.eval (G.inputs.map fun i => V.getD i false)

def R (x : Bool) (W V : List Bool) : Prop :=
  W.length = V.length + 2 ∧ 9 ≤ V.length ∧ W.getD 0 false = x ∧ W.getD 10 false = !x ∧
    ∀ j, V.getD j false = W.getD (up j) false

theorem getD_snoc (l : List Bool) (a : Bool) (i : ℕ) :
    (l ++ [a]).getD i false = if i < l.length then l.getD i false else if i = l.length then a else false := by
  rcases lt_trichotomy i l.length with h | h | h
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ i < l.length := by omega
    have h2 : i ≠ l.length := by omega
    simp only [h1, h2, if_false]
    rw [List.getD_eq_default]
    simp; omega

theorem R_snoc {x : Bool} {W V : List Bool} (h : R x W V) (a : Bool) : R x (W ++ [a]) (V ++ [a]) := by
  obtain ⟨hl, h9, h0, h10, hj⟩ := h
  refine ⟨by simp [hl], by simp; omega, ?_, ?_, ?_⟩
  · rw [getD_snoc, if_pos (by omega), h0]
  · rw [getD_snoc, if_pos (by omega), h10]
  · intro j
    rw [getD_snoc, getD_snoc, hj j]
    unfold up
    split_ifs <;> first | rfl | omega

theorem R_get {x : Bool} {W V : List Bool} (h : R x W V) (i : ℕ) (h0 : i ≠ 0) (h10 : i ≠ 10) :
    W.getD i false = V.getD (dn i) false := by
  rw [h.2.2.2.2 (dn i)]
  congr 1
  unfold up dn
  split_ifs <;> omega

theorem R_big {x : Bool} {W V : List Bool} (h : R x W V) (hV : V.length ≤ 100) :
    V.getD 100 false = false := by
  rw [List.getD_eq_default]; omega

theorem gate_ok (x : Bool) (W V : List Bool) (hR : R x W V) (hV : V.length ≤ 100) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hl : g.inputs.length ≤ 2) :
    ev V (Sum.elim id (X1 x) (tr g)) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  have h0 : W.getD 0 false = x := hR.2.2.1
  have h10 : W.getD 10 false = !x := hR.2.2.2.1
  have hd := R_get hR
  have hb := R_big hR hV
  simp only [List.getD_eq_getElem?_getD] at h0 h10 hb hd
  obtain ⟨op, ins⟩ := g
  simp only at hop hl
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [tr, touched, ev, GateOp.eval]
  · by_cases ha0 : a = 0
    · subst ha0
      rcases hop with rfl | rfl | rfl <;> cases x <;>
        simp [tr, touched, choice, val, oth, X1, ev, GateOp.eval, h0, h10, hb]
    · by_cases ha10 : a = 10
      · subst ha10
        rcases hop with rfl | rfl | rfl <;> cases x <;>
          simp [tr, touched, choice, val, oth, X1, ev, GateOp.eval, h0, h10, hb]
      · have ha0' : ¬ 0 = a := fun h => ha0 h.symm
        have ha10' : ¬ 10 = a := fun h => ha10 h.symm
        rcases hop with rfl | rfl | rfl <;>
          simp [tr, touched, ev, GateOp.eval, ha0, ha10, ha0', ha10', hd a ha0 ha10]
  · obtain rfl | rfl | ⟨ha0, ha10, ha0', ha10'⟩ : a = 0 ∨ a = 10 ∨ (a ≠ 0 ∧ a ≠ 10 ∧ 0 ≠ a ∧ 10 ≠ a) := by
      omega
    all_goals obtain rfl | rfl | ⟨hb0, hb10, hb0', hb10'⟩ :
      b = 0 ∨ b = 10 ∨ (b ≠ 0 ∧ b ≠ 10 ∧ 0 ≠ b ∧ 10 ≠ b) := by omega
    all_goals rcases hop with rfl | rfl | rfl
    all_goals cases x
    all_goals simp_all [tr, touched, choice, val, oth, X1, ev, GateOp.eval]
  · simp at hl

theorem fanin_split (op : GateOp) (h : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
  simpa [Set.mem_insert_iff] using h

def Fo (W : List Bool) (g : Gate) : List Bool := W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

theorem fold_R (x : Bool) (gs : List Gate)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (W V : List Bool) (hR : R x W V) (hV : V.length + gs.length ≤ 100) :
    R x (gs.foldl Fo W) ((gs.map fun g => Sum.elim id (X1 x) (tr g)).foldl Fo V) := by
  induction gs generalizing W V with
  | nil => simpa using hR
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hf g (by simp)
    have e := gate_ok x W V hR (by simp at hV; omega) g (fanin_split _ hg.1) hg.2
    apply ih (fun g' hg' => hf g' (by simp [hg']))
    · show R x (W ++ [_]) (V ++ [ev V (Sum.elim id (X1 x) (tr g))])
      rw [e]
      exact R_snoc hR _
    · simp only [Fo, List.length_append, List.length_singleton]
      simp at hV
      omega

theorem R_init (x : Bool) (V0 : List Bool) (hl : V0.length = 9) : R x (x :: V0 ++ [!x]) V0 := by
  refine ⟨by simp [hl], by omega, ?_, ?_, ?_⟩
  · rw [getD_snoc]; simp [hl]
  · rw [getD_snoc]; simp [hl]
  · intro j
    rw [getD_snoc]
    simp only [List.length_cons, hl]
    unfold up
    by_cases hj : j < 9
    · rw [if_pos hj, if_pos (by omega)]
      simp
    · rw [if_neg hj, if_neg (by omega), if_neg (by omega), List.getD_eq_default]
      omega

theorem main (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 18)
    (hc : List.countP touched C.gates ≤ 3)
    (hz : ∀ x7 : Bool, C.eval (x7 :: List.replicate 9 false ++ [!x7]) = false) :
    ∃ (x8 : List (Gate ⊕ Bool × Bool × ℕ)) (x9 : ℕ), x8.length ≤ 18 ∧
      List.countP Sum.isRight x8 ≤ 3 ∧
      PEqualNP.MetaComplexity.FanInTwo ⟨x8.map (Sum.elim id (X1 false)), x9⟩ ∧
      ∀ (x10 : Bool) (x11 : Fin 9 → Bool),
        (Circuit.mk (x8.map (Sum.elim id (X1 x10))) x9).eval (List.ofFn x11) =
          C.eval (x10 :: List.ofFn x11 ++ [!x10]) := by
  have hf' : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := hf
  have hsz : C.gates.length ≤ 18 := hs
  have hout : C.output ≠ 0 ∧ C.output ≠ 10 := by
    have key : ∀ x7 : Bool, R x7 (C.gates.foldl Fo (x7 :: List.replicate 9 false ++ [!x7]))
        ((C.gates.map fun g => Sum.elim id (X1 x7) (tr g)).foldl Fo (List.replicate 9 false)) :=
      fun x7 => fold_R x7 C.gates hf' _ _ (R_init x7 _ (by simp)) (by simp; omega)
    have ev7 : ∀ x7 : Bool, C.eval (x7 :: List.replicate 9 false ++ [!x7]) =
        (C.gates.foldl Fo (x7 :: List.replicate 9 false ++ [!x7])).getD C.output false := fun _ => rfl
    constructor
    · intro h
      have h1 := hz true
      rw [ev7, h, (key true).2.2.1] at h1
      exact absurd h1 (by decide)
    · intro h
      have h1 := hz false
      rw [ev7, h, (key false).2.2.2.1] at h1
      exact absurd h1 (by decide)
  refine ⟨C.gates.map tr, dn C.output, by simpa using hsz, ?_, ?_, ?_⟩
  · rw [List.countP_map]
    refine le_trans (List.countP_mono_left ?_) hc
    intro g _ h
    by_cases ht : touched g = true
    · exact ht
    · simp [Function.comp, tr, ht] at h
  · intro G hG
    simp only [List.map_map, List.mem_map] at hG
    obtain ⟨g, hg, rfl⟩ := hG
    have h2 := hf' g hg
    simp only [Function.comp, tr, choice]
    split_ifs <;> simp only [Sum.elim_inl, Sum.elim_inr, id, X1] <;> (try split_ifs) <;>
      first | (simp; done) | simpa [Set.mem_insert_iff] using h2
  · intro x10 x11
    have hF := fold_R x10 C.gates hf' _ _ (R_init x10 (List.ofFn x11) (by simp)) (by simp; omega)
    have e1 : (Circuit.mk ((C.gates.map tr).map (Sum.elim id (X1 x10))) (dn C.output)).eval
        (List.ofFn x11) = ((C.gates.map fun g => Sum.elim id (X1 x10) (tr g)).foldl Fo
          (List.ofFn x11)).getD (dn C.output) false := by
      simp only [Circuit.eval, Circuit.wires, List.map_map]
      rfl
    have e2 : C.eval (x10 :: List.ofFn x11 ++ [!x10]) =
        (C.gates.foldl Fo (x10 :: List.ofFn x11 ++ [!x10])).getD C.output false := rfl
    rw [e1, e2, R_get hF C.output hout.1 hout.2]

end PEqualNP.Outside.L_meta_6957

theorem PEqualNP.Outside.L_meta_6957 : have x1 : Bool → Bool × Bool × ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x1 : Bool) (x2 : Bool × Bool × ℕ) => if x1 = x2.1 then { op := if x2.2.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2.2.2] : PEqualNP.CircuitLowerBounds.Gate }; have x2 : Bool → List (PEqualNP.CircuitLowerBounds.Gate ⊕ Bool × Bool × ℕ) → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x2 : Bool) (x3 : List (PEqualNP.CircuitLowerBounds.Gate ⊕ Bool × Bool × ℕ)) (x4 : ℕ) => { gates := List.map (Sum.elim id (x1 x2)) x3, output := x4 : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (18 : ℕ) →       List.countP             (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) =>               have x7 : List ℕ := PEqualNP.CircuitLowerBounds.GateOp.rec x6.inputs x6.inputs (List.take (1 : ℕ) x6.inputs) (fun (x7 : ℕ) => x6.inputs) x6.inputs x6.op;               x7.contains (0 : ℕ) || x7.contains (10 : ℕ))             x3.gates ≤           (3 : ℕ) →         (∀ (x7 : Bool), x3.eval (x7 :: List.replicate (9 : ℕ) Bool.false ++ [!x7]) = Bool.false) → ∃ (x8 : List (PEqualNP.CircuitLowerBounds.Gate ⊕ Bool × Bool × ℕ)) (x9 : ℕ), x8.length ≤ (18 : ℕ) ∧ List.countP Sum.isRight x8 ≤ (3 : ℕ) ∧ PEqualNP.MetaComplexity.FanInTwo (x2 Bool.false x8 x9) ∧ ∀ (x10 : Bool) (x11 : Fin (9 : ℕ) → Bool), (x2 x10 x8 x9).eval (List.ofFn x11) = x3.eval (x10 :: List.ofFn x11 ++ [!x10]) := by
  intro x1 x2 C hf hs hc hz
  exact PEqualNP.Outside.L_meta_6957.main C hf hs hc hz
