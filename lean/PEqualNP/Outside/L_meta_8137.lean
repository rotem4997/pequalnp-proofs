import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8137

-- The fold lemmas below are taken from the checked file L_meta_6794.lean of this repository.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl
theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl
theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)
theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem wv_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) (u : ℕ) (hu : u < n) :
    BlindGate.wireValue C n z u = z ⟨u, hu⟩ := by
  unfold BlindGate.wireValue
  rw [wires_W, W_prefix _ _ _ (by simpa using hu)]
  exact ofFn_getD z u hu

theorem wv_ge {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) (h : n + C.gates.length ≤ w) :
    BlindGate.wireValue C n z w = false := by
  unfold BlindGate.wireValue
  rw [wires_W]
  exact W_ge _ _ _ (by simpa using h)

theorem wv_gate {n : ℕ} (C : Circuit) (hrb : ReadsBack n C) (z : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    BlindGate.wireValue C n z (n + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => BlindGate.wireValue C n z i) := by
  unfold BlindGate.wireValue
  have h := W_gate C.gates (List.ofFn z) j hj
  rw [List.length_ofFn] at h
  rw [wires_W, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < n + j := by
    have := hrb j hj i
    rw [gateAt_eq hj] at this
    exact this hi
  rw [if_pos hlt]

def R9 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (g : Gate) (c : ℕ), b = n + k ∧ C.gates[k]? = some g ∧
    (g.inputs = [a, c] ∨ g.inputs = [c, a]) ∧
    (g.op = GateOp.or ∨ g.op = GateOp.and ∧ BlindGate.wireValue C n x c = true)

def R10 (n : ℕ) (C : Circuit) (y : Fin n → Bool) (a b : ℕ) : Prop :=
  ∃ k : ℕ, b = n + k ∧ a ∈ (gateAt C k).inputs ∧ BlindGate.wireValue C n y b = true

def Res (n : ℕ) (C : Circuit) (x y : Fin n → Bool) (v w : ℕ) : Prop :=
  Relation.ReflTransGen (R9 n C x) v w ∨ ∃ (k : ℕ) (a : ℕ) (b : ℕ),
    C.gates[k]? = some ⟨GateOp.and, [a, b]⟩ ∧ BlindGate.wireValue C n y (n + k) = true ∧
    BlindGate.wireValue C n x a = false ∧ BlindGate.wireValue C n x b = false ∧
    Relation.ReflTransGen (R9 n C x) v a ∧ Relation.ReflTransGen (R9 n C x) v b ∧
    Relation.ReflTransGen (R10 n C y) (n + k) w

theorem res_lift {n : ℕ} {C : Circuit} {x y : Fin n → Bool} {v u w : ℕ}
    (h : Res n C x y v u) (h9 : R9 n C x u w) (h10 : R10 n C y u w) : Res n C x y v w := by
  rcases h with h | ⟨k, a, b, h1, h2, h3, h4, h5, h6, h7⟩
  · exact Or.inl (h.tail h9)
  · exact Or.inr ⟨k, a, b, h1, h2, h3, h4, h5, h6, h7.tail h10⟩

theorem main (n : ℕ) (C : Circuit) (hAO : TopForm.IsAO2 n C) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ i : Fin n, x i = false → y i = true → i = v) :
    ∀ w : ℕ, BlindGate.wireValue C n x w = false → BlindGate.wireValue C n y w = true →
      Res n C x y v.val w := by
  obtain ⟨hao, hrb, hlen⟩ := hAO
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hx hy
  by_cases hw : w < n
  · left
    rw [wv_input C x w hw] at hx
    rw [wv_input C y w hw] at hy
    have h := hxy ⟨w, hw⟩ hx hy
    have e : w = v.val := by rw [← h]
    rw [e]
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    by_cases hj : j < C.gates.length
    swap
    · rw [wv_ge C y (n + j) (by omega)] at hy
      exact absurd hy (by simp)
    have hgm : C.gates[j] ∈ C.gates := List.getElem_mem hj
    have hop := hao _ hgm
    have hl := hlen _ hgm
    have hrbj : ∀ i ∈ (C.gates[j]).inputs, i < n + j := by
      intro i hi
      have := hrb j hj i
      rw [gateAt_eq hj] at this
      exact this hi
    obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[j]).inputs = [a, b] := by
      rcases hq : (C.gates[j]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
      · rw [hq] at hl; simp at hl
      · rw [hq] at hl; simp at hl
      · exact ⟨a, b, rfl⟩
      · rw [hq] at hl; simp at hl
    have ha : a < n + j := hrbj a (by rw [hab]; simp)
    have hb : b < n + j := hrbj b (by rw [hab]; simp)
    have hgx := wv_gate C hrb x j hj
    have hgy := wv_gate C hrb y j hj
    rw [hab] at hgx hgy
    have hgs : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hj
    have hga : gateAt C j = C.gates[j] := gateAt_eq hj
    have e10a : R10 n C y a (n + j) := ⟨j, rfl, by rw [hga, hab]; simp, hy⟩
    have e10b : R10 n C y b (n + j) := ⟨j, rfl, by rw [hga, hab]; simp, hy⟩
    rcases hop with hand | hor
    · rw [hand] at hgx hgy
      have hy' : BlindGate.wireValue C n y a = true ∧ BlindGate.wireValue C n y b = true := by
        rw [hgy] at hy
        simpa [GateOp.eval] using hy
      have hx' : BlindGate.wireValue C n x a = false ∨ BlindGate.wireValue C n x b = false := by
        rw [hgx] at hx
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true] at hx
        exact Bool.and_eq_false_iff.mp hx
      have hgeq : C.gates[j] = ⟨GateOp.and, [a, b]⟩ := by
        rw [← hand, ← hab]
      cases hxa : BlindGate.wireValue C n x a <;> cases hxb : BlindGate.wireValue C n x b
      · -- both false
        rcases ih a ha hxa hy'.1 with h1 | ⟨k, a', b', r1, r2, r3, r4, r5, r6, r7⟩
        · rcases ih b hb hxb hy'.2 with h2 | ⟨k, a', b', r1, r2, r3, r4, r5, r6, r7⟩
          · right
            exact ⟨j, a, b, by rw [hgs, hgeq], hy, hxa, hxb, h1, h2, Relation.ReflTransGen.refl⟩
          · exact Or.inr ⟨k, a', b', r1, r2, r3, r4, r5, r6, r7.tail e10b⟩
        · exact Or.inr ⟨k, a', b', r1, r2, r3, r4, r5, r6, r7.tail e10a⟩
      · -- a false, b true
        exact res_lift (ih a ha hxa hy'.1)
          ⟨j, C.gates[j], b, rfl, hgs, Or.inl hab, Or.inr ⟨hand, hxb⟩⟩ e10a
      · -- a true, b false
        exact res_lift (ih b hb hxb hy'.2)
          ⟨j, C.gates[j], a, rfl, hgs, Or.inr hab, Or.inr ⟨hand, hxa⟩⟩ e10b
      · rw [hxa, hxb] at hx'
        simp at hx'
    · rw [hor] at hgx hgy
      have hx' : BlindGate.wireValue C n x a = false ∧ BlindGate.wireValue C n x b = false := by
        rw [hgx] at hx
        simpa [GateOp.eval] using hx
      have hy' : BlindGate.wireValue C n y a = true ∨ BlindGate.wireValue C n y b = true := by
        rw [hgy] at hy
        simpa [GateOp.eval] using hy
      rcases hy' with hya | hyb
      · exact res_lift (ih a ha hx'.1 hya)
          ⟨j, C.gates[j], b, rfl, hgs, Or.inl hab, Or.inl hor⟩ e10a
      · exact res_lift (ih b hb hx'.2 hyb)
          ⟨j, C.gates[j], a, rfl, hgs, Or.inr hab, Or.inl hor⟩ e10b

end PEqualNP.Outside.L_meta_8137

theorem PEqualNP.Outside.L_meta_8137 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1 → Bool) (x6 : Fin x1),       (∀ (x7 : Fin x1), x4 x7 = Bool.false → x5 x7 = Bool.true → x7 = x6) →         have x8 : (Fin x1 → Bool) → ℕ → Bool := PEqualNP.BlindGate.wireValue x2 x1;         have x9 : ℕ → ℕ → Prop := fun (x9 x10 : ℕ) => ∃ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate) (x13 : ℕ), x10 = x1 + x11 ∧ x2.gates[x11]? = Option.some x12 ∧ (x12.inputs = [x9, x13] ∨ x12.inputs = [x13, x9]) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x8 x4 x13 = Bool.true);         have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ), x11 = x1 + x12 ∧ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs ∧ x8 x5 x11 = Bool.true;         ∀ (x11 : ℕ), x8 x4 x11 = Bool.false → x8 x5 x11 = Bool.true → Relation.ReflTransGen x9 (↑x6) x11 ∨ ∃ (x14 : ℕ) (x15 : ℕ) (x16 : ℕ), x2.gates[x14]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x15, x16] : PEqualNP.CircuitLowerBounds.Gate } ∧ x8 x5 (x1 + x14) = Bool.true ∧ x8 x4 x15 = Bool.false ∧ x8 x4 x16 = Bool.false ∧ Relation.ReflTransGen x9 (↑x6) x15 ∧ Relation.ReflTransGen x9 (↑x6) x16 ∧ Relation.ReflTransGen x10 (x1 + x14) x11 := by
  intro x1 x2 hAO x4 x5 x6 hx
  exact PEqualNP.Outside.L_meta_8137.main x1 x2 hAO x4 x5 x6 hx
