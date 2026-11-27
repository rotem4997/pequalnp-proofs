import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6074

-- The fold lemmas below (step, W and their properties) are taken from the checked file
-- L_meta_5465.lean of this repository (Apache-2.0).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

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

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

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

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl


-- Renaming the wires read by every gate.
def remap (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

-- If the renaming matches the two starting wire lists and sends gate wires to gate wires,
-- the renamed gate list computes the same values at the renamed wires.
theorem sim (r : ℕ → ℕ) (wa wb : List Bool)
    (hbase : ∀ i, wb.getD (r i) false = wa.getD i false)
    (hr : ∀ i k, r i = wb.length + k ↔ i = wa.length + k) :
    ∀ (gs : List Gate) (i : ℕ),
      (W (gs.map (remap r)) wb).getD (r i) false = (W gs wa).getD i false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro i; exact hbase i
  | append_singleton gs g ih =>
    intro i
    rw [List.map_append, List.map_cons, List.map_nil, W_snoc_getD, W_snoc_getD, List.length_map]
    by_cases hi : i = wa.length + gs.length
    · rw [if_pos ((hr i gs.length).mpr hi), if_pos hi]
      show g.op.eval ((g.inputs.map r).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · rw [if_neg (fun h => hi ((hr i gs.length).mp h)), if_neg hi]
      exact ih i

theorem remap_mono (r : ℕ → ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ gs.map (remap r), g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := h g0 hg0
  exact ⟨this.1, by simpa [remap] using this.2⟩

theorem main (n m : ℕ) (σ : Fin n → Fin m) (A B : Circuit) (hA : Monotone2 A) (hB : Monotone2 B)
    (hoA : A.output < n + A.size) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ A.size + B.size + 1 ∧ D.output < m + D.size ∧
      ∀ y : Fin m → Bool, D.eval (List.ofFn y) =
        (A.eval (List.ofFn (y ∘ σ)) || B.eval (List.ofFn y)) := by
  have hoA' : A.output < n + A.gates.length := hoA
  let r1 : ℕ → ℕ := fun i => if h : i < n then (σ ⟨i, h⟩).val else i - n + m
  let r2 : ℕ → ℕ := fun i => if i < m then i else i + A.gates.length
  have hr1lt : r1 A.output < m + A.gates.length := by
    show (if h : A.output < n then (σ ⟨A.output, h⟩).val else A.output - n + m) < _
    split
    · have := (σ ⟨A.output, by assumption⟩).isLt
      omega
    · omega
  refine ⟨⟨A.gates.map (remap r1) ++ B.gates.map (remap r2) ++
      [⟨GateOp.or, [r1 A.output, r2 B.output]⟩], m + A.gates.length + B.gates.length⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · rcases List.mem_append.mp h with h | h
      · exact remap_mono r1 A.gates hA g h
      · exact remap_mono r2 B.gates hB g h
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨by simp, by simp⟩
  · show (A.gates.map (remap r1) ++ B.gates.map (remap r2) ++ [_]).length ≤
      A.gates.length + B.gates.length + 1
    simp
    omega
  · show m + A.gates.length + B.gates.length <
      m + (A.gates.map (remap r1) ++ B.gates.map (remap r2) ++ [_]).length
    simp
    omega
  · intro y
    have s1 := sim r1 (List.ofFn (y ∘ σ)) (List.ofFn y) (by
        intro i
        show (List.ofFn y).getD (if h : i < n then (σ ⟨i, h⟩).val else i - n + m) false = _
        split
        · rename_i h
          rw [ofFn_getD y _ (σ ⟨i, h⟩).isLt, ofFn_getD (y ∘ σ) i h]
          rfl
        · rw [getD_ge _ _ (by rw [List.length_ofFn]; omega),
            getD_ge _ _ (by rw [List.length_ofFn]; omega)]) (by
        intro i k
        rw [List.length_ofFn, List.length_ofFn]
        show (if h : i < n then (σ ⟨i, h⟩).val else i - n + m) = m + k ↔ i = n + k
        split
        · rename_i h
          have := (σ ⟨i, h⟩).isLt
          constructor <;> intro h' <;> omega
        · constructor <;> intro h' <;> omega) A.gates
    have s2 := sim r2 (List.ofFn y) (W (A.gates.map (remap r1)) (List.ofFn y)) (by
        intro i
        show (W (A.gates.map (remap r1)) (List.ofFn y)).getD
          (if i < m then i else i + A.gates.length) false = _
        split
        · exact W_prefix _ _ _ (by rw [List.length_ofFn]; assumption)
        · rw [W_ge _ _ _ (by rw [List.length_ofFn, List.length_map]; omega),
            getD_ge _ _ (by rw [List.length_ofFn]; omega)]) (by
        intro i k
        rw [W_length, List.length_ofFn, List.length_map]
        show (if i < m then i else i + A.gates.length) = m + A.gates.length + k ↔ i = m + k
        split
        · constructor <;> intro h' <;> omega
        · constructor <;> intro h' <;> omega) B.gates
    show (W (A.gates.map (remap r1) ++ B.gates.map (remap r2) ++
      [⟨GateOp.or, [r1 A.output, r2 B.output]⟩]) (List.ofFn y)).getD
        (m + A.gates.length + B.gates.length) false =
      ((W A.gates (List.ofFn (y ∘ σ))).getD A.output false ||
        (W B.gates (List.ofFn y)).getD B.output false)
    rw [W_snoc_getD, if_pos (by simp; omega)]
    simp only [List.map_cons, List.map_nil]
    rw [eval_or2, W_append, s2 B.output,
      W_prefix _ _ _ (by rw [W_length, List.length_ofFn, List.length_map]; exact hr1lt),
      s1 A.output]

end PEqualNP.Outside.L_meta_6074

theorem PEqualNP.Outside.L_meta_6074 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.Monotone2 x5 → x4.output < x1 + x4.size → x5.output < x2 + x5.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧ x10.output < x2 + x10.size ∧ ∀ (x11 : Fin x2 → Bool), x10.eval (List.ofFn x11) = (x4.eval (List.ofFn (x11 ∘ x3)) || x5.eval (List.ofFn x11)) := by
  intro n m σ A B hA hB hoA _
  exact PEqualNP.Outside.L_meta_6074.main n m σ A B hA hB hoA
