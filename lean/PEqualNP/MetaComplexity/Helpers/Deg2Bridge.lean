import PEqualNP.MetaComplexity.Helpers.Deg2Path
import PEqualNP.MetaComplexity.Helpers.LineDegTest

/-!
# The foldl bridges and cleaning for the degree-two chain (helper for L-meta-649)

Cards of the degree-two card plan, statements as there:

* `api_prefix`: appending gates keeps the old wires (value and degree).
* `card03c_val`, `card03d_deg`: the translation `ofCircuit` keeps every value and does not raise
  any degree.
* `card03r_val`: the converse translation `toCircuit` keeps values and degrees.
* `card04_clean` (D2-04): every AND of a never-dead label (degree 0, true at every test input of
  at most two lines) and a degree 1 wire is replaced in place by the OR of the degree 1 wire with
  itself. Degrees do not change, values go up, values at the test inputs do not change, so the
  checked test lemma (L-meta-629, through `toCircuit`) gives the edge function back.

Method for the bridges: induction on the gate list from the end; old wires by `api_prefix`, the
new top wire by one unfolding, the root side by `LineDegTest.W_snoc` and `Dg_snoc`.
-/

namespace PEqualNP.MetaComplexity.Deg2.Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg2

variable {N : ℕ}

/-- Appending gates keeps the old wires. -/
theorem api_prefix (D D' : Dag N) (h : D.gates <+: D'.gates) (i : ℕ) (hi : i < N + N + D.size)
    (x : Fin (N + N) → Bool) : D'.val x i = D.val x i ∧ D'.deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then D'.val x a else false) =
        (if _ : a < i then D.val x a else false) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).1
      · rfl
    have hd : ∀ a, (if _ : a < i then D'.deg a else 0) = (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).2
      · rfl
    have hg : ¬ i < N + N → D'.gates[i - (N + N)]? = D.gates[i - (N + N)]? := by
      intro h0
      obtain ⟨t, ht⟩ := h
      rw [← ht, List.getElem?_append_left (by unfold Dag.size at hi; omega)]
    constructor
    · conv_lhs => rw [Dag.val]
      conv_rhs => rw [Dag.val]
      split_ifs with h0
      · rfl
      · rw [hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hv a, hv b]
          | or a b => dsimp only; rw [hv a, hv b]
          | cst v => rfl
    · conv_lhs => rw [Dag.deg]
      conv_rhs => rw [Dag.deg]
      by_cases h0 : i < N + N
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hd a, hd b]
          | or a b => dsimp only; rw [hd a, hd b]
          | cst v => rfl

/-- The value of a DAG gate given the values `r` of the wires it reads. -/
def gval (r : ℕ → Bool) : G → Bool
  | .and a b => r a && r b
  | .or a b => r a || r b
  | .cst v => v

/-- The degree of a DAG gate given the degrees `r` of the wires it reads. -/
def gdeg (r : ℕ → ℕ) : G → ℕ
  | .and a b => r a + r b
  | .or a b => max (r a) (r b)
  | .cst _ => 0

/-- Above the last gate, a wire reads `false` and has degree `0`. -/
theorem val_deg_ge (D : Dag N) {i : ℕ} (hi : N + N + D.size ≤ i) (x : Fin (N + N) → Bool) :
    D.val x i = false ∧ D.deg i = 0 := by
  have hn : D.gates[i - (N + N)]? = none := by
    rw [List.getElem?_eq_none]; unfold Dag.size at hi; omega
  constructor
  · rw [Dag.val, dif_neg (by omega), hn]
  · rw [Dag.deg, if_neg (by omega), hn]

/-- The new top wire after appending one gate. -/
theorem top_snoc (D D' : Dag N) (g : G) (h : D'.gates = D.gates ++ [g]) (x : Fin (N + N) → Bool) :
    D'.val x (N + N + D.size) =
        gval (fun a => if _ : a < N + N + D.size then D.val x a else false) g ∧
      D'.deg (N + N + D.size) = gdeg (fun a => if _ : a < N + N + D.size then D.deg a else 0) g := by
  have hp : D.gates <+: D'.gates := h ▸ List.prefix_append _ _
  have hv : ∀ a, (if _ : a < N + N + D.size then D'.val x a else false) =
      (if _ : a < N + N + D.size then D.val x a else false) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).1
    · rfl
  have hd : ∀ a, (if _ : a < N + N + D.size then D'.deg a else 0) =
      (if _ : a < N + N + D.size then D.deg a else 0) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).2
    · rfl
  have hg : D'.gates[N + N + D.size - (N + N)]? = some g := by
    rw [h, Nat.add_sub_cancel_left, List.getElem?_append_right (by unfold Dag.size; omega)]
    simp [Dag.size]
  constructor
  · rw [Dag.val, dif_neg (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hv a, hv b]; rfl
    | or a b => dsimp only; rw [hv a, hv b]; rfl
    | cst v => rfl
  · rw [Dag.deg, if_neg (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hd a, hd b]; rfl
    | or a b => dsimp only; rw [hd a, hd b]; rfl
    | cst v => rfl

theorem getD_ge_false {l : List Bool} {k : ℕ} (h : l.length ≤ k) : l.getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_ge_zero {l : List ℕ} {k : ℕ} (h : l.length ≤ k) : l.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- One root gate of a fan-in-two AND/OR circuit and its translation compute the same value. -/
theorem trGate_val (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (r : ℕ → Bool) (hr : ∀ k, i ≤ k → r k = false) :
    gval r (trGate i g) = g.op.eval (g.inputs.map r) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gval, GateOp.eval]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;>
      (split_ifs with ha
       · simp [gval, GateOp.eval]
       · simp [gval, GateOp.eval, hr a (by omega)])
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp only [gval, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.any_cons,
        List.all_nil, List.any_nil, id, Bool.and_true, Bool.or_false]
    · by_cases ha : a < i
      · rw [hr b (by omega), Bool.and_false]
      · rw [hr a (by omega), Bool.false_and]
    · rw [hr b (by omega), Bool.or_false, Bool.or_self]
    · rw [hr a (by omega), Bool.false_or, Bool.or_self]
    · rw [hr a (by omega), hr b (by omega), Bool.or_false]
  · simp at hl

theorem gdeg_mono {r r' : ℕ → ℕ} (h : ∀ k, r k ≤ r' k) (g : G) : gdeg r g ≤ gdeg r' g := by
  cases g with
  | and a b => exact Nat.add_le_add (h a) (h b)
  | or a b => exact max_le_max (h a) (h b)
  | cst v => exact le_rfl

/-- The translation of one root gate does not raise its degree. -/
theorem trGate_deg (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (d : List ℕ) : gdeg (fun k => d.getD k 0) (trGate i g) ≤ g.lineDegree d := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gdeg]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with ha <;>
      simp [gdeg, Gate.lineDegree]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp [gdeg, Gate.lineDegree]
  · simp at hl

/-- A DAG gate and its root gate compute the same value. -/
theorem toGate_val (r : ℕ → Bool) (g : G) : gval r g = g.toGate.op.eval (g.toGate.inputs.map r) := by
  cases g with
  | and a b => simp [gval, G.toGate, GateOp.eval]
  | or a b => simp [gval, G.toGate, GateOp.eval]
  | cst v => cases v <;> simp [gval, G.toGate, GateOp.eval]

/-- A DAG gate and its root gate have the same degree. -/
theorem toGate_deg (d : List ℕ) (g : G) : gdeg (fun k => d.getD k 0) g = g.toGate.lineDegree d := by
  cases g with
  | and a b => simp [gdeg, G.toGate, Gate.lineDegree]
  | or a b => simp [gdeg, G.toGate, Gate.lineDegree]
  | cst v => cases v <;> simp [gdeg, G.toGate, Gate.lineDegree]

open LineDegTest in
/-- D2-03c. The translation keeps the value of every wire. -/
theorem card03c_val (C : Circuit) (hC : Monotone2 C) (x : Fin (N + N) → Bool) (i : ℕ) :
    (ofCircuit N C).val x i = (C.wires (List.ofFn x)).getD i false := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ = (List.ofFn x).getD i false
    rw [ofFn_getD, Dag.val]
    split_ifs with h
    · rfl
    · simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (W gs (List.ofFn x)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [W_length, hsz]; simp
    change _ = (W (gs ++ [g]) (List.ofFn x)).getD i false
    rw [W_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).1]
      exact ih i
    · rw [if_neg (lt_irrefl _), if_pos rfl, (top_snoc _ _ _ hgates x).1]
      have hr : (fun a => if _ : a < N + N + (ofCircuit N ⟨gs, o⟩).size then
          (ofCircuit N ⟨gs, o⟩).val x a else false) = fun a => (W gs (List.ofFn x)).getD a false := by
        funext a
        split_ifs with ha
        · exact ih a
        · exact (getD_ge_false (by omega)).symm
      rw [hr]
      exact trGate_val _ g hgC _ (fun k hk => getD_ge_false (by omega))
    · rw [if_neg (by omega), if_neg (by omega)]
      refine (val_deg_ge _ ?_ x).1
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega

open LineDegTest in
/-- D2-03d. The translation does not raise the degree of any wire. -/
theorem card03d_deg (C : Circuit) (hC : Monotone2 C) (i : ℕ) :
    (ofCircuit N C).deg i ≤ (C.lineDegrees (N + N) (lineMarks N)).getD i 0 := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ ≤ (Dg [] (N + N) (lineMarks N)).getD i 0
    rw [Dag.deg]
    by_cases h : i < N + N
    · rw [if_pos h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h, lineMarks]
    · rw [if_neg h]
      simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (Dg gs (N + N) (lineMarks N)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [Dg_length, hsz]
    change _ ≤ (Dg (gs ++ [g]) (N + N) (lineMarks N)).getD i 0
    rw [Dg_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h (fun _ => false)).2]
      exact ih i
    · rw [if_neg (lt_irrefl _), if_pos rfl, (top_snoc _ _ _ hgates (fun _ => false)).2]
      refine le_trans (gdeg_mono (r' := fun k => (Dg gs (N + N) (lineMarks N)).getD k 0) ?_ _)
        (trGate_deg _ g hgC _)
      intro a
      split_ifs with ha
      · exact ih a
      · exact Nat.zero_le _
    · rw [(val_deg_ge _ ?_ (fun _ => false)).2]
      · exact Nat.zero_le _
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega

open LineDegTest in
/-- D2-03r. The converse translation keeps values and degrees. -/
theorem card03r_val (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) :
    (D.toCircuit.wires (List.ofFn x)).getD i false = D.val x i ∧
      (D.toCircuit.lineDegrees (N + N) (lineMarks N)).getD i 0 = D.deg i := by
  obtain ⟨gs, o⟩ := D
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change (List.ofFn x).getD i false = _ ∧ (Dg [] (N + N) (lineMarks N)).getD i 0 = _
    rw [ofFn_getD, Dag.val, Dag.deg]
    by_cases h : i < N + N
    · rw [dif_pos h, dif_pos h, if_pos h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h, lineMarks]
    · rw [dif_neg h, dif_neg h, if_neg h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]
  | append_singleton gs g ih =>
    have hsz : (⟨gs, o⟩ : Dag N).size = gs.length := rfl
    have hgates : (⟨gs ++ [g], o⟩ : Dag N).gates = (⟨gs, o⟩ : Dag N).gates ++ [g] := rfl
    have hlenW : (W (gs.map G.toGate) (List.ofFn x)).length = N + N + (⟨gs, o⟩ : Dag N).size := by
      rw [W_length, hsz]; simp
    have hlenD : (Dg (gs.map G.toGate) (N + N) (lineMarks N)).length =
        N + N + (⟨gs, o⟩ : Dag N).size := by
      rw [Dg_length, hsz]; simp
    change (W ((gs ++ [g]).map G.toGate) (List.ofFn x)).getD i false = _ ∧
      (Dg ((gs ++ [g]).map G.toGate) (N + N) (lineMarks N)).getD i 0 = _
    rw [List.map_append, List.map_singleton, W_snoc, Dg_snoc, getD_snoc, getD_snoc, hlenW, hlenD]
    have ih' : ∀ k, (W (gs.map G.toGate) (List.ofFn x)).getD k false = (⟨gs, o⟩ : Dag N).val x k ∧
        (Dg (gs.map G.toGate) (N + N) (lineMarks N)).getD k 0 = (⟨gs, o⟩ : Dag N).deg k := ih
    rcases lt_trichotomy i (N + N + (⟨gs, o⟩ : Dag N).size) with h | rfl | h
    · rw [if_pos h, if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).1,
        (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).2]
      exact ih' i
    · rw [if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl,
        (top_snoc _ _ _ hgates x).1, (top_snoc _ _ _ hgates x).2]
      have hr : (fun a => if _ : a < N + N + (⟨gs, o⟩ : Dag N).size then
          (⟨gs, o⟩ : Dag N).val x a else false) =
          fun a => (W (gs.map G.toGate) (List.ofFn x)).getD a false := by
        funext a
        split_ifs with ha
        · exact (ih' a).1.symm
        · exact (getD_ge_false (by omega)).symm
      have hd : (fun a => if _ : a < N + N + (⟨gs, o⟩ : Dag N).size then
          (⟨gs, o⟩ : Dag N).deg a else 0) =
          fun a => (Dg (gs.map G.toGate) (N + N) (lineMarks N)).getD a 0 := by
        funext a
        split_ifs with ha
        · exact (ih' a).2.symm
        · exact (getD_ge_zero (by omega)).symm
      rw [hr, hd, toGate_val, toGate_deg]
      exact ⟨rfl, rfl⟩
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hs1 : (⟨gs ++ [g], o⟩ : Dag N).size = (⟨gs, o⟩ : Dag N).size + 1 := by
        simp [Dag.size]
      have := val_deg_ge (⟨gs ++ [g], o⟩ : Dag N) (i := i) (by omega) x
      exact ⟨this.1.symm, this.2.symm⟩

/-! ## D2-04: cleaning -/

open Classical in
/-- The cleaning of one gate: an AND of a degree 0 wire with no dead set of at most two lines and
a degree 1 wire becomes the OR of the degree 1 wire with itself. Degrees are read in `D`. -/
noncomputable def cleanG (I : Fin N → Fin N → Prop) (D : Dag N) : G → G
  | .and a b =>
      if D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅ then .or b b
      else if D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅ then .or a a
      else .and a b
  | .or a b => .or a b
  | .cst v => .cst v

theorem cleanG_and (I : Fin N → Fin N → Prop) (D : Dag N) (a b : ℕ) :
    ((D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧ cleanG I D (.and a b) = .or b b) ∨
    (¬ (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧
      (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅) ∧ cleanG I D (.and a b) = .or a a) ∨
    (¬ (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧
      ¬ (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅) ∧ cleanG I D (.and a b) = .and a b) := by
  simp only [cleanG]
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, rfl⟩)

/-- The cleaned DAG: every gate cleaned in place. -/
noncomputable def clean (I : Fin N → Fin N → Prop) (D : Dag N) : Dag N :=
  ⟨D.gates.map (cleanG I D), D.out⟩

theorem clean_get (I : Fin N → Fin N → Prop) (D : Dag N) (k : ℕ) :
    (clean I D).gates[k]? = (D.gates[k]?).map (cleanG I D) := by
  simp [clean]

theorem clean_gateAt (I : Fin N → Fin N → Prop) (D : Dag N) (i : ℕ) :
    (clean I D).gateAt i = (D.gateAt i).map (cleanG I D) := by
  unfold Dag.gateAt
  split_ifs
  · exact clean_get I D _
  · rfl

theorem cleanG_kids (I : Fin N → Fin N → Prop) (D : Dag N) (g : G) :
    ∀ c ∈ (cleanG I D g).kids, c ∈ g.kids := by
  intro c hc
  cases g with
  | and a b =>
    simp only [cleanG] at hc
    split_ifs at hc <;> simp_all [G.kids]
  | or a b => exact hc
  | cst v => exact hc

theorem clean_wf (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) : (clean I D).WF := by
  intro i g hg c hc
  rw [clean_gateAt] at hg
  obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hg
  exact hwf i g0 hg0 c (cleanG_kids I D g0 c hc)

theorem gate_lt {D : Dag N} (hwf : D.WF) {i a b : ℕ} (hi : ¬ i < N + N)
    (hg : D.gates[i - (N + N)]? = some (.and a b)) : a < i ∧ b < i := by
  have h : D.gateAt i = some (.and a b) := by
    unfold Dag.gateAt; rw [if_pos (by omega)]; exact hg
  exact ⟨hwf i _ h a (by simp [G.kids]), hwf i _ h b (by simp [G.kids])⟩

/-- Cleaning keeps every degree. -/
theorem clean_deg (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (i : ℕ) :
    (clean I D).deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then (clean I D).deg a else 0) =
        (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · rfl
    conv_lhs => rw [Dag.deg]
    conv_rhs => rw [Dag.deg]
    by_cases h0 : i < N + N
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, clean_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          obtain ⟨ha, hb⟩ := gate_lt hwf h0 hg
          rcases cleanG_and I D a b with ⟨h1, hc⟩ | ⟨-, h2, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · rw [hd b, dif_pos ha, dif_pos hb, max_self]
            omega
          · rw [hd a, dif_pos ha, dif_pos hb, max_self]
            omega
          · rw [hd a, hd b]
        | or a b => dsimp only [Option.map_some, cleanG]; rw [hd a, hd b]
        | cst v => rfl

theorem band_le_or_right : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (d || d) := by decide
theorem band_le_or_left : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c || c) := by decide

/-- Cleaning raises values. -/
theorem clean_mono (I : Fin N → Fin N → Prop) (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) :
    D.val x i ≤ (clean I D).val x i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then D.val x a else false) ≤
        (if _ : a < i then (clean I D).val x a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · exact le_rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with h0
    · exact le_rfl
    · rw [clean_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => exact le_rfl
      | some g =>
        cases g with
        | and a b =>
          rcases cleanG_and I D a b with ⟨-, hc⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · exact band_le_or_right _ _ _ _ (hv a) (hv b)
          · exact band_le_or_left _ _ _ _ (hv a) (hv b)
          · exact Api.band_mono _ _ _ _ (hv a) (hv b)
        | or a b => exact Api.bor_mono _ _ _ _ (hv a) (hv b)
        | cst v => exact le_rfl

theorem true_of_noDead (I : Fin N → Fin N → Prop) (D : Dag N) {a : ℕ}
    (h : D.deadSets I 2 a = ∅) {S : Finset (Fin N)} (hS : S.card ≤ 2) :
    D.val (testInput I S) a = true := by
  classical
  by_contra hne
  have hmem : S ∈ D.deadSets I 2 a := by
    unfold Dag.deadSets
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hS, by simpa using hne⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem

/-- Cleaning keeps every value at every test input of at most two lines. -/
theorem clean_test (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) {S : Finset (Fin N)}
    (hS : S.card ≤ 2) (i : ℕ) : (clean I D).val (testInput I S) i = D.val (testInput I S) i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then (clean I D).val (testInput I S) a else false) =
        (if _ : a < i then D.val (testInput I S) a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with h0
    · rfl
    · rw [clean_get]
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          obtain ⟨ha, hb⟩ := gate_lt hwf h0 hg
          rcases cleanG_and I D a b with ⟨h1, hc⟩ | ⟨-, h2, hc⟩ | ⟨-, -, hc⟩ <;>
            simp only [Option.map_some, hc]
          · rw [hv b, dif_pos ha, dif_pos hb, Bool.or_self,
              true_of_noDead I D h1.2.2 hS, Bool.true_and]
          · rw [hv a, dif_pos ha, dif_pos hb, Bool.or_self,
              true_of_noDead I D h2.2.2 hS, Bool.and_true]
          · rw [hv a, hv b]
        | or a b => dsimp only [Option.map_some, cleanG]; rw [hv a, hv b]
        | cst v => rfl

theorem clean_deadSets (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (f : ℕ) :
    (clean I D).deadSets I 2 f = D.deadSets I 2 f := by
  classical
  unfold Dag.deadSets
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← clean_test I D hwf h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [clean_test I D hwf h1]; exact h2⟩

theorem cleanG_eq_and {I : Fin N → Fin N → Prop} {D : Dag N} {g : G} {f v : ℕ}
    (h : cleanG I D g = .and f v) :
    g = .and f v ∧ ¬ (D.deg f = 0 ∧ D.deg v = 1 ∧ D.deadSets I 2 f = ∅) ∧
      ¬ (D.deg v = 0 ∧ D.deg f = 1 ∧ D.deadSets I 2 v = ∅) := by
  cases g with
  | and a b =>
    simp only [cleanG] at h
    split_ifs at h with h1 h2
    simp only [G.and.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, h1, h2⟩
  | or a b => simp [cleanG] at h
  | cst v => simp [cleanG] at h

/-- The cleaned DAG is cleaned on every gate. -/
theorem clean_cleaned (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (Gs : Finset ℕ) :
    (clean I D).Cleaned I Gs := by
  intro e _ f v hl
  rw [clean_deadSets I D hwf]
  obtain ⟨hg, hf, hv⟩ := hl
  rw [clean_deg I D hwf] at hf hv
  intro hdead
  rcases hg with hg | hg
  · rw [clean_gateAt] at hg
    obtain ⟨g0, -, h0⟩ := Option.map_eq_some_iff.1 hg
    exact (cleanG_eq_and h0).2.1 ⟨hf, hv, hdead⟩
  · rw [clean_gateAt] at hg
    obtain ⟨g0, -, h0⟩ := Option.map_eq_some_iff.1 hg
    exact (cleanG_eq_and h0).2.2 ⟨hf, hv, hdead⟩

theorem ble_of_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

/-- A test input carries no incident pair. -/
theorem testInput_noEdge (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) :
    ¬ ∃ p l, I p l ∧ testInput I S (Fin.castAdd N p) = true ∧
      testInput I S (Fin.natAdd N l) = true := by
  classical
  rintro ⟨p, l, hI, hp, hl⟩
  simp only [testInput, inp, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq,
    Finset.mem_filter, Finset.mem_univ, true_and] at hp hl
  exact hp l hl hI

/-- The test lemma on a DAG (L-meta-629 through `toCircuit`): degree at most two at the output,
true on every input carrying an incident pair, false at every test input of at most two lines. -/
theorem test_computes (I : Fin N → Fin N → Prop) (D : Dag N) (hd : D.deg D.out ≤ 2)
    (hup : ∀ z, (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      D.fn z = true)
    (htest : ∀ S : Finset (Fin N), S.card ≤ 2 → D.fn (testInput I S) = false) :
    Computes I D.fn := by
  classical
  let Gr : SimpleGraph (Fin (N + N)) :=
    { Adj := fun i j => ∃ p l, I p l ∧
        ((i = Fin.castAdd N p ∧ j = Fin.natAdd N l) ∨ (i = Fin.natAdd N l ∧ j = Fin.castAdd N p))
      symm := ⟨by
        rintro i j ⟨p, l, hI, h⟩
        exact ⟨p, l, hI, h.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩⟩
      loopless := by
        refine ⟨fun i => ?_⟩
        rintro ⟨p, l, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := p.isLt; omega
        · have := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := p.isLt; omega }
  have hev : ∀ x, D.toCircuit.eval (List.ofFn x) = D.fn x := fun x => (card03r_val D x D.out).1
  have key := LineDegTest.main (N + N) 2 (lineMarks N) Gr D.toCircuit
    (by
      rintro i j ⟨p, l, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
        simp only [lineMarks, Finset.mem_Ico, Fin.val_castAdd, Fin.val_natAdd] <;>
        have := p.isLt <;> have := l.isLt <;> constructor <;> intro <;> omega)
    (fun g hg => by simpa using (Api.card03r_mono D g hg).1)
    (by
      show (D.toCircuit.lineDegrees (N + N) (lineMarks N)).getD D.out 0 ≤ 2
      rw [(card03r_val D (fun _ => false) D.out).2]
      exact hd)
    (by
      rintro i j ⟨p, l, hI, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> rw [hev] <;> apply hup <;>
        exact ⟨p, l, hI, by simp, by simp⟩)
    (by
      intro S hSm hSc
      let S' : Finset (Fin N) := Finset.univ.filter (fun l => Fin.natAdd N l ∈ S)
      have hcard : S'.card ≤ 2 := by
        refine le_trans (Finset.card_le_card_of_injOn (Fin.natAdd N) ?_ ?_) hSc
        · intro l hl
          simp only [S', Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl
          exact hl
        · intro a _ b _ hab
          exact (Fin.natAdd_inj N).1 hab
      rw [hev]
      have hle := Api.api_val_mono D D.out (x := fun k => decide (k ∈ S ∨
          (k.val ∉ lineMarks N ∧ ∀ j ∈ S, ¬ Gr.Adj k j))) (y := testInput I S') (by
        intro k
        refine Fin.addCases (fun p => ?_) (fun l => ?_) k
        · apply ble_of_imp
          intro h
          simp only [decide_eq_true_eq] at h
          simp only [testInput, inp, Fin.addCases_left, decide_eq_true_eq, Finset.mem_filter,
            Finset.mem_univ, true_and]
          rcases h with h | ⟨-, h⟩
          · have := hSm _ h
            simp only [lineMarks, Finset.mem_Ico, Fin.val_castAdd] at this
            have := p.isLt; omega
          · intro l hl hI
            simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at hl
            exact h _ hl ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩
        · apply ble_of_imp
          intro h
          simp only [decide_eq_true_eq] at h
          simp only [testInput, inp, Fin.addCases_right, decide_eq_true_eq]
          rcases h with h | ⟨h, -⟩
          · simpa [S'] using h
          · simp only [lineMarks, Finset.mem_Ico, Fin.val_natAdd] at h
            have := l.isLt; omega)
      have h0 := htest S' hcard
      unfold Dag.fn at h0 ⊢
      rw [h0] at hle
      revert hle
      cases D.val _ D.out <;> decide)
  intro z
  rw [← hev z, key z]
  constructor
  · rintro ⟨i, j, ⟨p, l, hI, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hi, hj⟩
    · exact ⟨p, l, hI, hi, hj⟩
    · exact ⟨p, l, hI, hj, hi⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    exact ⟨_, _, ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩

/-- D2-04. Cleaning: never-dead labels of ANDs of M replaced (in place, by `or v v`). Proof:
the cleaned circuit is pointwise above, equal at every test input with at most two lines, so the
test lemma (L-meta-629, through `toCircuit`) gives the edge function. -/
theorem card04_clean (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) :
    ∃ D' : Dag N, D'.WF ∧ D'.size ≤ D.size ∧ Computes I D'.fn ∧ D'.deg D'.out ≤ 2 ∧
      D'.Cleaned I D'.cone := by
  have hdeg' : (clean I D).deg (clean I D).out ≤ 2 := by
    rw [clean_deg I D hwf]; exact hd
  refine ⟨clean I D, clean_wf I D hwf, by simp [clean, Dag.size], ?_, hdeg',
    clean_cleaned I D hwf _⟩
  refine test_computes I (clean I D) hdeg' ?_ ?_
  · intro z hz
    have h1 : D.fn z = true := (hc z).2 hz
    have := clean_mono I D z D.out
    unfold Dag.fn at h1 ⊢
    rw [h1] at this
    change (clean I D).val z D.out = true
    revert this
    cases (clean I D).val z D.out <;> decide
  · intro S hS
    unfold Dag.fn
    show (clean I D).val (testInput I S) D.out = false
    rw [clean_test I D hwf hS]
    cases ht : D.val (testInput I S) D.out
    · rfl
    · exact absurd ((hc _).1 ht) (testInput_noEdge I S)

end PEqualNP.MetaComplexity.Deg2.Bridge
