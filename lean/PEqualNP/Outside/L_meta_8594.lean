import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8594_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

open PEqualNP.TopForm in
lemma junk_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (hk : k ∈ junk G C) : k < C.gates.length ∧ (gateAt C k).op = GateOp.and := by
  have hjm := hk
  unfold junk gatesWhere at hjm
  obtain ⟨hlen0, hdirty⟩ := Finset.mem_filter.mp hjm
  exact ⟨Finset.mem_range.mp hlen0, hdirty.1⟩

open PEqualNP.TopForm in
lemma and_val2 {n : ℕ} (C : Circuit) (hAO2 : IsAO2 n C) (h : ℕ) (hlen : h < C.gates.length)
    (hand : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C h x = true ↔
      (val C (List.ofFn x) (opnd C h 0) = true ∧ val C (List.ofFn x) (opnd C h 1) = true) := by
  obtain ⟨_, hRB, h2⟩ := hAO2
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hlen))
  have e0 : opnd C h 0 = p := by simp [opnd, hin]
  have e1 : opnd C h 1 = q := by simp [opnd, hin]
  have hpin : p ∈ (gateAt C h).inputs := by rw [hin]; simp
  have hqin : q ∈ (gateAt C h).inputs := by rw [hin]; simp
  have hp : p < n + h := hRB h hlen p hpin
  have hq : q < n + h := hRB h hlen q hqin
  rw [gateVal_eq_val, val_and (n := n) (by simp) hlen hand, hin, e0, e1]
  constructor
  · intro hall
    exact ⟨(hall p (by simp)).2, (hall q (by simp)).2⟩
  · rintro ⟨h1, h2'⟩ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, h1⟩
    · exact ⟨hq, h2'⟩

open PEqualNP.TopForm in
lemma junk_rect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (h : ℕ) (hj : h ∈ junk G C) (x : Fin n → Bool)
    (hx : (∃ a ∈ side (n := n) C h 0, x a = true) ∧ (∃ b ∈ side (n := n) C h 1, x b = true)) :
    gateVal n C h x = true := by
  obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ := hx
  obtain ⟨hlen, hand⟩ := junk_lt G C h hj
  exact (and_val2 C hAO2 h hlen hand x).mpr
    ⟨reach_var_val x _ a (mem_orIn_reach a ha) hax, reach_var_val x _ b (mem_orIn_reach b hb) hbx⟩

lemma fin2_sub (i : Fin 2) :
    (i = 0 ∧ (1 : Fin 2) - i = 1) ∨ (i = 1 ∧ (1 : Fin 2) - i = 0) := by
  revert i; decide

lemma common_unique {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (z z' x y : Fin n) (h1 : G.Adj z x) (h2 : G.Adj z y) (h3 : G.Adj z' x) (h5 : G.Adj z' y)
    (hxy : x ≠ y) : z = z' := by
  by_contra hzz
  exact h4 z x z' y hzz hxy ⟨h1, h3.symm, h5, h2.symm⟩

lemma fibre_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (Pset Q : Finset (Fin n)) (k : ℕ) (Z : Finset (Fin n × Fin n))
    (hZ : ∀ zv ∈ Z, G.Adj zv.1 zv.2 ∧ zv.2 ∈ Pset ∧ zv.2 ∈ Q ∧
      (∀ v' ∈ Pset, G.Adj zv.1 v' → v' = zv.2) ∧
      (∃ b ∈ Q, b ≠ zv.2 ∧ G.Adj zv.1 b) ∧ (Q.filter (fun x => ¬ G.Adj zv.1 x)).card ≤ k) :
    Z.card ≤ (2 * k + 1) ^ 2 := by
  classical
  by_cases hsame : ∀ zv ∈ Z, ∀ zv' ∈ Z, zv.1 = zv'.1
  · have h1 : Z.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro zv hzv zv' hzv'
      have e1 := hsame zv hzv zv' hzv'
      obtain ⟨_, _, _, hu, _, _⟩ := hZ zv hzv
      obtain ⟨hadj', hmem', _, _, _, _⟩ := hZ zv' hzv'
      have e2 : zv'.2 = zv.2 := hu zv'.2 hmem' (by rw [e1]; exact hadj')
      exact Prod.ext e1 e2.symm
    exact h1.trans (Nat.one_le_pow _ _ (by omega))
  · obtain ⟨z1, hA⟩ := not_forall.mp hsame
    obtain ⟨hz1, hB⟩ := Classical.not_imp.mp hA
    obtain ⟨z2, hD⟩ := not_forall.mp hB
    obtain ⟨hz2, hne⟩ := Classical.not_imp.mp hD
    obtain ⟨_, _, _, _, _, hd1⟩ := hZ z1 hz1
    obtain ⟨_, _, _, _, _, hd2⟩ := hZ z2 hz2
    have hcn : (Q.filter (fun x => G.Adj z1.1 x ∧ G.Adj z2.1 x)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_filter] at hx hy
      by_contra hxy
      exact hne (common_unique G h4 z1.1 z2.1 x y hx.2.1 hy.2.1 hx.2.2 hy.2.2 hxy)
    have hsub : Q ⊆ (Q.filter (fun x => ¬ G.Adj z1.1 x)) ∪ (Q.filter (fun x => ¬ G.Adj z2.1 x)) ∪
        (Q.filter (fun x => G.Adj z1.1 x ∧ G.Adj z2.1 x)) := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases a1 : G.Adj z1.1 x
      · by_cases a2 : G.Adj z2.1 x
        · exact Or.inr ⟨hx, a1, a2⟩
        · exact Or.inl (Or.inr ⟨hx, a2⟩)
      · exact Or.inl (Or.inl ⟨hx, a1⟩)
    have hQ : Q.card ≤ 2 * k + 1 := by
      have u0 := Finset.card_le_card hsub
      have u1 := Finset.card_union_le
        ((Q.filter (fun x => ¬ G.Adj z1.1 x)) ∪ (Q.filter (fun x => ¬ G.Adj z2.1 x)))
        (Q.filter (fun x => G.Adj z1.1 x ∧ G.Adj z2.1 x))
      have u2 := Finset.card_union_le (Q.filter (fun x => ¬ G.Adj z1.1 x))
        (Q.filter (fun x => ¬ G.Adj z2.1 x))
      omega
    have hw : ∀ zv : Fin n × Fin n, ∃ b : Fin n, zv ∈ Z →
        (b ∈ Q ∧ b ≠ zv.2 ∧ G.Adj zv.1 b) := by
      intro zv
      by_cases hz : zv ∈ Z
      · obtain ⟨_, _, _, _, ⟨b, hb⟩, _⟩ := hZ zv hz
        exact ⟨b, fun _ => hb⟩
      · exact ⟨zv.1, fun h => absurd h hz⟩
    choose bw hbw using hw
    have hinj : Z.card ≤ (Q ×ˢ Q).card := by
      apply Finset.card_le_card_of_injOn (fun zv => (zv.2, bw zv))
      · intro zv hzv
        have hzv' := Finset.mem_coe.mp hzv
        obtain ⟨_, _, hm, _, _, _⟩ := hZ zv hzv'
        exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hm, (hbw zv hzv').1⟩)
      · intro zv hzv zv' hzv' heq
        have hzvm := Finset.mem_coe.mp hzv
        have hzvm' := Finset.mem_coe.mp hzv'
        have e2 : zv.2 = zv'.2 := congrArg Prod.fst heq
        have e3 : bw zv = bw zv' := congrArg Prod.snd heq
        obtain ⟨ha, _, _, _, _, _⟩ := hZ zv hzvm
        obtain ⟨ha', _, _, _, _, _⟩ := hZ zv' hzvm'
        obtain ⟨_, hb2, hb3⟩ := hbw zv hzvm
        obtain ⟨_, _, hb3'⟩ := hbw zv' hzvm'
        have e1 : zv.1 = zv'.1 :=
          common_unique G h4 zv.1 zv'.1 zv.2 (bw zv) ha hb3 (by rw [e2]; exact ha')
            (by rw [e3]; exact hb3') (Ne.symm hb2)
        exact Prod.ext e1 e2
    rw [Finset.card_product] at hinj
    calc Z.card ≤ Q.card * Q.card := hinj
      _ ≤ (2 * k + 1) * (2 * k + 1) := Nat.mul_le_mul hQ hQ
      _ = (2 * k + 1) ^ 2 := by ring

lemma orIn_input {n : ℕ} (C : Circuit) (v b : Fin n)
    (hb : b ∈ PEqualNP.TopForm.orIn n C v.val) : b = v := by
  have hr := mem_orIn_reach b hb
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hstep, _⟩
  · exact Fin.ext h.symm
  · obtain ⟨k, _, hk, _, _, _⟩ := hstep
    have := v.isLt
    omega

lemma orIn_mono {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    PEqualNP.TopForm.orIn n C w' ⊆ PEqualNP.TopForm.orIn n C w := by
  intro u hu
  exact reach_mem_orIn u (h.trans (mem_orIn_reach u hu))

lemma chain_split {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (z v : Fin n) :
    ∀ w : ℕ, v ∈ PEqualNP.TopForm.orIn n C w →
      (∃ b ∈ PEqualNP.TopForm.orIn n C w, b ≠ v ∧ G.Adj z b) →
      ∃ g c : ℕ, g < C.gates.length ∧ c ∈ (gateAt C g).inputs ∧
        Relation.ReflTransGen (OrStep n C) w (n + g) ∧
        v ∈ PEqualNP.TopForm.orIn n C c ∧ v ∈ PEqualNP.TopForm.orIn n C (n + g) ∧
        (∀ v' ∈ PEqualNP.TopForm.orIn n C c, G.Adj z v' → v' = v) ∧
        (∃ b ∈ PEqualNP.TopForm.orIn n C (n + g), b ≠ v ∧ G.Adj z b) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hb
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with h | ⟨c, hstep, hrest⟩
    · exfalso
      obtain ⟨b, hbm, hbne, _⟩ := hb
      rw [h] at hbm
      exact hbne (orIn_input C v b hbm)
    · obtain ⟨g, hg, hwg, hop, hin, hlt⟩ := hstep
      have hvc : v ∈ PEqualNP.TopForm.orIn n C c := reach_mem_orIn v hrest
      by_cases huniq : ∀ v' ∈ PEqualNP.TopForm.orIn n C c, G.Adj z v' → v' = v
      · subst hwg
        exact ⟨g, c, hg, hin, Relation.ReflTransGen.refl, hvc, hv, huniq, hb⟩
      · obtain ⟨v', h1⟩ := not_forall.mp huniq
        obtain ⟨hv'm, h2⟩ := Classical.not_imp.mp h1
        obtain ⟨hadj, hne⟩ := Classical.not_imp.mp h2
        obtain ⟨g', c', hg', hin', hr', hvc', hvg', hu', hb'⟩ :=
          ih c (by omega) hvc ⟨v', hv'm, hne, hadj⟩
        exact ⟨g', c', hg', hin',
          Relation.ReflTransGen.head ⟨g, hg, hwg, hop, hin, hlt⟩ hr', hvc', hvg', hu', hb'⟩

def slots (C : Circuit) : Finset (ℕ × ℕ) :=
  (Finset.range C.gates.length).biUnion fun g =>
    (gateAt C g).inputs.toFinset.image fun c => (g, c)

lemma slots_card (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (slots C).card ≤ 2 * C.gates.length := by
  unfold slots
  calc ((Finset.range C.gates.length).biUnion fun g =>
        (gateAt C g).inputs.toFinset.image fun c => (g, c)).card
      ≤ ∑ g ∈ Finset.range C.gates.length,
          ((gateAt C g).inputs.toFinset.image fun c => (g, c)).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ Finset.range C.gates.length, 2 := Finset.sum_le_sum (fun g hg => by
        have hlt := Finset.mem_range.mp hg
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (h2 _ (gateAt_mem hlt))))
    _ = 2 * C.gates.length := by simp [mul_comm]

lemma charge_dirt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (k : ℕ)
    (P : Finset (Fin n × Fin n))
    (hP : ∀ zv ∈ P, G.Adj zv.1 zv.2 ∧ ∃ w : ℕ, zv.2 ∈ PEqualNP.TopForm.orIn n C w ∧
      (∃ b ∈ PEqualNP.TopForm.orIn n C w, b ≠ zv.2 ∧ G.Adj zv.1 b) ∧
      ((PEqualNP.TopForm.orIn n C w).filter (fun x => ¬ G.Adj zv.1 x)).card ≤ k) :
    P.card ≤ (2 * k + 1) ^ 2 * (2 * C.gates.length) := by
  classical
  have hslot : ∀ zv : Fin n × Fin n, ∃ gc : ℕ × ℕ, zv ∈ P →
      (gc ∈ slots C ∧ zv.2 ∈ PEqualNP.TopForm.orIn n C gc.2 ∧
        zv.2 ∈ PEqualNP.TopForm.orIn n C (n + gc.1) ∧
        (∀ v' ∈ PEqualNP.TopForm.orIn n C gc.2, G.Adj zv.1 v' → v' = zv.2) ∧
        (∃ b ∈ PEqualNP.TopForm.orIn n C (n + gc.1), b ≠ zv.2 ∧ G.Adj zv.1 b) ∧
        ((PEqualNP.TopForm.orIn n C (n + gc.1)).filter (fun x => ¬ G.Adj zv.1 x)).card ≤ k) := by
    intro zv
    by_cases hz : zv ∈ P
    · obtain ⟨_, w, hv, hb, hk⟩ := hP zv hz
      obtain ⟨g, c, hg, hin, hr, hvc, hvg, hu, hb'⟩ := chain_split G C zv.1 zv.2 w hv hb
      refine ⟨(g, c), fun _ => ⟨?_, hvc, hvg, hu, hb', ?_⟩⟩
      · unfold slots
        exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_range.mpr hg,
          Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hin, rfl⟩⟩
      · exact (Finset.card_le_card (Finset.filter_subset_filter _ (orIn_mono hr))).trans hk
    · exact ⟨(0, 0), fun h => absurd h hz⟩
  choose f hf using hslot
  refine (Finset.card_le_mul_card_image_of_maps_to (f := f) (t := slots C)
    (fun zv hzv => (hf zv hzv).1) ((2 * k + 1) ^ 2) ?_).trans
    (Nat.mul_le_mul_left _ (slots_card C h2))
  intro gc _
  apply fibre_bound G h4 (PEqualNP.TopForm.orIn n C gc.2)
    (PEqualNP.TopForm.orIn n C (n + gc.1)) k
  intro zv hzv
  rw [Finset.mem_filter] at hzv
  obtain ⟨hzP, hfz⟩ := hzv
  obtain ⟨_, h1, h1', h3, h5, h6⟩ := hf zv hzP
  rw [hfz] at h1 h1' h3 h5 h6
  exact ⟨(hP zv hzP).1, h1, h1', h3, h5, h6⟩

open PEqualNP.TopForm

def Wide {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ w : ℕ, v ∈ orIn n C w ∧ 2 ≤ (orIn n C w).card ∧ ∀ a ∈ orIn n C w, G.Adj u a

theorem guarded_ray {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (g : ℕ) (hg : g ∈ junk G C) (b : Fin 2) (u : Fin n)
    (safe : u ∈ wmax G C g) (hu : u ∈ side C g b) :
    ∀ v ∈ side C g (1-b), G.Adj u v := by
  intro v hv
  apply (graphFun_pair G u v).mp
  have clean := (Finset.mem_filter.mp safe).2
  apply clean (pairInput u v) _ (pairInput_left u v)
  apply junk_rect G C ao g hg
  rcases fin2_sub b with ⟨a,d⟩ | ⟨a,d⟩ <;> rw [a] at hu <;> rw [d] at hv
  · exact ⟨⟨u,hu,pairInput_left u v⟩,v,hv,pairInput_right u v⟩
  · exact ⟨⟨v,hv,pairInput_right u v⟩,u,hu,pairInput_left u v⟩

theorem wide_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (ao : IsAO2 n C)
    (E : Finset (Sym2 (Fin n))) (hw : ∀ e ∈ E, ∃ u v, e = s(u,v) ∧ Wide G C u v) :
    E.card ≤ 2 * (C.size+1) := by
  classical
  let P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => Wide G C p.1 p.2)
  have sub : E ⊆ P.image (fun p => s(p.1,p.2)) := by
    intro e he
    obtain ⟨u,v,rfl,h⟩ := hw e he
    exact Finset.mem_image.mpr ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  have four : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨hab,hbc,hcd,hda⟩
    exact no4 G girth a b c d hab hbc hcd hda hac hbd
  have two : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g h => (ao.2.2 g h).le
  have count := charge_dirt G four C two 0 P (by
    intro p hp
    obtain ⟨w,hv,hsize,ha⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨b,hb,ne⟩ := Finset.exists_mem_ne hsize p.2
    refine ⟨ha _ hv,w,hv,⟨b,hb,ne,ha _ hb⟩,?_⟩
    have he : ((orIn n C w).filter (fun a => ¬G.Adj p.1 a)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun a h => not_not_intro (ha a h))
    simp [he])
  have card := (Finset.card_le_card sub).trans Finset.card_image_le
  change E.card ≤ 2 * (C.gates.length+1)
  omega

end PEqualNP.Outside.L_meta_8594_aux

open PEqualNP.Outside.L_meta_8594_aux PEqualNP.TopForm

theorem PEqualNP.Outside.L_meta_8594 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.wmax x3 x5 x12 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x12 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x12 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x12 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false ∧ ∃ (x13 : Fin (2 : ℕ)), x10 ∈ PEqualNP.TopForm.orIn x2 x5 (PEqualNP.TopForm.opnd x5 x12 x13) ∧ x11 ∈ PEqualNP.TopForm.orIn x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) ∧ (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13))).card}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  refine ⟨2,?_⟩
  intro n G dec C girth least _
  apply wide_budget G C girth least.1
  intro e he
  obtain ⟨_,u,v,eq,g,hg,hu,_,_,_,b,hl,hr,hw⟩ := Finset.mem_filter.mp he
  exact ⟨u,v,eq,opnd C g (1-b),hr,hw,guarded_ray G C least.1 g hg b u hu hl⟩
