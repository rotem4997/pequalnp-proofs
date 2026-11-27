import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- The junk gate g is true at the pair u, v. Either it is already true at v alone, or it is not.
-- If it is, every input on the side of u is a neighbour of v. When that side has two inputs or
-- more, the pair is charged to the lowest OR gate of the side that still reaches two inputs,
-- and to the operand of that gate that reaches u only: with no 4-cycle, that gate and operand
-- give u and v back, so there are at most two such pairs per gate. That case is proved here.
-- What is left: the side reaches the input u only (leaf), or g is false at v alone (edge).
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1768_233
    (leaf : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true ∧ gateVal n C g (pairInput v v) = true ∧
        side C a b = {u})).card ≤ k * (C.size + 1))
    (edge : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true ∧
        gateVal n C g (pairInput v v) = false)).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k₁, h₁⟩ := leaf
  obtain ⟨k₂, h₂⟩ := edge
  refine ⟨k₁ + k₂ + 2, ?_⟩
  intro n G inst C hG hL hTop
  have hA := h₁ n G C hG hL hTop
  have hB := h₂ n G C hG hL hTop
  obtain ⟨⟨hAO, hRB, hTwo⟩, -, -⟩ := hL
  letI : DecidableEq GateOp := gateOpDecEq
  have orStep_eq : ∀ (cs : List (List ℕ)) (g : Gate), orStep n cs g =
      cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else [])] := fun _ _ => rfl
  have gateAt_def : ∀ (j : ℕ), gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ => rfl
  have opnd_def : ∀ (a : ℕ) (b : Fin 2), opnd C a b = (gateAt C a).inputs.getD b 0 :=
    fun _ _ => rfl
  have pairInput_def : ∀ (u v w : Fin n), pairInput u v w = decide (w = u ∨ w = v) :=
    fun _ _ _ => rfl
  have graphFun_def : ∀ (x : Fin n → Bool), graphFun G ∅ x =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
  have eval_or : ∀ (l : List Bool), GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_and : ∀ (l : List Bool), GateOp.and.eval l = l.all id := fun _ => rfl
  have mem_orIn : ∀ (w : ℕ) (t : Fin n), t ∈ orIn n C w ↔ ((t : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (t : ℕ) ∈ (gateAt C k).inputs) :=
    fun w t => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
  have mem_tops : ∀ (a : ℕ), a ∈ tops G C ↔
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a :=
    fun a => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
  have comb : ∀ (U : Finset (Sym2 (Fin n))) (P PA PB P3 : Sym2 (Fin n) → Prop)
      [DecidablePred P] [DecidablePred PA] [DecidablePred PB] [DecidablePred P3] (a b c : ℕ),
      (∀ e ∈ U, P e → PA e ∨ PB e ∨ P3 e) → (U.filter PA).card ≤ a → (U.filter PB).card ≤ b →
      (U.filter P3).card ≤ c → (U.filter P).card ≤ a + b + c := by
    intro U P PA PB P3 _ _ _ _ a b c h ha hb hc
    have hsub : U.filter P ⊆ U.filter PA ∪ U.filter PB ∪ U.filter P3 := by
      intro e he
      rw [Finset.mem_filter] at he
      simp only [Finset.mem_union, Finset.mem_filter]
      rcases h e he.1 he.2 with h1 | h1 | h1
      · exact Or.inl (Or.inl ⟨he.1, h1⟩)
      · exact Or.inl (Or.inr ⟨he.1, h1⟩)
      · exact Or.inr ⟨he.1, h1⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (U.filter PA ∪ U.filter PB) (U.filter P3)
    have h3 := Finset.card_union_le (U.filter PA) (U.filter PB)
    omega
  obtain ⟨SW, hSW⟩ : ∃ SW : List Bool → Gate → List Bool, ∀ w g,
      SW w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := ⟨_, fun _ _ => rfl⟩
  have hSWfun : (fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = SW := by
    funext w g
    exact (hSW w g).symm
  have wires_eq : ∀ x : List Bool, C.wires x = C.gates.foldl SW x := by
    intro x
    rw [← hSWfun]
    rfl
  have foldl_length : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl SW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [hSW]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl SW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i hi; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      have hlt : i < (SW w g).length := by simp [hSW]; omega
      rw [ih (SW w g) i hlt]
      simp [hSW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl SW w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl SW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (SW w g).length := by simp [hSW]
        rw [Nat.add_zero, foldl_getD_lt gs (SW w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (SW w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [hSW, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (SW w g) i (by simp [hSW]; omega)]
          simp [hSW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (SW w g) j hj'
        have hl : (SW w g).length = w.length + 1 := by simp [hSW]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  obtain ⟨V, hV⟩ : ∃ V : (Fin n → Bool) → ℕ → Bool, ∀ x u,
      V x u = (C.wires (List.ofFn x)).getD u false := ⟨_, fun _ _ => rfl⟩
  have gateAt_eq : ∀ (j : ℕ) (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro j hj
    rw [gateAt_def]
    simp [List.getD_eq_getElem?_getD, hj]
  have gateAt_mem : ∀ (j : ℕ), j < C.gates.length → gateAt C j ∈ C.gates := by
    intro j hj
    rw [gateAt_eq j hj]
    exact List.getElem_mem hj
  have val_input : ∀ (x : Fin n → Bool) (u : Fin n), V x u.val = x u := by
    intro x u
    rw [hV, wires_eq, foldl_getD_lt _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have val_ge : ∀ (x : Fin n → Bool) (u : ℕ), n + C.gates.length ≤ u → V x u = false := by
    intro x u hu
    rw [hV]
    apply getD_ge
    rw [wires_eq, foldl_length]
    simp only [List.length_ofFn]
    exact hu
  have val_gate : ∀ (x : Fin n → Bool) (j : ℕ), j < C.gates.length →
      V x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then V x i else false) := by
    intro x j hj
    rw [gateAt_eq j hj]
    have key := foldl_getD_gate C.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at key
    simp only [hV, wires_eq]
    exact key
  have val_or : ∀ (x : Fin n → Bool) (r : ℕ), r < C.gates.length →
      (gateAt C r).op = GateOp.or →
      (V x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ V x i = true) := by
    intro x r hr hop
    rw [val_gate x r hr, hop]
    rw [eval_or]
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
  have val_and : ∀ (x : Fin n → Bool) (r : ℕ), r < C.gates.length →
      (gateAt C r).op = GateOp.and →
      (V x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ V x i = true) := by
    intro x r hr hop
    rw [val_gate x r hr, hop]
    rw [eval_and]
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      simp [orStep_eq]
      omega
  have orSets_char : ∀ (gs : List Gate),
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    intro gs
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
        simp only [orStep_eq, List.getD_eq_getElem?_getD]
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
            simp only [orStep_eq, List.getD_eq_getElem?_getD]
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
            simp only [orStep_eq, List.getD_eq_getElem?_getD]
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
          simp only [orStep_eq, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩
          simp at h0
          omega
  have orReaches_iff : ∀ (k g : ℕ),
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    intro k g
    have h := orSets_char C.gates g k
    show (n ≤ n + k ∧ g ∈ (C.gates.foldl (orStep n) []).getD (n + k - n) []) ↔
      k < C.gates.length ∧ (g = k ∨ ((C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ i ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs, i < n + k ∧
          (n ≤ i ∧ g ∈ (C.gates.foldl (orStep n) []).getD (i - n) [])))
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
  have reach_up : ∀ (x : Fin n → Bool) (g : ℕ), V x (n + g) = true →
      ∀ w, OrReaches n C w g → V x w = true := by
    intro x g hg w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      have hnw : n ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h
      rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
      · rw [← h3]; exact hg
      · exact (val_or x k hk hop).mpr ⟨i, hi, hlt, ih i hlt hr⟩
  have orIn_up : ∀ (x : Fin n → Bool) (w : ℕ) (t : Fin n), t ∈ orIn n C w → x t = true →
      V x w = true := by
    intro x w t ht hx
    rw [mem_orIn] at ht
    rcases ht with h | ⟨k, hk, hr, hop, hin⟩
    · rw [← h, val_input]; exact hx
    · refine reach_up x k ?_ w hr
      have hlt := t.isLt
      exact (val_or x k hk hop).mpr ⟨t.val, hin, by omega, by rw [val_input]; exact hx⟩
  have mono : ∀ (x y : Fin n → Bool), (∀ t, x t = true → y t = true) →
      ∀ w, V x w = true → V y w = true := by
    intro x y hxy w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < n
      · have h1 := val_input x ⟨w, hw⟩
        have h2 := val_input y ⟨w, hw⟩
        simp only at h1 h2
        rw [h2]
        rw [h1] at hv
        exact hxy _ hv
      · by_cases hlen : n + C.gates.length ≤ w
        · rw [val_ge x w hlen] at hv; cases hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < C.gates.length := by omega
          rcases hAO _ (gateAt_mem k hk) with hop | hop
          · rw [val_and y k hk hop]
            intro i hi
            obtain ⟨hlt, hi2⟩ := (val_and x k hk hop).mp hv i hi
            exact ⟨hlt, ih i hlt hi2⟩
          · obtain ⟨i, hi, hlt, hi2⟩ := (val_or x k hk hop).mp hv
            exact (val_or y k hk hop).mpr ⟨i, hi, hlt, ih i hlt hi2⟩
  have orIn_input : ∀ (w : ℕ), w < n → ∀ t ∈ orIn n C w, (t : ℕ) = w := by
    intro w hw t ht
    rw [mem_orIn] at ht
    rcases ht with h | ⟨k, hk, hr, -⟩
    · exact h
    · have h1 : n ≤ w := hr.1
      omega
  have orIn_big : ∀ (w : ℕ), n + C.gates.length ≤ w → ∀ t ∈ orIn n C w, False := by
    intro w hw t ht
    rw [mem_orIn] at ht
    have hlt := t.isLt
    rcases ht with h | ⟨k, hk, hr, -⟩
    · omega
    · have hnw : n ≤ w := hr.1
      obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
      have h1 := ((orReaches_iff k' k).mp hr).1
      omega
  have orIn_down : ∀ (k : ℕ), k < C.gates.length → ∀ t ∈ orIn n C (n + k),
      (gateAt C k).op = GateOp.or ∧ ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ t ∈ orIn n C i := by
    intro k hk t ht
    rw [mem_orIn] at ht
    have hlt := t.isLt
    rcases ht with h | ⟨k', hk', hr, hop', hin'⟩
    · omega
    · obtain ⟨-, h3⟩ := (orReaches_iff k k').mp hr
      rcases h3 with h3 | ⟨hop, i, hi, hlt2, hr2⟩
      · subst h3
        refine ⟨hop', t.val, hin', by omega, ?_⟩
        rw [mem_orIn]
        exact Or.inl rfl
      · refine ⟨hop, i, hi, hlt2, ?_⟩
        rw [mem_orIn]
        exact Or.inr ⟨k', hk', hr2, hop', hin'⟩
  have orIn_upw : ∀ (k : ℕ), k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ i ∈ (gateAt C k).inputs, i < n + k → ∀ t ∈ orIn n C i, t ∈ orIn n C (n + k) := by
    intro k hk hop i hi hlt t ht
    rw [mem_orIn] at ht ⊢
    rcases ht with h | ⟨k', hk', hr, hop', hin'⟩
    · exact Or.inr ⟨k, hk, (orReaches_iff k k).mpr ⟨hk, Or.inl rfl⟩, hop, by rw [h]; exact hi⟩
    · exact Or.inr ⟨k', hk',
        (orReaches_iff k k').mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩, hop', hin'⟩
  have descend : ∀ (w : ℕ) (u u' : Fin n), u ∈ orIn n C w → u' ∈ orIn n C w → u' ≠ u →
      ∃ (k : ℕ) (s : Fin 2), k < C.gates.length ∧ (∀ t ∈ orIn n C (n + k), t ∈ orIn n C w) ∧
        u ∈ orIn n C (n + k) ∧ (∃ u1 ∈ orIn n C (n + k), u1 ≠ u) ∧
        u ∈ orIn n C (opnd C k s) ∧ ∀ t ∈ orIn n C (opnd C k s), t = u := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro u u' hu hu' hne
      by_cases hw : w < n
      · exact absurd (Fin.ext ((orIn_input w hw u' hu').trans (orIn_input w hw u hu).symm)) hne
      · by_cases hlen : n + C.gates.length ≤ w
        · exact (orIn_big w hlen u hu).elim
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < C.gates.length := by omega
          obtain ⟨hop, i, hi, hlt, hui⟩ := orIn_down k hk u hu
          obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hTwo _ (gateAt_mem k hk))
          by_cases hall : ∀ t ∈ orIn n C i, t = u
          · have hs : ∃ s : Fin 2, opnd C k s = i := by
              have hi2 := hi
              rw [hin] at hi2
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi2
              rcases hi2 with h | h
              · exact ⟨0, by rw [opnd_def, hin]; simp [h]⟩
              · exact ⟨1, by rw [opnd_def, hin]; simp [h]⟩
            obtain ⟨s, hs⟩ := hs
            exact ⟨k, s, hk, fun t ht => ht, hu, ⟨u', hu', hne⟩, by rw [hs]; exact hui,
              by rw [hs]; exact hall⟩
          · obtain ⟨t, ht, htne⟩ : ∃ t ∈ orIn n C i, t ≠ u := by
              by_contra hno
              exact hall (fun t ht => by_contra (fun hne2 => hno ⟨t, ht, hne2⟩))
            obtain ⟨k', s, hk', hsub, h1, h2, h3, h4⟩ := ih i hlt u t hui ht htne
            exact ⟨k', s, hk', fun z hz => orIn_upw k hk hop i hi hlt z (hsub z hz), h1, h2, h3, h4⟩
  have noC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → False := by
    intro a b c d hac hbd h1 h2 h3 h4
    have e1 := G.ne_of_adj h1
    have e2 := G.ne_of_adj h2
    have e3 := G.ne_of_adj h3
    have e4 := G.ne_of_adj h4
    have hcyc : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
        (SimpleGraph.Walk.cons h3 (SimpleGraph.Walk.cons h4 SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
      · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    have h5 := hG a _ hcyc
    simp at h5
  have pair_true : ∀ (u v w : Fin n), pairInput u v w = true ↔ w = u ∨ w = v := by
    intro u v w
    rw [pairInput_def]
    simp
  have graphFun_pair : ∀ (u v : Fin n), graphFun G ∅ (pairInput u v) = true → G.Adj u v := by
    intro u v
    rw [graphFun_def]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pair_true]
    rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  have side_adj : ∀ (a : ℕ) (b : Fin 2) (j : ℕ) (v : Fin n), a ∈ tops G C →
      OrReaches n C (opnd C a (1 - b)) j → gateVal n C j (pairInput v v) = true →
      ∀ t ∈ orIn n C (opnd C a b), G.Adj t v := by
    intro a b j v ha hr hj t ht
    obtain ⟨hlen, hop, hbel⟩ := (mem_tops a).mp ha
    apply graphFun_pair
    apply hbel
    have hjv : V (pairInput t v) (n + j) = true := by
      refine mono (pairInput v v) (pairInput t v) ?_ (n + j) ?_
      · intro z hz
        rw [pair_true] at hz ⊢
        rcases hz with h | h <;> exact Or.inr h
      · rw [hV]; exact hj
    have hQ := reach_up (pairInput t v) j hjv _ hr
    have hP := orIn_up (pairInput t v) _ t ht ((pair_true t v t).mpr (Or.inl rfl))
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hTwo _ (gateAt_mem a hlen))
    have hp : p < n + a := hRB a hlen p (by rw [hin]; simp)
    have hq : q < n + a := hRB a hlen q (by rw [hin]; simp)
    have e0 : opnd C a 0 = p := by rw [opnd_def, hin]; simp
    have e1 : opnd C a 1 = q := by rw [opnd_def, hin]; simp
    have key : V (pairInput t v) p = true ∧ V (pairInput t v) q = true := by
      rcases (by decide : ∀ b : Fin 2, b = 0 ∨ b = 1) b with rfl | rfl
      · rw [show (1 : Fin 2) - 0 = 1 from by decide, e1] at hQ
        rw [e0] at hP
        exact ⟨hP, hQ⟩
      · rw [show (1 : Fin 2) - 1 = 0 from by decide, e0] at hQ
        rw [e1] at hP
        exact ⟨hQ, hP⟩
    show (C.wires (List.ofFn (pairInput t v))).getD (n + a) false = true
    rw [← hV, val_and _ a hlen hop, hin]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h
    · rw [h]; exact ⟨hp, key.1⟩
    · rw [h]; exact ⟨hq, key.2⟩
  classical
  refine le_trans (comb (Ustar G C) _ _ _ (fun e => ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      gateVal n C g (pairInput v v) = true ∧ ∃ u' ∈ side (n := n) C a b, u' ≠ u)
      _ _ (2 * C.size) ?_ hA hB ?_) ?_
  · intro e he hP
    obtain ⟨u, v, rfl, a, ha, b, j, hj, hu, hr, hval⟩ := hP
    by_cases hvv : gateVal n C j (pairInput v v) = true
    · by_cases hc : side (n := n) C a b = {u}
      · exact Or.inl ⟨u, v, rfl, a, ha, b, j, hj, hu, hr, hval, hvv, hc⟩
      · refine Or.inr (Or.inr ⟨u, v, rfl, a, ha, b, j, hj, hu, hr, hvv, ?_⟩)
        by_contra hno
        exact hc (Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hu, fun x hx => by_contra (fun hne2 => hno ⟨x, hx, hne2⟩)⟩)
    · exact Or.inr (Or.inl ⟨u, v, rfl, a, ha, b, j, hj, hu, hr, hval,
        (Bool.not_eq_true _).mp hvv⟩)
  · have hTc : ((Finset.range C.gates.length) ×ˢ (Finset.univ : Finset (Fin 2))).card =
        2 * C.size := by
      rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_comm _ _
    rw [← hTc]
    refine Finset.card_le_card_of_forall_subsingleton
      (fun (e : Sym2 (Fin n)) (ks : ℕ × Fin 2) => ∃ u v : Fin n, e = s(u, v) ∧
        u ∈ orIn n C (opnd C ks.1 ks.2) ∧ (∀ t ∈ orIn n C (opnd C ks.1 ks.2), t = u) ∧
        (∃ u1 ∈ orIn n C (n + ks.1), u1 ≠ u) ∧ u ∈ orIn n C (n + ks.1) ∧
        ∀ t ∈ orIn n C (n + ks.1), G.Adj t v) ?_ ?_
    · intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨-, u, v, rfl, a, ha, b, j, hj, hu, hr, hvv, u', hu', hne⟩ := he
      have hu2 : u ∈ orIn n C (opnd C a b) := hu
      have hu3 : u' ∈ orIn n C (opnd C a b) := hu'
      obtain ⟨k, s, hk, hsub, h1, h2, h3, h4⟩ := descend _ u u' hu2 hu3 hne
      refine ⟨(k, s), by simp [hk], u, v, rfl, h3, h4, h2, h1, ?_⟩
      intro t ht
      exact side_adj a b j v ha hr hvv t (hsub t ht)
    · rintro ⟨k, s⟩ - e ⟨-, u, v, rfl, hu, hall, ⟨u1, hu1, hne⟩, huk, hadj⟩
        e' ⟨-, u', v', rfl, hu', hall', -, -, hadj'⟩
      have huu : u' = u := hall u' hu'
      rw [huu]
      by_cases hvv : v = v'
      · rw [hvv]
      · exact (noC4 u v u1 v' (Ne.symm hne) hvv (hadj u huk) (hadj u1 hu1).symm
          (hadj' u1 hu1) (hadj' u huk).symm).elim
  · have e : (k₁ + k₂ + 2) * (C.size + 1) =
        k₁ * (C.size + 1) + k₂ * (C.size + 1) + 2 * C.size + 2 := by ring
    rw [e]
    exact Nat.le_add_right _ _
