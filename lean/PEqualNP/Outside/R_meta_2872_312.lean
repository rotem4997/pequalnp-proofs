import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_2872_312
    (leafless : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) →
      (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
      let leaf := fun e : Fin n × Fin m =>
        (∀ d ∈ E, d.1 = e.1 → d = e) ∨ (∀ d ∈ E, d.2 = e.2 → d = e);
      (∀ e ∈ E, ¬ leaf e) → E.card + M.card ≤ C.size + 1)
    (matchedLeaves : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) →
      (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
      let leaf := fun e : Fin n × Fin m =>
        (∀ d ∈ E, d.1 = e.1 → d = e) ∨ (∀ d ∈ E, d.2 = e.2 → d = e);
      (∀ e ∈ E, leaf e → e ∈ M) → (∃ e ∈ M, leaf e) → E.card + M.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp (config := {congrConsts := false})
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp (config := {congrConsts := false}) [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp (config := {congrConsts := false}) only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp (config := {congrConsts := false}) at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp (config := {congrConsts := false}) only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := {congrConsts := false}) [stepWire]; omega)]
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa (config := {congrConsts := false}) using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp (config := {congrConsts := false}) [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp (config := {congrConsts := false}) only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
      (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp (config := {congrConsts := false}) [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp (config := {congrConsts := false}) [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp (config := {congrConsts := false}) [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        R (val C x (n + r)) (val C x i)) :
      ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp (config := {congrConsts := false}) only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp (config := {congrConsts := false}) only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
              exact hrefl _
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
                exact hrefl _

  have bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : R (val C x (n + r)) (val C x i)) :
      R (C.eval x) ((bypass n C r i).eval x) := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · have hgi : val (bypass n C r i) x i = val C x i := by
        rcases hi with hi | hi
        · exact bypass_val_lt hx hr i hi
        · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
      rw [h, aliasWire_self, hgi]; exact hR
    · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

  have bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x :=
    (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

  have bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hout : C.output ≠ n + r)
      (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
      (fun h => h.elim fun k hk => absurd hk.2 (hno k hk.1)) _ hout).symm

  have bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
      ∀ k < (bypass n C r i).gates.length,
        (gateAt (bypass n C r i) k).op = GateOp.and ∨
          (gateAt (bypass n C r i) k).op = GateOp.or := by
    intro k hk
    rw [bypass_length] at hk
    rw [gateAt_bypass hk]
    split_ifs with h
    · exact hAO k (by omega)
    · exact hAO (k + 1) (by omega)

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp (config := {congrConsts := false}) only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp (config := {congrConsts := false}) [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp (config := {congrConsts := false}) only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  -- Erase gates one at a time on the zero restriction. Any false output of a
  -- removed gate can be redirected to the pinned input during this process.
  have pinZero (n : ℕ) (p : Fin n) : ∀ k (C : Circuit), C.size = k → IsAO2 n C →
      (∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
        C.eval (List.ofFn (Function.update y p false))) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
        ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠
          C.eval (List.ofFn (Function.update x p false))) → D.size < C.size) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x p false)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro C hk hC hn
      let row := fun (x : Fin n → Bool) => List.ofFn (Function.update x p false)
      have lengths (x : Fin n → Bool) : (row x).length = n := by simp (config := {congrConsts := false}) [row]
      have pinned (x : Fin n → Bool) : val C (row x) p.val = false := by
        rw [val_input (lengths x) p.isLt]
        change (List.ofFn (Function.update x p false)).getD p.val false = false
        rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false})),List.getElem_ofFn]
        simp (config := {congrConsts := false})
      have opGood : ∀ j < C.gates.length,
          (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
        fun j hj => hC.1 _ (gateAt_mem hj)
      have outNe : C.output ≠ p.val := by
        intro eq
        obtain ⟨x,y,hnxy⟩ := hn
        apply hnxy
        rw [eval_eq_val,eval_eq_val,eq,pinned,pinned]
      by_cases reads : ∃ j < C.gates.length, p.val ∈ (gateAt C j).inputs
      · obtain ⟨j,hj,hr⟩ := reads
        have canErase (u : ℕ) (hu : u < n+j)
            (eq : ∀ x : Fin n → Bool, val C (row x) (n+j) = val C (row x) u) :
            ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
              ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (row x)) → D.size < C.size) ∧
              ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (row x) := by
          let B := bypass n C j u
          have hlt : B.size < C.size := by
            change (bypass n C j u).gates.length < C.gates.length
            rw [bypass_length]
            omega
          have hB : IsAO2 n B := by
            refine ⟨?_,bypass_readsBack hu hC.2.1,?_⟩
            · intro g hg
              obtain ⟨g',hg',ho,_⟩ := bypass_mem g hg
              simpa (config := {congrConsts := false}) only [ho] using hC.1 g' hg'
            · intro g hg
              obtain ⟨g',hg',_,hl⟩ := bypass_mem g hg
              rw [hl]
              exact hC.2.2 g' hg'
          have same (x : Fin n → Bool) : B.eval (row x) = C.eval (row x) :=
            bypass_eval_eq (lengths x) opGood hj (Or.inl hu) (eq x)
          have hnB : ∃ x y : Fin n → Bool, B.eval (row x) ≠ B.eval (row y) := by
            obtain ⟨x,y,hxy⟩ := hn
            exact ⟨x,y,by rw [same,same]; exact hxy⟩
          obtain ⟨D,hD,hDsize,_,heval⟩ := ih B.size (by omega) B rfl hB hnB
          refine ⟨D,hD,by omega,fun _ => by omega,?_⟩
          intro x
          exact (heval x).trans (same x)
        rcases opGood j hj with hop | hop
        · refine canErase p.val (by have := p.isLt; omega) ?_
          intro x
          rw [pinned]
          apply Bool.eq_false_iff.mpr
          intro h
          have h' := ((val_and (lengths x) hj hop).mp h p.val hr).2
          rw [pinned] at h'
          cases h'
        · obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hC.2.2 _ (gateAt_mem hj))
          have ha : a < n+j := hC.2.1 j hj a (by simp (config := {congrConsts := false}) [hab])
          have hb : b < n+j := hC.2.1 j hj b (by simp (config := {congrConsts := false}) [hab])
          have hmem : p.val = a ∨ p.val = b := by simpa (config := {congrConsts := false}) [hab] using hr
          rcases hmem with h | h
          · refine canErase b hb ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) b <;> rfl
          · refine canErase a ha ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) a <;> rfl
      · have absent : ∀ j < C.gates.length, p.val ∉ (gateAt C j).inputs := by
          intro j hj hr
          exact reads ⟨j,hj,hr⟩
        have stable (x : Fin n → Bool) : ∀ w : ℕ, w ≠ p.val →
            val C (List.ofFn x) w = val C (row x) w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hi : w < n
            · rw [val_input (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hi,val_input (lengths x) hi]
              change (List.ofFn x).getD w false =
                (List.ofFn (Function.update x p false)).getD w false
              rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),
                List.getElem_ofFn,List.getElem_ofFn]
              exact (Function.update_of_ne (fun h => hw (congrArg Fin.val h)) _ _).symm
            · by_cases hl : w < n+C.gates.length
              · let j := w-n
                have hj : j < C.gates.length := by dsimp [j]; omega
                have eq : w = n+j := by dsimp [j]; omega
                rw [eq,val_gate (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hj,val_gate (lengths x) hj]
                apply congrArg (gateAt C j).op.eval
                apply List.map_congr_left
                intro i hii
                have earlier := hC.2.1 j hj i hii
                rw [ite_eq_left earlier,ite_eq_left earlier]
                exact ih i (by omega) (fun h => absent j hj (h ▸ hii))
              · rw [val_ge (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) (by omega),val_ge (lengths x) (by omega)]
        have same (x : Fin n → Bool) : C.eval (List.ofFn x) = C.eval (row x) := stable x C.output outNe
        refine ⟨C,hC,le_rfl,?_,same⟩
        rintro ⟨x,hx⟩
        exact (hx (same x)).elim


  intro n m E M C hSquare hAO hEval hSub hMatchP hMatchL
  let left : Fin n → Fin (n+m) := Fin.castAdd m
  let right : Fin m → Fin (n+m) := Fin.natAdd n
  let target (A : Finset (Fin n × Fin m)) (z : Fin (n+m) → Bool) : Bool :=
    decide (∃ p l, (p,l) ∈ A ∧ z (left p) = true ∧ z (right l) = true)
  let leaf (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) : Prop :=
    (∀ d ∈ A, d.1 = e.1 → d = e) ∨ (∀ d ∈ A, d.2 = e.2 → d = e)
  let squareFree (A : Finset (Fin n × Fin m)) : Prop :=
    ∀ (p q : Fin n) (l s : Fin m), p ≠ q → l ≠ s →
      ¬ ((p,l) ∈ A ∧ (p,s) ∈ A ∧ (q,l) ∈ A ∧ (q,s) ∈ A)
  have leftInj : Function.Injective left := by
    intro p q eq
    have h := congrArg (fun i : Fin (n+m) => i.val) eq
    exact Fin.ext h
  have rightInj : Function.Injective right := by
    intro p q eq
    apply Fin.ext
    have k := congrArg Fin.val eq
    change n+p.val = n+q.val at k
    omega
  have sides (p : Fin n) (l : Fin m) : left p ≠ right l := by
    intro e
    have h := congrArg Fin.val e
    change p.val = n+l.val at h
    omega
  have pinPoint (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (h : leaf A e) :
      ∃ a : Fin (n+m), (a = left e.1 ∨ a = right e.2) ∧
        ∀ d ∈ A, (a = left d.1 ∨ a = right d.2) → d = e := by
    rcases h with h | h
    · refine ⟨left e.1,Or.inl rfl,?_⟩
      intro d hd hh
      rcases hh with hh | hh
      · exact h d hd (leftInj hh).symm
      · exact (sides _ _ hh).elim
    · refine ⟨right e.2,Or.inr rfl,?_⟩
      intro d hd hh
      rcases hh with hh | hh
      · exact (sides _ _ hh.symm).elim
      · exact h d hd (rightInj hh).symm
  have project (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (a : Fin (n+m))
      (ha : a = left e.1 ∨ a = right e.2)
      (unique : ∀ d ∈ A, (a = left d.1 ∨ a = right d.2) → d = e)
      (z : Fin (n+m) → Bool) : target A (Function.update z a false) = target (A.erase e) z := by
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨p,l,he,hp,hl⟩
      have dp : left p ≠ a := by
        intro eq
        rw [eq,Function.update_self] at hp
        cases hp
      have dl : right l ≠ a := by
        intro eq
        rw [eq,Function.update_self] at hl
        cases hl
      have neq : (p,l) ≠ e := by
        intro ee
        rw [← ee] at ha
        exact ha.elim (fun h => dp h.symm) (fun h => dl h.symm)
      rw [Function.update_of_ne dp] at hp
      rw [Function.update_of_ne dl] at hl
      exact ⟨p,l,Finset.mem_erase.mpr ⟨neq,he⟩,hp,hl⟩
    · rintro ⟨p,l,he,hp,hl⟩
      obtain ⟨neq,he⟩ := Finset.mem_erase.mp he
      have dp : left p ≠ a := fun eq => neq (unique (p,l) he (Or.inl eq.symm))
      have dl : right l ≠ a := fun eq => neq (unique (p,l) he (Or.inr eq.symm))
      exact ⟨p,l,he,by rwa [Function.update_of_ne dp],by rwa [Function.update_of_ne dl]⟩
  have sensitive (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (he : e ∈ A) :
      ∃ z : Fin (n+m) → Bool, target A z ≠ target (A.erase e) z := by
    let z := fun i : Fin (n+m) => decide (i = left e.1 ∨ i = right e.2)
    have yes : target A z = true := by
      apply decide_eq_true_eq.mpr
      exact ⟨e.1,e.2,he,by simp (config := {congrConsts := false}) [z],by simp (config := {congrConsts := false}) [z]⟩
    have no : target (A.erase e) z = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,he',hp,hl⟩ := decide_eq_true_eq.mp h
      have pe : p = e.1 := by
        simp (config := {congrConsts := false}) only [z,decide_eq_true_eq] at hp
        exact hp.elim (fun v => leftInj v) (fun v => (sides _ _ v).elim)
      have le : l = e.2 := by
        simp (config := {congrConsts := false}) only [z,decide_eq_true_eq] at hl
        exact hl.elim (fun v => (sides _ _ v.symm).elim) (fun v => rightInj v)
      exact (Finset.mem_erase.mp he').1 (Prod.ext pe le)
    exact ⟨z,by rw [yes,no]; decide⟩
  have inductionBound : ∀ k (A : Finset (Fin n × Fin m)) (B : Circuit), A.card = k →
      squareFree A → IsAO2 (n+m) B → (∀ z, circuitFun (n+m) B z = target A z) →
      M ⊆ A → A.card + M.card ≤ B.size + 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro A B hcard hA hB evB Msub
      by_cases removable : ∃ e ∈ A, e ∉ M ∧ leaf A e
      · obtain ⟨e,he,heM,hLeaf⟩ := removable
        let A' := A.erase e
        have hcard' : A'.card + 1 = A.card := Finset.card_erase_add_one he
        have mSub' : M ⊆ A' := by
          intro d hd
          exact Finset.mem_erase.mpr ⟨fun eq => heM (eq ▸ hd),Msub hd⟩
        by_cases hasEdge : A'.Nonempty
        · obtain ⟨a,ha,alone⟩ := pinPoint A e hLeaf
          have cofactor (z : Fin (n+m) → Bool) :
              B.eval (List.ofFn (Function.update z a false)) = target A' z :=
            (evB (Function.update z a false)).trans (project A e a ha alone z)
          have hn : ∃ x y : Fin (n+m) → Bool, B.eval (List.ofFn (Function.update x a false)) ≠
              B.eval (List.ofFn (Function.update y a false)) := by
            have no : target A' (fun _ => false) = false := by simp (config := {congrConsts := false}) [target]
            obtain ⟨d,hd⟩ := hasEdge
            have yes : target A' (fun _ => true) = true :=
              decide_eq_true_eq.mpr ⟨d.1,d.2,hd,rfl,rfl⟩
            exact ⟨fun _ => false,fun _ => true,by rw [cofactor,cofactor,no,yes]; decide⟩
          have needsPin : ∃ z : Fin (n+m) → Bool, B.eval (List.ofFn z) ≠
              B.eval (List.ofFn (Function.update z a false)) := by
            obtain ⟨z,hz⟩ := sensitive A e he
            refine ⟨z,?_⟩
            rw [cofactor]
            change circuitFun (n+m) B z ≠ target A' z
            rw [evB z]
            exact hz
          obtain ⟨D,hD,_,saved,models⟩ := pinZero (n+m) a B.size B rfl hB hn
          have small := saved needsPin
          have hDModel (z : Fin (n+m) → Bool) : circuitFun (n+m) D z = target A' z :=
            (models z).trans (cofactor z)
          have hA' : squareFree A' := by
            intro p q l s hp hl agree
            exact hA p q l s hp hl ⟨Finset.erase_subset _ _ agree.1,
              Finset.erase_subset _ _ agree.2.1,Finset.erase_subset _ _ agree.2.2.1,
              Finset.erase_subset _ _ agree.2.2.2⟩
          have smaller := ih A'.card (by omega) A' D rfl hA' hD hDModel mSub'
          omega
        · have empty : A' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hasEdge
          have mk := Finset.card_le_card mSub'
          rw [empty,Finset.card_empty] at mk hcard'
          omega
      · have allMatched : ∀ e ∈ A, leaf A e → e ∈ M := by
          intro e he h
          by_contra hM
          exact removable ⟨e,he,hM,h⟩
        by_cases anyLeaf : ∃ e ∈ A, leaf A e
        · obtain ⟨e,he,h⟩ := anyLeaf
          exact matchedLeaves n m A M B hA hB evB Msub hMatchP hMatchL allMatched ⟨e,allMatched e he h,h⟩
        · exact leafless n m A M B hA hB evB Msub hMatchP hMatchL (fun e he h => anyLeaf ⟨e,he,h⟩)
  exact inductionBound E.card E C rfl hSquare hAO hEval hSub
