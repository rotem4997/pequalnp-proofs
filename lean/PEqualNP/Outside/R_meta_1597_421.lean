import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

-- The four degree-two vertices are numbered zero through three.
-- Fixing any one of them to false leaves ten free inputs and fourteen edges.
-- Equal wires on that face can be bypassed, latest first, keeping earlier wires intact.
-- The bypass calculations adapt L_meta_1499. The cover argument adapts R_meta_1597_318.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_1597_421
  (faceBound : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ (v : Fin 11) (E : Circuit), v.val < 4 → IsAO2 11 E →
      (∀ x : Fin 11 → Bool, x v = false → circuitFun 11 E x = graphFun G ∅ x) →
      19 ≤ E.size)
  (repeats : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ D : Circuit, IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card → D.size ≤ 21 →
      2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card <
        2 * (Ustar G D).card →
      ∃ v : Fin 11, v.val < 4 ∧
        let repeatsAt := fun j : ℕ => ∃ w < 11 + j,
          ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + j) = wval D x w
        ∃ i j k : ℕ, i < j ∧ j < k ∧ k < D.size ∧ repeatsAt i ∧ repeatsAt j ∧ repeatsAt k) :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  classical
  intro routes pre D hm ht hj
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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
        rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

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
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
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
          simp only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, by omega, hk1, hi'⟩
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

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

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
    · simp only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)
  have drop : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (r w : ℕ),
      IsAO2 n C → r < C.size → w < n + r →
      (∀ x : Fin n → Bool, x v = false → wval C x (n + r) = wval C x w) →
      ∃ E : Circuit, IsAO2 n E ∧ E.size + 1 = C.size ∧
        (∀ x : Fin n → Bool, x v = false → circuitFun n E x = circuitFun n C x) ∧
        ∀ (x : Fin n → Bool) (u : ℕ), u < n + r → wval E x u = wval C x u := by
    intro n C v r w model hr hw heq
    change r < C.gates.length at hr
    let E := bypass n C r w
    have ops : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨
        (gateAt C j).op = GateOp.or := fun j hj => model.1 _ (gateAt_mem hj)
    have modelE : IsAO2 n E := by
      refine ⟨?_, bypass_readsBack hw model.2.1, ?_⟩
      · intro g hg
        obtain ⟨g', hmem, hop, _⟩ := bypass_mem g hg
        rw [hop]
        exact model.1 g' hmem
      · intro g hg
        obtain ⟨g', hmem, _, hlen⟩ := bypass_mem g hg
        exact hlen.trans (model.2.2 g' hmem)
    refine ⟨E, modelE, ?_, ?_, ?_⟩
    · change (bypass n C r w).gates.length + 1 = C.gates.length
      rw [bypass_length]
      omega
    · intro x hx
      exact bypass_eval_eq List.length_ofFn ops hr (Or.inl hw) (heq x hx)
    · intro x u hu
      exact bypass_val_lt List.length_ofFn hr u hu
  let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let U := Ustar G D
  let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
  by_contra! short
  have h4 : NoFourCycle G := by dsimp [G]; decide +kernel
  have h16 : G.edgeFinset.card = 16 := by dsimp [G]; decide +kernel
  have h7 : ∀ K : Finset (Fin 11), G.IsVertexCover (K : Set (Fin 11)) → 7 ≤ K.card := by
    intro K hK
    classical
    let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
    have ew (u v : Fin 11) (he : G.Adj u v) : 1 ≤ w u + w v := by
      rcases hK he with hu | hv
      · change u ∈ K at hu
        simp [w, hu]
      · change v ∈ K at hv
        simp [w, hv]
    have e0 := ew 1 4 (by decide +kernel)
    have e1 := ew 4 8 (by decide +kernel)
    have e2 := ew 8 1 (by decide +kernel)
    have e3 := ew 3 6 (by decide +kernel)
    have e4 := ew 6 7 (by decide +kernel)
    have e5 := ew 7 3 (by decide +kernel)
    have e6 := ew 0 9 (by decide +kernel)
    have e7 := ew 9 5 (by decide +kernel)
    have e8 := ew 5 2 (by decide +kernel)
    have e9 := ew 2 10 (by decide +kernel)
    have e10 := ew 10 0 (by decide +kernel)
    have hw : ∑ i, w i = K.card := by
      simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    omega
  have he : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hs, hk⟩ := pre 11 G D h4 he hm ht
  rw [h16] at hs
  change 16 + (tops G D \ centreless G D).card + 2 * (centreless G D).card +
    (junk G D).card + (orN G D \ lam G D).card ≤ D.size + U.card + 1 at hs
  have acc : 16 + (tops G D \ centreless G D).card + B ≤ D.size + U.card + 1 := by
    dsimp [B]
    omega
  by_cases loose : 2 * U.card ≤ B
  · let H := G.deleteEdges (↑U)
    let P (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = m
    have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp [H], rfl⟩
    obtain ⟨K, hK, hcard⟩ := Nat.find_spec existsP
    have hmin : IsMinCover H K := by
      refine ⟨hK, fun T hT => ?_⟩
      exact hcard.trans_le (Nat.find_min' existsP ⟨T, hT, rfl⟩)
    have kt := hk K hmin
    let X := U.image (fun e => e.out.1)
    have hx : X.card ≤ U.card := Finset.card_image_le
    have cover : G.IsVertexCover (↑(K ∪ X)) := by
      intro u v huv
      by_cases eh : s(u,v) ∈ U
      · have hvx : s(u,v).out.1 ∈ X := Finset.mem_image_of_mem _ eh
        have hh := Sym2.out_fst_mem s(u,v)
        rw [Sym2.mem_iff] at hh
        rcases hh with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hvx))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hvx))
      · have hh : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, eh⟩
        rcases hK hh with h | h
        · exact Or.inl (Finset.mem_union_left X h)
        · exact Or.inr (Finset.mem_union_left X h)
    have score := h7 _ cover
    have card := Finset.card_union_le K X
    omega
  · have small : B < 2 * U.card := Nat.lt_of_not_ge loose
    obtain ⟨v, hv, i, j, k, hij, hjk, hk, ⟨wi, hwi, ei⟩, ⟨wj, hwj, ej⟩, wk, hwk, ek⟩ :=
      repeats D hm ht hj (by omega) small
    obtain ⟨E, mE, lE, oE, pE⟩ := drop 11 D v k wk hm.1 hk hwk ek
    have ejE (x : Fin 11 → Bool) (hx : x v = false) :
        wval E x (11 + j) = wval E x wj := by
      rw [pE x _ (by omega), pE x _ (by omega)]
      exact ej x hx
    obtain ⟨F, mF, lF, oF, pF⟩ := drop 11 E v j wj mE (by omega) hwj ejE
    have eiF (x : Fin 11 → Bool) (hx : x v = false) :
        wval F x (11 + i) = wval F x wi := by
      rw [pF x _ (by omega), pF x _ (by omega), pE x _ (by omega), pE x _ (by omega)]
      exact ei x hx
    obtain ⟨H, mH, lH, oH, _⟩ := drop 11 F v i wi mF (by omega) hwi eiF
    have face := faceBound v H hv mH (fun x hx =>
      (oH x hx).trans ((oF x hx).trans ((oE x hx).trans (congrFun hm.2.1 x))))
    omega
