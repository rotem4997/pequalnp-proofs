import Mathlib
import PEqualNP.Defs

-- Split the collapsing-gate property for the four degree-two vertices into two structural regimes:
-- either some vertex below 4 feeds a unique AND gate read by a unique OR gate,
-- or every vertex below 4 feeds at most two gates, all of them OR gates.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_8203_1
  (h1 : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)];
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      let ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
      let wv := PEqualNP.ReadTwo.wval C;
      let J := PEqualNP.TopForm.junk G C;
      (PEqualNP.TopForm.IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧ C.size ≤ 21 ∧ a ∈ J ∧ b ∈ J ∧ a < b ∧
        2 * (PEqualNP.TopForm.centreless G C).card + J.card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card < 2 * (PEqualNP.TopForm.Ustar G C).card ∧
        (∀ k ∈ [a, b], ∀ x : Fin 11 → Bool, wv x (11 + k) = true ↔ ∀ s : Fin 2, (∃ u ∈ PEqualNP.TopForm.side C k s, x u = true) ∨ k = b ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C k s) a ∧ wv x (11 + a) = true)) →
      ∀ (v : Fin 11) (g r : ℕ),
        (v.val < 4 ∧ g < r ∧ r < C.size ∧ (ga g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (ga r).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (∀ u < C.size, v.val ∈ (ga u).inputs ↔ u = g) ∧ (∀ u < C.size, 11 + g ∈ (ga u).inputs ↔ u = r)) →
        ∃ w : Fin 11, w.val < 4 ∧
          have P := fun i => ∃ j < 11 + i, ∀ x : Fin 11 → Bool, x w = false → wv x (11 + i) = wv x j;
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ P i ∧ P j ∧ P k)
  (h2 : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)];
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      let ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
      let wv := PEqualNP.ReadTwo.wval C;
      let J := PEqualNP.TopForm.junk G C;
      (PEqualNP.TopForm.IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧ C.size ≤ 21 ∧ a ∈ J ∧ b ∈ J ∧ a < b ∧
        2 * (PEqualNP.TopForm.centreless G C).card + J.card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card < 2 * (PEqualNP.TopForm.Ustar G C).card ∧
        (∀ k ∈ [a, b], ∀ x : Fin 11 → Bool, wv x (11 + k) = true ↔ ∀ s : Fin 2, (∃ u ∈ PEqualNP.TopForm.side C k s, x u = true) ∨ k = b ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C k s) a ∧ wv x (11 + a) = true) ∧
        (∀ v : Fin 11, v.val < 4 →
          (∀ u < C.size, v.val ∈ (ga u).inputs → (ga u).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∀ i j k : ℕ, i < j → j < k → k < C.size → v.val ∈ (ga i).inputs → v.val ∈ (ga j).inputs → v.val ∉ (ga k).inputs)) →
        ∃ w : Fin 11, w.val < 4 ∧
          have P := fun i => ∃ j < 11 + i, ∀ x : Fin 11 → Bool, x w = false → wv x (11 + i) = wv x j;
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ P i ∧ P j ∧ P k) :
  have x1 : ℕ := (11 : ℕ); let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x2 : ℕ) => (x2 / (11 : ℕ), x2 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   PEqualNP.TopForm.IsLeastAO x2 x3 →     PEqualNP.TopForm.TopForm x2 x3 →       x3.size ≤ (21 : ℕ) →         x4 ∈ PEqualNP.TopForm.junk x2 x3 →           x5 ∈ PEqualNP.TopForm.junk x2 x3 →             x4 < x5 →               (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card →                 (∀ x13 ∈ [x4, x5], ∀ (x15 : Fin x1 → Bool), PEqualNP.ReadTwo.wval x3 x15 (x1 + x13) = Bool.true ↔ ∀ (x16 : Fin (2 : ℕ)), (∃ x17 ∈ PEqualNP.TopForm.side x3 x13 x16, x15 x17 = Bool.true) ∨ x13 = x5 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x3 (PEqualNP.TopForm.opnd x3 x13 x16) x4 ∧ PEqualNP.ReadTwo.wval x3 x15 (x1 + x4) = Bool.true) →                   ∃ (x14 : Fin (11 : ℕ)),                     ↑x14 < (4 : ℕ) ∧                       have x15 : ℕ → Prop := fun (x15 : ℕ) => ∃ x16 < (11 : ℕ) + x15, ∀ (x17 : Fin (11 : ℕ) → Bool), x17 x14 = Bool.false → PEqualNP.ReadTwo.wval x3 x17 ((11 : ℕ) + x15) = PEqualNP.ReadTwo.wval x3 x17 x16;                       ∃ (x16 : ℕ) (x17 : ℕ) (x18 : ℕ), x16 < x17 ∧ x17 < x18 ∧ x18 < x3.size ∧ x15 x16 ∧ x15 x17 ∧ x15 x18 := by
  classical
  intro x1 x2 D x4 x5 hm ht hsz hx4 hx5 hx45 hnum hrec
  let stepWire (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt2 (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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

  have foldl_getD_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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

  let val (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : PEqualNP.CircuitLowerBounds.Circuit} {j : ℕ} (hj : j < C.gates.length) : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : PEqualNP.CircuitLowerBounds.Circuit} {j : ℕ} (hj : j < C.gates.length) : PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

  have val_ge {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : PEqualNP.CircuitLowerBounds.GateOp), (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have val_prefix {n : ℕ} {C D : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
      (hg : ∀ k < m, PEqualNP.MetaComplexity.NestedCover.gateAt D k = PEqualNP.MetaComplexity.NestedCover.gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
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

  let aliasGate (w i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (r i : ℕ) : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then PEqualNP.MetaComplexity.NestedCover.gateAt C k else aliasGate (n + r) i (PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

  have bypass_output (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      PEqualNP.MetaComplexity.NestedCover.gateAt (bypass n C r i) k =
        if k < r then PEqualNP.MetaComplexity.NestedCover.gateAt C k else aliasGate (n + r) i (PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp [bypass]

  have bypass_val_lt {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
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
      {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) →
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
      {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or)
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

  have bypass_mem {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨PEqualNP.MetaComplexity.NestedCover.gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  have bypass_ok {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
      (hR : ((∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) ∨
        C.output = n + r) → val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · rw [h, aliasWire_self, bypass_val_lt hx hr i hi]
      exact (hR (Or.inr h)).symm
    · exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr (Or.inl hi)
        (fun hk => hR (Or.inl hk)) _ h).symm

  have dropG : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (r w : ℕ), PEqualNP.TopForm.IsAO2 11 C → r < C.gates.length → w < 11 + r →
      (((∃ k, r < k ∧ k < C.gates.length ∧ 11 + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) ∨ C.output = 11 + r) →
        ∀ x : Fin 11 → Bool, PEqualNP.ReadTwo.wval C x (11 + r) = PEqualNP.ReadTwo.wval C x w) →
      ∃ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 11 E ∧ E.gates.length + 1 = C.gates.length ∧
        PEqualNP.MetaComplexity.circuitFun 11 E = PEqualNP.MetaComplexity.circuitFun 11 C := by
    intro C r w model hr hw heq
    have ops : ∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or := fun j hj => model.1 _ (gateAt_mem hj)
    have modelE : PEqualNP.TopForm.IsAO2 11 (bypass 11 C r w) := by
      refine ⟨?_, bypass_readsBack hw model.2.1, ?_⟩
      · intro g hg
        obtain ⟨g', hmem, hop, _⟩ := bypass_mem g hg
        rw [hop]
        exact model.1 g' hmem
      · intro g hg
        obtain ⟨g', hmem, _, hlen⟩ := bypass_mem g hg
        exact hlen.trans (model.2.2 g' hmem)
    refine ⟨bypass 11 C r w, modelE, ?_, ?_⟩
    · rw [bypass_length]
      omega
    · funext x
      exact bypass_ok List.length_ofFn ops hr hw (fun h => heq h x)

  have hAO2 : PEqualNP.TopForm.IsAO2 11 D := hm.1
  have hfun : PEqualNP.MetaComplexity.circuitFun 11 D = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := hm.2.1
  have noRep : ∀ r w : ℕ, r < D.gates.length → w < 11 + r →
      (((∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs) ∨ D.output = 11 + r) →
        ∀ x : Fin 11 → Bool, PEqualNP.ReadTwo.wval D x (11 + r) = PEqualNP.ReadTwo.wval D x w) → False := by
    intro r w hr hw heq
    obtain ⟨E, mE, lE, fE⟩ := dropG D r w hAO2 hr hw heq
    have hle := hm.2.2 E mE (fE.trans hfun)
    change D.gates.length ≤ E.gates.length at hle
    omega

  have hasReader : ∀ r, r < D.gates.length → D.output ≠ 11 + r →
      ∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs := by
    intro r hr hout
    by_contra hno
    refine noRep r 0 hr (by omega) ?_
    rintro (h | h)
    · exact absurd h hno
    · exact absurd h hout

  have hRB : ∀ k < D.gates.length, ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, u < 11 + k := hAO2.2.1
  have hops : ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.or := fun k hk => hAO2.1 _ (gateAt_mem hk)
  have hlen2 : ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs.length = 2 :=
    fun k hk => hAO2.2.2 _ (gateAt_mem hk)
  have andE : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have orE : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have gsem : ∀ k < D.gates.length, ∃ p q : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs = [p, q] ∧ p < 11 + k ∧
      q < 11 + k ∧ (∀ x : Fin 11 → Bool,
        PEqualNP.ReadTwo.wval D x (11 + k) = (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op.eval [PEqualNP.ReadTwo.wval D x p, PEqualNP.ReadTwo.wval D x q]) := by
    intro k hk
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen2 k hk)
    have hp : p < 11 + k := hRB k hk p (by rw [hpq]; simp)
    have hq : q < 11 + k := hRB k hk q (by rw [hpq]; simp)
    refine ⟨p, q, hpq, hp, hq, fun x => ?_⟩
    have hv := val_gate (C := D) (x := List.ofFn x) List.length_ofFn hk
    rw [hpq] at hv
    simp only [List.map_cons, List.map_nil, ite_eq_left hp, ite_eq_left hq] at hv
    exact hv
  have hin : ∀ (v : Fin 11) (x : Fin 11 → Bool), PEqualNP.ReadTwo.wval D x v.val = x v := by
    intro v x
    have hv := val_input (C := D) (x := List.ofFn x) List.length_ofFn v.isLt
    refine hv.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _
  have zv : ∀ (v : Fin 11) (x : Fin 11 → Bool), x v = false → PEqualNP.ReadTwo.wval D x v.val = false :=
    fun v x hx => (hin v x).trans hx
  have zand : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs → (∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x u = false) →
      ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + k) = false := by
    intro v k u hk hop hu hz x hx
    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
    rw [hpq, List.mem_pair] at hu
    rw [hs x, hop, andE]
    have hzz := hz x hx
    rcases hu with h | h <;> subst h <;> simp [hzz]
  have rep1 : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs →
      (∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x u = false) →
      ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + k) = PEqualNP.ReadTwo.wval D x w := by
    intro v k u hk hu hz
    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
    have hu' := hu
    rw [hpq, List.mem_pair] at hu'
    rcases hops k hk with hop | hop
    · refine ⟨u, hRB k hk u hu, fun x hx => ?_⟩
      rw [zand v k u hk hop hu hz x hx, hz x hx]
    · rcases hu' with h | h
      · subst h
        refine ⟨q, hq, fun x hx => ?_⟩
        have hzz := hz x hx
        rw [hs x, hop, orE]
        simp [hzz]
      · subst h
        refine ⟨p, hp, fun x hx => ?_⟩
        have hzz := hz x hx
        rw [hs x, hop, orE]
        simp [hzz]
  have outNZ : ∀ (v : Fin 11) (g : ℕ), v.val < 4 →
      (∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + g) = false) → D.output ≠ 11 + g := by
    intro v g hv hz hout
    have e1 := hz (fun i : Fin 11 => decide (4 ≤ i.val)) (by simpa using hv)
    have e0 : PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]) ∅ (fun i : Fin 11 => decide (4 ≤ i.val)) = true := by
      decide +kernel
    have e2 : PEqualNP.MetaComplexity.circuitFun 11 D (fun i : Fin 11 => decide (4 ≤ i.val)) = true := by
      rw [hfun]
      exact e0
    have e3 : PEqualNP.MetaComplexity.circuitFun 11 D (fun i : Fin 11 => decide (4 ≤ i.val)) =
        PEqualNP.ReadTwo.wval D (fun i : Fin 11 => decide (4 ≤ i.val)) D.output := rfl
    rw [e3, hout, e1] at e2
    exact Bool.false_ne_true e2
  have fin : ∀ (v : Fin 11), v.val < 4 → ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
      a < D.gates.length → b < D.gates.length → c < D.gates.length →
      (∃ w < 11 + a, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + a) = PEqualNP.ReadTwo.wval D x w) →
      (∃ w < 11 + b, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + b) = PEqualNP.ReadTwo.wval D x w) →
      (∃ w < 11 + c, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + c) = PEqualNP.ReadTwo.wval D x w) →
      ∃ x8 : Fin 11, x8.val < 4 ∧ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < D.size ∧
        (∃ w < 11 + i, ∀ x : Fin 11 → Bool, x x8 = false → PEqualNP.ReadTwo.wval D x (11 + i) = PEqualNP.ReadTwo.wval D x w) ∧
        (∃ w < 11 + j, ∀ x : Fin 11 → Bool, x x8 = false → PEqualNP.ReadTwo.wval D x (11 + j) = PEqualNP.ReadTwo.wval D x w) ∧
        (∃ w < 11 + k, ∀ x : Fin 11 → Bool, x x8 = false → PEqualNP.ReadTwo.wval D x (11 + k) = PEqualNP.ReadTwo.wval D x w) := by
    intro v hv a b c hab hac hbc ha hb hc ra rb rc
    refine ⟨v, hv, ?_⟩
    rcases lt_or_gt_of_ne hab with o1 | o1 <;> rcases lt_or_gt_of_ne hac with o2 | o2 <;>
      rcases lt_or_gt_of_ne hbc with o3 | o3 <;>
      first
      | exact ⟨a, b, c, by omega, by omega, hc, ra, rb, rc⟩
      | exact ⟨a, c, b, by omega, by omega, hb, ra, rc, rb⟩
      | exact ⟨b, a, c, by omega, by omega, hc, rb, ra, rc⟩
      | exact ⟨b, c, a, by omega, by omega, ha, rb, rc, ra⟩
      | exact ⟨c, a, b, by omega, by omega, hb, rc, ra, rb⟩
      | exact ⟨c, b, a, by omega, by omega, ha, rc, rb, ra⟩
  by_cases hA : ∃ v : Fin 11, v.val < 4 ∧ ∃ g, g < D.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt D g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D g).inputs
  · obtain ⟨v, hv, g, hg, hgop, hgv⟩ := hA
    have zg := zand v g v.val hg hgop hgv (zv v)
    have rg := rep1 v g v.val hg hgv (zv v)
    obtain ⟨r, hgr, hr, hrg⟩ := hasReader g hg (outNZ v g hv zg)
    have rr := rep1 v r (11 + g) hr hrg zg
    rcases hops r hr with hrop | hrop
    · have zr := zand v r (11 + g) hr hrop hrg zg
      obtain ⟨s, hrs, hs, hsr⟩ := hasReader r hr (outNZ v r hv zr)
      exact fin v hv g r s (by omega) (by omega) (by omega) hg hr hs rg rr
        (rep1 v s (11 + r) hs hsr zr)
    · by_cases hB : ∃ k, k < D.gates.length ∧ k ≠ g ∧ k ≠ r ∧
          (v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs ∨ 11 + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs)
      · obtain ⟨k, hk, hkg, hkr, hkin⟩ := hB
        have rk : ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false →
            PEqualNP.ReadTwo.wval D x (11 + k) = PEqualNP.ReadTwo.wval D x w := by
          rcases hkin with h | h
          · exact rep1 v k v.val hk h (zv v)
          · exact rep1 v k (11 + g) hk h zg
        exact fin v hv g r k (by omega) (Ne.symm hkg) (Ne.symm hkr) hg hr hk rg rr rk
      · have hvr : v.val ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt D r).inputs := by
          intro hvr
          refine noRep r v.val hr (by omega) (fun _ x => ?_)
          obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem r hr
          have hvr' := hvr
          have hrg' := hrg
          rw [hpq, List.mem_pair] at hvr' hrg'
          rw [hs x, hrop, orE]
          cases hxv : PEqualNP.ReadTwo.wval D x v.val with
          | false =>
            have hz := gsem g hg
            have hz2 : PEqualNP.ReadTwo.wval D x (11 + g) = false := by
              obtain ⟨p', q', hpq', hp', hq', hs'⟩ := hz
              have hgv' := hgv
              rw [hpq', List.mem_pair] at hgv'
              rw [hs' x, hgop, andE]
              rcases hgv' with h | h <;> subst h <;> simp [hxv]
            rcases hvr' with h | h <;> rcases hrg' with h' | h' <;>
              first
              | (exfalso; omega)
              | (subst h; subst h'; simp [hxv, hz2])
          | true =>
            rcases hvr' with h | h <;> rcases hrg' with h' | h' <;>
              first
              | (exfalso; omega)
              | (subst h; subst h'; simp [hxv])
        have u1 : ∀ k < D.size, (v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs ↔ k = g) := by
          intro k hk
          constructor
          · intro h
            by_contra hne
            by_cases hkr : k = r
            · exact hvr (hkr ▸ h)
            · exact hB ⟨k, hk, hne, hkr, Or.inl h⟩
          · intro h
            rw [h]
            exact hgv
        have u2 : ∀ k < D.size, (11 + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs ↔ k = r) := by
          intro k hk
          constructor
          · intro h
            by_contra hne
            have hkg : k ≠ g := by
              intro e
              have hlt := hRB k hk _ h
              omega
            exact hB ⟨k, hk, hkg, hne, Or.inr h⟩
          · intro h
            rw [h]
            exact hrg
        exact h1 D x4 x5 ⟨hm, ht, hsz, hx4, hx5, hx45, hnum, hrec⟩ v g r ⟨hv, hgr, hr, hgop, hrop, u1, u2⟩
  · by_cases hC : ∃ v : Fin 11, v.val < 4 ∧ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < D.gates.length ∧
        v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs ∧ v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs ∧ v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs
    · obtain ⟨v, hv, i, j, k, hij, hjk, hk, hi, hj', hk'⟩ := hC
      exact fin v hv i j k (by omega) (by omega) (by omega) (by omega) (by omega) hk
        (rep1 v i v.val (by omega) hi (zv v)) (rep1 v j v.val (by omega) hj' (zv v))
        (rep1 v k v.val hk hk' (zv v))
    · refine h2 D x4 x5 ⟨hm, ht, hsz, hx4, hx5, hx45, hnum, hrec, fun v hv => ⟨fun k hk hkv => ?_,
        fun i j k hij hjk hk hi hj' hk' => hC ⟨v, hv, i, j, k, hij, hjk, hk, hi, hj', hk'⟩⟩⟩
      rcases hops k hk with h | h
      · exact absurd ⟨v, hv, k, hk, h, hkv⟩ hA
      · exact h
