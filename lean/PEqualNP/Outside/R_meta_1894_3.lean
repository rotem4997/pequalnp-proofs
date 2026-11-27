import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1894_3
    (hAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 →
      (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔
        ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)),
          (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) =>
            [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6),
             (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)),
             (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧
          x3 x4 = Bool.true ∧ x3 x5 = Bool.true) →
      (21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    (hDualAnd : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D →
      (∀ (x : Fin 42 → Bool),
        PEqualNP.MetaComplexity.circuitFun 43 D
          (fun i : Fin (42 + 1) => Fin.cases true (fun j : Fin 42 => !x j) i) =
        !decide (∃ (p l : Fin 42),
          (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x p = true ∧ x l = true)) →
      (104 : ℕ) ≤ {i : Fin D.gates.length | (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  classical
  intro C hMono hSize _
  by_contra hNoBad
  have hComp : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42,
        (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x u = true ∧ x v = true := by
    intro x
    by_contra hbad
    exact hNoBad ⟨x, hbad⟩
  have hEdgeEq : ∀ u v : Fin 42,
      (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ↔
      (u.val, v.val) ∈ List.flatMap (fun k : ℕ =>
        [(k, 21 + (k + 20) % 21), (k, 21 + k), (k, 21 + (k + 5) % 21),
         (k, 21 + (k + 7) % 21), (k, 21 + (k + 17) % 21)]) (List.range 21) := by
    intro u v
    rw [List.mem_flatMap]
    have hvlt : v.val < 42 := v.isLt
    constructor
    · intro h
      obtain ⟨hu, hv, hm⟩ := h
      refine ⟨u.val, List.mem_range.mpr hu, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hm ⊢
      obtain h0 | hm := hm
      · right; left; omega
      · obtain h5 | hm := hm
        · right; right; left; omega
        · obtain h7 | hm := hm
          · right; right; right; left; omega
          · obtain h17 | h20 := hm
            · right; right; right; right; omega
            · left; omega
    · intro h
      obtain ⟨k, hk, hmem⟩ := h
      have hklt : k < 21 := List.mem_range.mp hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem ⊢
      obtain ⟨huk, hvk⟩ | hmem := hmem
      · refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (by omega))))⟩
      · obtain ⟨huk, hvk⟩ | hmem := hmem
        · refine ⟨by omega, by omega, Or.inl (by omega)⟩
        · obtain ⟨huk, hvk⟩ | hmem := hmem
          · refine ⟨by omega, by omega, Or.inr (Or.inl (by omega))⟩
          · obtain ⟨huk, hvk⟩ | ⟨huk, hvk⟩ := hmem
            · refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inl (by omega)))⟩
            · refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inl (by omega))))⟩
  have hAndGe : 21 ≤ {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard := by
    refine hAnd C hMono ?_
    intro x
    refine (hComp x).trans ?_
    constructor
    · intro hx
      obtain ⟨u, v, huv, hxu, hxv⟩ := hx
      exact ⟨u, v, (hEdgeEq u v).mp huv, hxu, hxv⟩
    · intro hx
      obtain ⟨u, v, huv, hxu, hxv⟩ := hx
      exact ⟨u, v, (hEdgeEq u v).mpr huv, hxu, hxv⟩
  let sw : GateOp → GateOp := fun o =>
    if o = GateOp.and then GateOp.or else if o = GateOp.or then GateOp.and else o
  have hsw_and : sw GateOp.and = GateOp.or := ite_eq_left rfl
  have hsw_or : sw GateOp.or = GateOp.and := by
    change (if GateOp.or = GateOp.and then GateOp.or else if GateOp.or = GateOp.or then GateOp.and else GateOp.or) = GateOp.and
    rw [ite_eq_right (fun h => GateOp.noConfusion h), ite_eq_left rfl]
  have hsw_eq_and : ∀ o : GateOp, (o = GateOp.and ∨ o = GateOp.or) → (sw o = GateOp.and ↔ o = GateOp.or) := by
    intro o ho
    obtain rfl | rfl := ho
    · rw [hsw_and]
      constructor
      · intro h; exact False.elim (GateOp.noConfusion h)
      · intro h; exact False.elim (GateOp.noConfusion h)
    · rw [hsw_or]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  let rr : ℕ → ℕ → ℕ := fun m w => if w < m then w + 1 else 0
  let dl : List Gate → ℕ → List Gate := fun gs =>
    List.rec (fun _ => []) (fun g _ ih m => ⟨sw g.op, g.inputs.map (rr m)⟩ :: ih (m + 1)) gs
  have hdl_len : ∀ (gs : List Gate) (m : ℕ), (dl gs m).length = gs.length := by
    intro gs
    induction gs with
    | nil => intro _; rfl
    | cons g gs ih =>
      intro m
      change ((⟨sw g.op, g.inputs.map (rr m)⟩ : Gate) :: dl gs (m + 1)).length = (g :: gs).length
      rw [List.length_cons, List.length_cons, ih (m + 1)]
  have hdl_get : ∀ (gs : List Gate) (m i : ℕ) (h1 : i < (dl gs m).length) (h2 : i < gs.length),
      ((dl gs m).get ⟨i, h1⟩).op = sw (gs.get ⟨i, h2⟩).op := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h2; exact False.elim (Nat.not_lt_zero _ h2)
    | cons g gs ih =>
      intro m i
      induction i with
      | zero => intro _ _; rfl
      | succ i _ =>
        intro h1 h2
        exact ih (m + 1) i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)
  have hdl_mono : ∀ (gs : List Gate) (m : ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ dl gs m, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro gs
    induction gs with
    | nil =>
      intro _ _ g hg
      exact False.elim (List.not_mem_nil hg)
    | cons g gs ih =>
      intro m h g' hg'
      change g' ∈ (⟨sw g.op, g.inputs.map (rr m)⟩ : Gate) :: dl gs (m + 1) at hg'
      obtain rfl | hmem := List.mem_cons.mp hg'
      · obtain ⟨h1, h2⟩ := h g (List.mem_cons_self)
        have h1' : g.op = GateOp.and ∨ g.op = GateOp.or := h1
        refine ⟨?_, ?_⟩
        · obtain hop | hop := h1'
          · rw [hop, hsw_and]; exact Or.inr rfl
          · rw [hop, hsw_or]; exact Or.inl rfl
        · change (g.inputs.map (rr m)).length ≤ 2
          rw [List.length_map]
          exact h2
      · exact ih (m + 1) (fun g0 hg0 => h g0 (List.mem_cons_of_mem g hg0)) g' hmem
  have hdemorgan : ∀ (o : GateOp), (o = GateOp.and ∨ o = GateOp.or) → ∀ l : List Bool,
      (sw o).eval (l.map not) = !o.eval l := by
    intro o ho l
    obtain rfl | rfl := ho
    · rw [hsw_and]
      change (l.map not).any id = !(l.all id)
      induction l with
      | nil => rfl
      | cons b bs ih =>
        rw [List.map_cons, List.any_cons, List.all_cons, id_eq, id_eq, ih]
        cases b <;> rfl
    · rw [hsw_or]
      change (l.map not).all id = !(l.any id)
      induction l with
      | nil => rfl
      | cons b bs ih =>
        rw [List.map_cons, List.all_cons, List.any_cons, id_eq, id_eq, ih]
        cases b <;> rfl
  let run : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  let Inv : ℕ → List Bool → List Bool → Prop := fun m W W' =>
    W.length = m ∧ W'.length = m + 1 ∧ ∀ w, W'.getD (rr m w) false = !W.getD w false
  have hinv_step : ∀ (m : ℕ) (W W' : List Bool), Inv m W W' →
      ∀ (g : Gate), (g.op = GateOp.and ∨ g.op = GateOp.or) →
      Inv (m + 1)
        (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
        (W' ++ [(sw g.op).eval ((g.inputs.map (rr m)).map fun i => W'.getD i false)]) := by
    intro m W W' hI g hg
    obtain ⟨h1, h2, h3⟩ := hI
    have hv : (sw g.op).eval ((g.inputs.map (rr m)).map fun i => W'.getD i false) =
        !g.op.eval (g.inputs.map fun i => W.getD i false) := by
      rw [← hdemorgan g.op hg, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h3 i
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton, h1]
    · rw [List.length_append, List.length_singleton, h2]
    · intro w
      rw [hv]
      by_cases hwlt : w < m
      · have he1 : rr m w = w + 1 := ite_eq_left hwlt
        have he2 : rr (m + 1) w = w + 1 := ite_eq_left (Nat.lt_succ_of_lt hwlt)
        have h3w := h3 w
        rw [he1] at h3w
        rw [he2, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), h3w]
      · by_cases hweq : w = m
        · rw [hweq]
          have he2 : rr (m + 1) m = m + 1 := ite_eq_left (Nat.lt_succ_self m)
          rw [he2, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          rw [h1, h2, Nat.sub_self, Nat.sub_self]
          rfl
        · have hwgt : m + 1 ≤ w := by omega
          have he0 : rr m m = 0 := ite_eq_right (Nat.lt_irrefl m)
          have he2 : rr (m + 1) w = 0 := ite_eq_right (by omega)
          have h3m := h3 m
          rw [he0, List.getD_eq_default W false (by omega)] at h3m
          rw [he2, List.getD_append W' _ false 0 (by omega), h3m,
            List.getD_eq_default (W ++ _) false (by rw [List.length_append, List.length_singleton, h1]; omega)]
  have hinv_run : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ (m : ℕ) (W W' : List Bool), Inv m W W' →
      Inv (m + gs.length) (run gs W) (run (dl gs m) W') := by
    intro gs
    induction gs with
    | nil =>
      intro _ m W W' hI
      exact hI
    | cons g gs ih =>
      intro hg m W W' hI
      have hstep := hinv_step m W W' hI g (hg g List.mem_cons_self)
      have hrec := ih (fun g0 hg0 => hg g0 (List.mem_cons_of_mem g hg0)) (m + 1) _ _ hstep
      have hlenEq : m + 1 + gs.length = m + (g :: gs).length := by
        rw [List.length_cons]
        omega
      rw [hlenEq] at hrec
      exact hrec
  let D : Circuit := ⟨dl C.gates 42, rr (42 + C.gates.length) C.output⟩
  have hMonoD : Monotone2 D := hdl_mono C.gates 42 hMono
  have hDualEval : ∀ x : Fin 42 → Bool,
      circuitFun 43 D (fun i : Fin (42 + 1) => Fin.cases true (fun j : Fin 42 => !x j) i) =
      !decide (∃ p l : Fin 42,
        (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x p = true ∧ x l = true) := by
    intro x
    have hW : List.ofFn (fun i : Fin (42 + 1) => Fin.cases true (fun j : Fin 42 => !x j) i) =
        true :: (List.ofFn x).map not := by
      rw [List.ofFn_succ, List.map_ofFn]
      rfl
    have hI0 : Inv 42 (List.ofFn x) (true :: (List.ofFn x).map not) := by
      refine ⟨List.length_ofFn, ?_, ?_⟩
      · rw [List.length_cons, List.length_map, List.length_ofFn]
      · intro w
        by_cases hw : w < 42
        · have hrw : rr 42 w = w + 1 := ite_eq_left hw
          rw [hrw]
          change ((List.ofFn x).map not).getD w false = !(List.ofFn x).getD w false
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_ofFn, dite_eq_left hw]
          rfl
        · have hrw : rr 42 w = 0 := ite_eq_right hw
          rw [hrw]
          rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
          rfl
    have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hMono g hg).1
    obtain ⟨_, _, hres⟩ := hinv_run C.gates hgs 42 _ _ hI0
    have hval : circuitFun 43 D (fun i : Fin (42 + 1) => Fin.cases true (fun j : Fin 42 => !x j) i) =
        !C.eval (List.ofFn x) := by
      change (run (dl C.gates 42)
        (List.ofFn (fun i : Fin (42 + 1) => Fin.cases true (fun j : Fin 42 => !x j) i))).getD
        (rr (42 + C.gates.length) C.output) false = !(run C.gates (List.ofFn x)).getD C.output false
      rw [hW]
      exact hres C.output
    rw [hval]
    congr 1
    by_cases he : ∃ p l : Fin 42,
        (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x p = true ∧ x l = true
    · rw [decide_eq_true he, (hComp x).mpr he]
    · rw [decide_eq_false he]
      by_cases hc : C.eval (List.ofFn x) = true
      · exact False.elim (he ((hComp x).mp hc))
      · exact Bool.eq_false_iff.mpr hc
  have hDualGe : 104 ≤ {i : Fin D.gates.length | (D.gates.get i).op = GateOp.and}.ncard :=
    hDualAnd D hMonoD hDualEval
  have hOrEq : {i : Fin D.gates.length | (D.gates.get i).op = GateOp.and}.ncard =
      {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquiv (finCongr (hdl_len C.gates 42)) ?_)
    intro i
    have hgi := hdl_get C.gates 42 i.1 i.2 (by rw [← hdl_len C.gates 42]; exact i.2)
    have hmem : C.gates.get ⟨i.1, by rw [← hdl_len C.gates 42]; exact i.2⟩ ∈ C.gates := List.get_mem _ _
    have hop : (C.gates.get ⟨i.1, by rw [← hdl_len C.gates 42]; exact i.2⟩).op = GateOp.and ∨
        (C.gates.get ⟨i.1, by rw [← hdl_len C.gates 42]; exact i.2⟩).op = GateOp.or := (hMono _ hmem).1
    change (D.gates.get i).op = GateOp.and ↔
      (C.gates.get ⟨i.1, by rw [← hdl_len C.gates 42]; exact i.2⟩).op = GateOp.or
    change ((dl C.gates 42).get i).op = GateOp.and ↔ _
    rw [hgi]
    exact hsw_eq_and _ hop
  have hSum : {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard +
      {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard = C.size := by
    let SA : Set (Fin C.gates.length) := {i | (C.gates.get i).op = GateOp.and}
    let SO : Set (Fin C.gates.length) := {i | (C.gates.get i).op = GateOp.or}
    have hDisj : Disjoint SA SO := by
      rw [Set.disjoint_left]
      intro i hiA hiO
      have hA : (C.gates.get i).op = GateOp.and := hiA
      have hO : (C.gates.get i).op = GateOp.or := hiO
      rw [hA] at hO
      exact GateOp.noConfusion hO
    have hUnion : SA ∪ SO = Set.univ := by
      ext i
      constructor
      · intro _; trivial
      · intro _
        exact (hMono _ (List.get_mem C.gates i)).1
    have hnc := Set.ncard_union_eq hDisj (Set.toFinite SA) (Set.toFinite SO)
    rw [hUnion, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hnc
    exact hnc.symm
  omega
