import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3614_1
    (h_minor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)) 12)
    (h_full14 : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool =>
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) 14)
    (h_norm :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let X : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      let reads : ℕ → Gate → Bool := fun w g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains w
      ∀ (j : Fin 9) (C : Circuit) (k : ℕ) (d : Bool),
        j ≠ 0 → j ≠ 6 → FanInTwo C → C.size = 13 → 10 ≤ k → k < 23 →
        (∀ g ∈ C.gates.take (k + 1 - 10), j.val ∉ g.inputs) →
        (∀ x y : Fin 9 → Bool, (∀ i, i ≠ j → x i = y i) → F x ≠ F y →
          (C.wires (X x)).getD k false = !d) →
        (∃ g ∈ C.gates, reads 9 g = true) →
        (∃ g : Gate, g.op = GateOp.or ∧
          (∃ u : ℕ, u ∉ ([0, 6, 9] : List ℕ) ∧ (g.inputs = [6, u] ∨ g.inputs = [u, 6])) ∧
          C.gates.filter (reads 6) = [g]) →
        (∃ x : Fin 9 → Bool, x 6 = false ∧ (C.wires (X x)).getD k false = d) →
        ∃ x : Fin 9 → Bool,
          let a := (C.wires (X x)).getD k false
          C.eval ((X x).set j.val (if d then x j || a else x j && a)) ≠ F x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < (10 : ℕ) + x4.size →               (∀ x13 ∈ List.take (x5 + (1 : ℕ) - (10 : ℕ)) x4.gates, ↑x3 ∉ x13.inputs) →                 (∀ (x14 x15 : Fin (9 : ℕ) → Bool), (∀ (x16 : Fin (9 : ℕ)), x16 ≠ x3 → x14 x16 = x15 x16) → x1 x14 ≠ x1 x15 → (x4.wires (x2 x14)).getD x5 Bool.false = !x6) →                   ∃ (x15 : Fin (9 : ℕ) → Bool),                     have x16 : Bool := (x4.wires (x2 x15)).getD x5 Bool.false;                     x4.eval ((x2 x15).set (↑x3) (if x6 = Bool.true then x15 x3 || x16 else x15 x3 && x16)) ≠ x1 x15 := by
  dsimp only
  intro j C k d hj0 hj6 hFan hSize hk10 hkLt hPreNoJ hDom
  by_contra hAll
  push Not at hAll
  let F : (Fin 9 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
      x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let X : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
  let minor : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  let reads : ℕ → Gate → Bool := fun w g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains w
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have hEvalAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hEvalOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hEvalNot : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have hEvalAndF : GateOp.and.eval [false] = false := rfl
  have hEvalOrF : GateOp.or.eval [false] = false := rfl
  have hEvalNotF : GateOp.not.eval [false] = true := rfl
  have hcontains_true : ∀ (l : List ℕ) (a : ℕ), l.contains a = true ↔ a ∈ l := by
    intro l a; simp
  have hcontains_false : ∀ (l : List ℕ) (a : ℕ), l.contains a = false ↔ a ∉ l := by
    intro l a; simp
  have hrun_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih =>
      intro w
      change (run gs (step w g)).length = w.length + (gs.length + 1)
      rw [ih]; simp [step]; omega
  have hrun_append : ∀ (gs1 gs2 : List Gate) (w : List Bool),
      run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
    intro gs1 gs2 w; simp [run, List.foldl_append]
  have hrun_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (run gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (run gs (step w g)).getD i false = w.getD i false
      rw [ih (step w g) i (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have hgetD_snoc_lt : ∀ {α : Type} (w : List α) (b d0 : α) (i : ℕ), i < w.length →
      (w ++ [b]).getD i d0 = w.getD i d0 := by
    intro α w b d0 i hi; exact List.getD_append _ _ _ _ hi
  have hgetD_snoc_eq : ∀ {α : Type} (w : List α) (b d0 : α), (w ++ [b]).getD w.length d0 = b := by
    intro α w b d0; simp [List.getD_eq_getElem?_getD]
  have hgetD_snoc_gt : ∀ {α : Type} (w : List α) (b d0 : α) (i : ℕ), w.length < i →
      (w ++ [b]).getD i d0 = d0 := by
    intro α w b d0 i hi
    rw [List.getD_eq_default]; simp; omega
  have hX_len : ∀ x : Fin 9 → Bool, (X x).length = 10 := by
    intro x; simp [X]
  have hX_lt : ∀ (x : Fin 9 → Bool) (i : Fin 9), (X x).getD i.val false = x i := by
    intro x i
    rw [show X x = List.ofFn x ++ [x 0 || x 6] from rfl,
        List.getD_append _ _ _ _ (by simp)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  have hX_9 : ∀ x : Fin 9 → Bool, (X x).getD 9 false = (x 0 || x 6) := by
    intro x
    simp [X, List.getD_eq_getElem?_getD]
  have hgate_ok : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      g.inputs.length ≤ 2 → ∀ (w1 w2 : List Bool) (S : ℕ → Prop),
      (∀ i, ¬ S i → w1.getD i false = w2.getD i false) →
      (∀ i, S i → reads i g = false) →
      g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
    intro g hop hlen w1 w2 S hAgree hNoRead
    rcases hop with hAnd | hOr | hNot
    · rw [hAnd]; congr 1
      apply List.map_congr_left
      intro i hi
      apply hAgree
      intro hSi
      have hr := hNoRead i hSi
      have htake : g.inputs.take 2 = g.inputs := List.take_of_length_le hlen
      simp only [reads, hAnd, hEvalAndF, Bool.cond_false, htake] at hr
      exact ((hcontains_false _ _).mp hr) hi
    · rw [hOr]; congr 1
      apply List.map_congr_left
      intro i hi
      apply hAgree
      intro hSi
      have hr := hNoRead i hSi
      have htake : g.inputs.take 2 = g.inputs := List.take_of_length_le hlen
      simp only [reads, hOr, hEvalOrF, Bool.cond_false, htake] at hr
      exact ((hcontains_false _ _).mp hr) hi
    · change g.op = GateOp.not at hNot
      rw [hNot]
      cases hgi : g.inputs with
      | nil => rfl
      | cons a rest =>
        simp only [hEvalNot, List.map_cons, List.headD_cons]
        congr 1
        apply hAgree
        intro hSa
        have hr := hNoRead a hSa
        simp only [reads, hNot, hEvalNotF, Bool.cond_true, hgi, List.take_succ_cons, List.take_zero] at hr
        exact ((hcontains_false [a] a).mp hr) List.mem_cons_self
  have hrun_agree_off : ∀ (gs : List Gate) (w1 w2 : List Bool) (S : ℕ → Prop),
      w1.length = w2.length →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i, ¬ S i → w1.getD i false = w2.getD i false) →
      (∀ g ∈ gs, ∀ i, S i → reads i g = false) →
      ∀ i, ¬ S i → (run gs w1).getD i false = (run gs w2).getD i false := by
    intro gs
    induction gs with
    | nil => intro w1 w2 S _ _ hA _ i hi; exact hA i hi
    | cons g gs ih =>
      intro w1 w2 S hlen hok hA hNR i hi
      change (run gs (step w1 g)).getD i false = (run gs (step w2 g)).getD i false
      have hgok := hok g List.mem_cons_self
      have hgv := hgate_ok g hgok.1 hgok.2 w1 w2 S hA (hNR g List.mem_cons_self)
      apply ih (step w1 g) (step w2 g) S (by simp [step, hlen])
        (fun h hh => hok h (List.mem_cons_of_mem _ hh))
        (fun idx hidx => by
          rcases Nat.lt_trichotomy idx w1.length with hlt | heq | hgt
          · rw [hgetD_snoc_lt _ _ _ _ hlt, hgetD_snoc_lt _ _ _ _ (by omega)]
            exact hA idx hidx
          · subst heq
            rw [hgetD_snoc_eq, hlen, hgetD_snoc_eq, hgv]
          · rw [hgetD_snoc_gt _ _ _ _ hgt, hgetD_snoc_gt _ _ _ _ (by omega)])
        (fun h hh => hNR h (List.mem_cons_of_mem _ hh))
        i hi
  -- Step A: Materialize C1 of size C.size + 1 <= 14 on X x computing F x
  let pre : List Gate := C.gates.take (k + 1 - 10)
  let post : List Gate := C.gates.drop (k + 1 - 10)
  have hpre_post : pre ++ post = C.gates := List.take_append_drop _ _
  have hpre_len : pre.length = k + 1 - 10 := by
    simp only [pre, List.length_take]
    have : C.size = C.gates.length := rfl
    omega
  let gj : Gate := ⟨if d then GateOp.or else GateOp.and, [j.val, k]⟩
  let remap : ℕ → ℕ := fun i => if i = j.val then k + 1 else if k + 1 ≤ i then i + 1 else i
  let post' : List Gate := post.map (fun g => ⟨g.op, g.inputs.map remap⟩)
  let C1 : Circuit := ⟨pre ++ gj :: post', remap C.output⟩
  have hC1_size : C1.size = C.size + 1 := by
    change (pre ++ gj :: post').length = C.gates.length + 1
    rw [List.length_append, List.length_cons, List.length_map]
    have hpp := congrArg List.length hpre_post
    rw [List.length_append] at hpp
    omega
  have hC1_fan : FanInTwo C1 := by
    intro g hg
    change g ∈ pre ++ gj :: post' at hg
    simp only [List.mem_append, List.mem_cons] at hg
    rcases hg with hp | rfl | hq
    · exact hFan g (hpre_post ▸ List.mem_append_left _ hp)
    · cases d <;> simp [gj]
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hq
      obtain ⟨ho, hl⟩ := hFan g0 (hpre_post ▸ List.mem_append_right _ hg0)
      exact ⟨ho, by simpa using hl⟩
  have hC1_eval : ∀ x : Fin 9 → Bool, C1.eval (X x) = F x := by
    intro x
    let a : Bool := (C.wires (X x)).getD k false
    let v : Bool := if d then x j || a else x j && a
    have ha_pre : (run pre (X x)).getD k false = a := by
      have hc : C.wires (X x) = run post (run pre (X x)) := by
        change run C.gates (X x) = run post (run pre (X x))
        rw [← hpre_post, hrun_append]
      rw [show a = (C.wires (X x)).getD k false from rfl, hc]
      rw [hrun_lt post (run pre (X x)) k (by rw [hrun_len, hX_len, hpre_len]; omega)]
    have hpre_agree : ∀ i, i ≠ j.val →
        (run pre (X x)).getD i false = (run pre ((X x).set j.val v)).getD i false := by
      apply hrun_agree_off pre (X x) ((X x).set j.val v) (fun i => i = j.val)
      · simp
      · intro g hg; exact hFan g (hpre_post ▸ List.mem_append_left _ hg)
      · intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hi)]
      · intro g hg i hi
        subst hi
        have hnj := hPreNoJ g hg
        rw [show reads j.val g = false ↔ j.val ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2)
          from hcontains_false _ _]
        intro hmem
        exact hnj (List.mem_of_mem_take hmem)
    have hgj_val : gj.op.eval (gj.inputs.map fun i => (run pre (X x)).getD i false) = v := by
      have hj_val : (run pre (X x)).getD j.val false = x j := by
        rw [hrun_lt pre (X x) j.val (by rw [hX_len]; exact Nat.lt_trans j.isLt (by omega))]
        exact hX_lt x j
      cases d
      · simp only [gj, v, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil,
          hj_val, ha_pre, hEvalAnd, List.all_cons, List.all_nil, id, Bool.and_true]
      · simp only [gj, v, ite_true, List.map_cons, List.map_nil,
          hj_val, ha_pre, hEvalOr, List.any_cons, List.any_nil, id, Bool.or_false]
    have hpost_inv : ∀ (gs : List Gate) (wC w1 : List Bool),
        k + 1 ≤ wC.length → w1.length = wC.length + 1 →
        (∀ i, w1.getD (remap i) false = wC.getD i false) →
        ∀ i, (run (gs.map fun g => ⟨g.op, g.inputs.map remap⟩) w1).getD (remap i) false =
             (run gs wC).getD i false := by
      intro gs
      induction gs with
      | nil => intro wC w1 _ _ hI i; exact hI i
      | cons g gs ih =>
        intro wC w1 hlenC hlen1 hI i
        simp only [List.map_cons]
        change (run (gs.map fun g => ⟨g.op, g.inputs.map remap⟩) (step w1 ⟨g.op, g.inputs.map remap⟩)).getD (remap i) false =
               (run gs (step wC g)).getD i false
        have hgv : g.op.eval ((g.inputs.map remap).map fun z => w1.getD z false) =
                   g.op.eval (g.inputs.map fun z => wC.getD z false) := by
          congr 1; rw [List.map_map]; apply List.map_congr_left; intro z _; exact hI z
        apply ih (step wC g) (step w1 ⟨g.op, g.inputs.map remap⟩)
          (by simp [step]; omega) (by simp [step]; omega)
        intro idx
        rcases Nat.lt_trichotomy idx wC.length with hlt | heq | hgt
        · have hrlt : remap idx < w1.length := by
            simp only [remap]; split_ifs <;> omega
          rw [hgetD_snoc_lt _ _ _ _ hrlt, hgetD_snoc_lt _ _ _ _ hlt]
          exact hI idx
        · subst heq
          have hreq : remap wC.length = w1.length := by
            have hjlt : j.val < 9 := j.isLt
            simp only [remap, show wC.length ≠ j.val by omega, ite_false, hlenC, ite_true, hlen1]
          rw [hreq, hgetD_snoc_eq, hgetD_snoc_eq]
          exact hgv
        · have hrgt : w1.length < remap idx := by
            have hjlt : j.val < 9 := j.isLt
            simp only [remap, show idx ≠ j.val by omega, ite_false, show k + 1 ≤ idx by omega, ite_true]
            omega
          rw [hgetD_snoc_gt _ _ _ _ hrgt, hgetD_snoc_gt _ _ _ _ hgt]
    have hC1_eq : C1.eval (X x) = C.eval ((X x).set j.val v) := by
      change (run (pre ++ gj :: post') (X x)).getD (remap C.output) false =
             (run C.gates ((X x).set j.val v)).getD C.output false
      rw [← hpre_post, hrun_append, hrun_append]
      change (run post' (step (run pre (X x)) gj)).getD (remap C.output) false =
             (run post (run pre ((X x).set j.val v))).getD C.output false
      apply hpost_inv post (run pre ((X x).set j.val v)) (step (run pre (X x)) gj)
      · rw [hrun_len, List.length_set, hX_len, hpre_len]; omega
      · simp only [step, List.length_append, List.length_singleton, hrun_len, List.length_set, hX_len]
      · intro i
        have hlen_pre : (run pre (X x)).length = k + 1 := by rw [hrun_len, hX_len, hpre_len]; omega
        have hlen_preV : (run pre ((X x).set j.val v)).length = k + 1 := by
          rw [hrun_len, List.length_set, hX_len, hpre_len]; omega
        by_cases hij : i = j.val
        · subst hij
          simp only [remap, ite_true, step, hgj_val]
          rw [← hlen_pre, hgetD_snoc_eq]
          rw [hrun_lt pre ((X x).set j.val v) j.val (by rw [List.length_set, hX_len]; exact Nat.lt_trans j.isLt (by omega))]
          simp [List.getD_eq_getElem?_getD, List.getElem?_set_self (show j.val < (X x).length by rw [hX_len]; exact Nat.lt_trans j.isLt (by omega))]
        · by_cases hik : k + 1 ≤ i
          · simp only [remap, hij, ite_false, hik, ite_true, step]
            rw [hgetD_snoc_gt _ _ _ _ (by omega)]
            rw [List.getD_eq_default _ _ (by omega)]
          · simp only [remap, hij, ite_false, hik, ite_false, step]
            rw [hgetD_snoc_lt _ _ _ _ (by omega)]
            exact hpre_agree i hij
    exact hC1_eq.trans (hAll x)
  have hremap_iff : ∀ w : ℕ, w < 10 → w ≠ j.val → ∀ i : ℕ, remap i = w ↔ i = w := by
    intro w hw hne i
    have hjlt : j.val < 9 := j.isLt
    simp only [remap]
    split_ifs <;> omega
  have hreads_remap : ∀ (w : ℕ), w < 10 → w ≠ j.val → ∀ g : Gate,
      reads w ⟨g.op, g.inputs.map remap⟩ = reads w g := by
    intro w hw hne g
    simp only [reads, ← List.map_take]
    apply Bool.eq_iff_iff.mpr
    rw [hcontains_true, hcontains_true, List.mem_map]
    constructor
    · rintro ⟨a, ha, hr⟩
      rwa [← (hremap_iff w hw hne a).mp hr]
    · intro ha
      exact ⟨w, ha, (hremap_iff w hw hne w).mpr rfl⟩
  -- Step B: At least one gate of C effectively reads wire 9
  have hReads9 : ∃ g ∈ C.gates, reads 9 g = true := by
    by_contra hno9
    push Not at hno9
    have hno9_false : ∀ g ∈ C.gates, reads 9 g = false := fun g hg =>
      Bool.eq_false_iff.mpr (hno9 g hg)
    have hout9 : C1.output ≠ 9 := by
      intro ho9
      let x0 : Fin 9 → Bool := fun i => decide (i = 0)
      have h1 := hC1_eval x0
      have h2 : C1.eval (X x0) = true := by
        change (run C1.gates (X x0)).getD C1.output false = true
        rw [ho9, hrun_lt C1.gates (X x0) 9 (by rw [hX_len]; omega), hX_9]
        decide
      have h3 : F x0 = false := by decide
      rw [h2, h3] at h1
      exact Bool.noConfusion h1
    have hC1_no9 : ∀ g ∈ C1.gates, reads 9 g = false := by
      intro g hg
      change g ∈ pre ++ gj :: post' at hg
      simp only [List.mem_append, List.mem_cons] at hg
      rcases hg with hp | rfl | hq
      · exact hno9_false g (hpre_post ▸ List.mem_append_left _ hp)
      · have hjlt : j.val < 9 := j.isLt
        cases d
        · simp only [reads, gj, Bool.false_eq_true, ite_false, hEvalAndF, Bool.cond_false]
          rw [hcontains_false]; simp; omega
        · simp only [reads, gj, ite_true, hEvalOrF, Bool.cond_false]
          rw [hcontains_false]; simp; omega
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hq
        rw [hreads_remap 9 (by omega) (by have := j.isLt; omega) g0]
        exact hno9_false g0 (hpre_post ▸ List.mem_append_right _ hg0)
    let shift9 : ℕ → ℕ := fun i => if 10 ≤ i then i - 1 else i
    let C9 : Circuit := ⟨C1.gates.map fun g => ⟨g.op, g.inputs.map shift9⟩, shift9 C1.output⟩
    have hshift_inv : ∀ (gs : List Gate) (w9 w1 : List Bool),
        9 ≤ w9.length → w1.length = w9.length + 1 →
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ g ∈ gs, reads 9 g = false) →
        (∀ i, i ≠ 9 → w9.getD (shift9 i) false = w1.getD i false) →
        ∀ i, i ≠ 9 → (run (gs.map fun g => ⟨g.op, g.inputs.map shift9⟩) w9).getD (shift9 i) false =
                     (run gs w1).getD i false := by
      intro gs
      induction gs with
      | nil => intro w9 w1 _ _ _ _ hI i hi; exact hI i hi
      | cons g gs ih =>
        intro w9 w1 hlen9 hlen1 hok hnr hI i hi
        simp only [List.map_cons]
        change (run (gs.map fun g => ⟨g.op, g.inputs.map shift9⟩) (step w9 ⟨g.op, g.inputs.map shift9⟩)).getD (shift9 i) false =
               (run gs (step w1 g)).getD i false
        have hgok := hok g List.mem_cons_self
        have hgnr := hnr g List.mem_cons_self
        have hgv : g.op.eval ((g.inputs.map shift9).map fun z => w9.getD z false) =
                   g.op.eval (g.inputs.map fun z => w1.getD z false) := by
          rw [List.map_map]
          rcases hgok.1 with hAnd | hOr | hNot
          · rw [hAnd]; congr 1; apply List.map_congr_left; intro z hz
            apply hI z; intro hz9; subst hz9
            have htk : g.inputs.take 2 = g.inputs := List.take_of_length_le hgok.2
            simp only [reads, hAnd, hEvalAndF, Bool.cond_false, htk] at hgnr
            exact ((hcontains_false _ _).mp hgnr) hz
          · rw [hOr]; congr 1; apply List.map_congr_left; intro z hz
            apply hI z; intro hz9; subst hz9
            have htk : g.inputs.take 2 = g.inputs := List.take_of_length_le hgok.2
            simp only [reads, hOr, hEvalOrF, Bool.cond_false, htk] at hgnr
            exact ((hcontains_false _ _).mp hgnr) hz
          · change g.op = GateOp.not at hNot
            rw [hNot]
            cases hgi : g.inputs with
            | nil => rfl
            | cons a rest =>
              simp only [hEvalNot, List.map_cons, List.headD_cons, Function.comp_apply]
              congr 1; apply hI a; intro ha9; subst ha9
              simp only [reads, hNot, hEvalNotF, Bool.cond_true, hgi, List.take_succ_cons, List.take_zero] at hgnr
              exact ((hcontains_false [9] 9).mp hgnr) List.mem_cons_self
        apply ih (step w9 ⟨g.op, g.inputs.map shift9⟩) (step w1 g)
          (by simp [step]; omega) (by simp [step]; omega)
          (fun h hh => hok h (List.mem_cons_of_mem _ hh))
          (fun h hh => hnr h (List.mem_cons_of_mem _ hh))
        · intro idx hidx
          rcases Nat.lt_trichotomy idx w1.length with hlt | heq | hgt
          · have hslt : shift9 idx < w9.length := by simp only [shift9]; split_ifs <;> omega
            rw [hgetD_snoc_lt _ _ _ _ hslt, hgetD_snoc_lt _ _ _ _ hlt]
            exact hI idx hidx
          · subst heq
            have hseq : shift9 w1.length = w9.length := by simp only [shift9]; split_ifs <;> omega
            rw [hseq, hgetD_snoc_eq, hgetD_snoc_eq]
            exact hgv
          · have hsgt : w9.length < shift9 idx := by simp only [shift9]; split_ifs <;> omega
            rw [hgetD_snoc_gt _ _ _ _ hsgt, hgetD_snoc_gt _ _ _ _ hgt]
        · exact hi
    apply h_full14
    refine ⟨C9, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨ho, hl⟩ := hC1_fan g0 hg0
      exact ⟨ho, by simpa using hl⟩
    · change (C1.gates.map _).length ≤ 14
      rw [List.length_map]
      have : C1.size = C1.gates.length := rfl
      omega
    · intro x
      have heq := hshift_inv C1.gates (List.ofFn x) (X x) (by simp) (by simp [X])
        hC1_fan hC1_no9 (fun idx hidx => by
          by_cases hlt : idx < 9
          · simp only [shift9, show ¬ 10 ≤ idx by omega, ite_false]
            have h1 := hX_lt x ⟨idx, hlt⟩
            rw [h1]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
          · simp only [shift9, show 10 ≤ idx by omega, ite_true]
            rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by rw [hX_len]; omega)])
        C1.output hout9
      exact heq.trans (hC1_eval x)
  -- Step C: Constant-propagating simplifier on Fin 8 for x_6 = false (no match expressions)
  let lift8 : (Fin 8 → Bool) → Fin 9 → Bool :=
    fun y => ![y 1, y 0, y 4, y 7, y 5, y 2, false, y 6, y 3]
  have hlift_minor : ∀ y : Fin 8 → Bool, F (lift8 y) = minor y := by
    intro y
    simp only [F, lift8, minor, List.any_cons, List.any_nil, Bool.or_false]
    generalize y 0 = a0; generalize y 1 = a1; generalize y 2 = a2; generalize y 3 = a3
    generalize y 4 = a4; generalize y 5 = a5; generalize y 6 = a6; generalize y 7 = a7
    revert a0 a1 a2 a3 a4 a5 a6 a7
    decide
  let evalStat : List Bool → Sum Bool ℕ → Bool :=
    fun w s => Sum.elim id (fun i => w.getD i false) s
  let initEnv : List (Sum Bool ℕ) :=
    [Sum.inr 1, Sum.inr 0, Sum.inr 4, Sum.inr 7, Sum.inr 5,
     Sum.inr 2, Sum.inl false, Sum.inr 6, Sum.inr 3, Sum.inr 1]
  have hinit_sound : ∀ (y : Fin 8 → Bool) (i : ℕ),
      evalStat (List.ofFn y) (initEnv.getD i (Sum.inl false)) = (X (lift8 y)).getD i false := by
    intro y i
    by_cases hi : i < 10
    · interval_cases i <;>
        simp [evalStat, initEnv, X, lift8, List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default initEnv _ (by simp [initEnv]; omega),
          List.getD_eq_default (X (lift8 y)) _ (by rw [hX_len]; omega)]
      rfl
  have hinit_bdd : ∀ i w, initEnv.getD i (Sum.inl false) = Sum.inr w → w < 8 := by
    intro i w hw
    by_cases hi : i < 10
    · interval_cases i <;> simp [initEnv, List.getD_eq_getElem?_getD] at hw <;> omega
    · rw [List.getD_eq_default initEnv _ (by simp [initEnv]; omega)] at hw
      cases hw
  let simpAnd2 : ℕ → Sum Bool ℕ → Sum Bool ℕ → Sum Bool ℕ × Option Gate :=
    fun nextW sa sb =>
      Sum.elim
        (fun ba => Bool.casesOn ba (Sum.inl false, none) (sb, none))
        (fun wa => Sum.elim
          (fun bb => Bool.casesOn bb (Sum.inl false, none) (Sum.inr wa, none))
          (fun wb => if wa = wb then (Sum.inr wa, none) else (Sum.inr nextW, some ⟨GateOp.and, [wa, wb]⟩))
          sb)
        sa
  let simpOr2 : ℕ → Sum Bool ℕ → Sum Bool ℕ → Sum Bool ℕ × Option Gate :=
    fun nextW sa sb =>
      Sum.elim
        (fun ba => Bool.casesOn ba (sb, none) (Sum.inl true, none))
        (fun wa => Sum.elim
          (fun bb => Bool.casesOn bb (Sum.inr wa, none) (Sum.inl true, none))
          (fun wb => if wa = wb then (Sum.inr wa, none) else (Sum.inr nextW, some ⟨GateOp.or, [wa, wb]⟩))
          sb)
        sa
  let simpGate : ℕ → List (Sum Bool ℕ) → Gate → Sum Bool ℕ × Option Gate :=
    fun nextW env g =>
      let getS := fun i => env.getD i (Sum.inl false)
      GateOp.casesOn g.op
        -- and
        (List.casesOn g.inputs (Sum.inl true, none) fun a r1 =>
          List.casesOn r1 (getS a, none) fun b r2 =>
            List.casesOn r2 (simpAnd2 nextW (getS a) (getS b)) fun _ _ => (Sum.inl false, none))
        -- or
        (List.casesOn g.inputs (Sum.inl false, none) fun a r1 =>
          List.casesOn r1 (getS a, none) fun b r2 =>
            List.casesOn r2 (simpOr2 nextW (getS a) (getS b)) fun _ _ => (Sum.inl false, none))
        -- not
        (List.casesOn g.inputs (Sum.inl true, none) fun a _ =>
          Sum.elim (fun b => (Sum.inl (!b), none)) (fun w => (Sum.inr nextW, some ⟨GateOp.not, [w]⟩)) (getS a))
        -- mod
        (fun _ => (Sum.inl false, none))
        -- maj
        (Sum.inl false, none)
  let simpStep : List (Sum Bool ℕ) × List Gate → Gate → List (Sum Bool ℕ) × List Gate :=
    fun st g =>
      let res := simpGate (8 + st.2.length) st.1 g
      Option.casesOn res.2 (st.1 ++ [res.1], st.2) (fun g' => (st.1 ++ [res.1], st.2 ++ [g']))
  let simpRun : List Gate → List (Sum Bool ℕ) × List Gate → List (Sum Bool ℕ) × List Gate :=
    fun gs st => gs.foldl simpStep st
  have hsimpGate_bdd : ∀ (nextW : ℕ) (env : List (Sum Bool ℕ)) (g : Gate),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      (∀ i w, env.getD i (Sum.inl false) = Sum.inr w → w < nextW) →
      (∀ w, (simpGate nextW env g).1 = Sum.inr w →
        w < nextW + Option.casesOn (simpGate nextW env g).2 0 (fun _ => 1)) ∧
      (∀ g', (simpGate nextW env g).2 = some g' →
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) := by
    intro nextW env g hop hlen hbdd
    rcases hop with hAnd | hOr | hNot
    · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · dsimp only [simpGate]; rw [hAnd, hgi]; exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
      · dsimp only [simpGate]; rw [hAnd, hgi]; dsimp only
        refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
        have := hbdd a w hw; omega
      · dsimp only [simpGate]; rw [hAnd, hgi]; dsimp only [simpAnd2]
        cases hsa : env.getD a (Sum.inl false) with
        | inl ba =>
          cases ba
          · exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
          · refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
            have := hbdd b w hw; omega
        | inr wa =>
          cases hsb : env.getD b (Sum.inl false) with
          | inl bb =>
            cases bb
            · exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
            · refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
              cases hw; have := hbdd a wa hsa; omega
          | inr wb =>
            dsimp only [Sum.elim]
            by_cases heq : wa = wb
            · subst heq; simp only [ite_true]
              refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
              cases hw; have := hbdd a wa hsa; omega
            · simp only [heq, ite_false]
              refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
              · cases hw; omega
              · cases hg'; exact ⟨Or.inl rfl, by simp⟩
      · simp [hgi] at hlen
    · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · dsimp only [simpGate]; rw [hOr, hgi]; exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
      · dsimp only [simpGate]; rw [hOr, hgi]; dsimp only
        refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
        have := hbdd a w hw; omega
      · dsimp only [simpGate]; rw [hOr, hgi]; dsimp only [simpOr2]
        cases hsa : env.getD a (Sum.inl false) with
        | inl ba =>
          cases ba
          · refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
            have := hbdd b w hw; omega
          · exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
        | inr wa =>
          cases hsb : env.getD b (Sum.inl false) with
          | inl bb =>
            cases bb
            · refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
              cases hw; have := hbdd a wa hsa; omega
            · exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
          | inr wb =>
            dsimp only [Sum.elim]
            by_cases heq : wa = wb
            · subst heq; simp only [ite_true]
              refine ⟨fun w hw => ?_, (fun _ h => by cases h)⟩
              cases hw; have := hbdd a wa hsa; omega
            · simp only [heq, ite_false]
              refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
              · cases hw; omega
              · cases hg'; exact ⟨Or.inr (Or.inl rfl), by simp⟩
      · simp [hgi] at hlen
    · change g.op = GateOp.not at hNot
      cases hgi : g.inputs with
      | nil => dsimp only [simpGate]; rw [hNot, hgi]; exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
      | cons a rest =>
        dsimp only [simpGate]; rw [hNot, hgi]; dsimp only
        cases hsa : env.getD a (Sum.inl false) with
        | inl _ => exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
        | inr _ =>
          refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
          · cases hw; change nextW < nextW + 1; omega
          · cases hg'; exact ⟨Or.inr (Or.inr rfl), by simp⟩
  have hsimpGate_ok : ∀ (nextW : ℕ) (env : List (Sum Bool ℕ)) (g : Gate),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      ∀ (w8 w10 : List Bool), w8.length = nextW →
        (∀ i, evalStat w8 (env.getD i (Sum.inl false)) = w10.getD i false) →
        evalStat (Option.casesOn (simpGate nextW env g).2 w8 (fun g' => step w8 g'))
          (simpGate nextW env g).1 = g.op.eval (g.inputs.map fun i => w10.getD i false) := by
    intro nextW env g hop hlen w8 w10 hlen8 hsound
    rcases hop with hAnd | hOr | hNot
    · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · dsimp only [simpGate]; rw [hAnd, hgi]; rfl
      · dsimp only [simpGate]; rw [hAnd, hgi]; dsimp only
        have ha := hsound a
        simpa [hEvalAnd] using ha
      · dsimp only [simpGate]; rw [hAnd, hgi]; dsimp only [simpAnd2]
        have ha := hsound a
        have hb := hsound b
        cases hsa : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [hsa] at ha
          cases ba
          · dsimp only [Sum.elim, evalStat] at ha ⊢
            simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
            rw [← ha]; rfl
          · dsimp only [Sum.elim, evalStat, id] at ha ⊢
            simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
            rw [← ha, Bool.true_and]; exact hb
        | inr wa =>
          rw [hsa] at ha
          cases hsb : env.getD b (Sum.inl false) with
          | inl bb =>
            rw [hsb] at hb
            cases bb
            · dsimp only [Sum.elim, evalStat] at hb ⊢
              simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
              rw [← hb]; simp
            · dsimp only [Sum.elim, evalStat] at ha hb ⊢
              simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
              rw [← ha, ← hb]; simp
          | inr wb =>
            rw [hsb] at hb
            by_cases heq : wa = wb
            · subst heq
              dsimp only [Sum.elim]
              simp only [ite_true]
              dsimp only [evalStat, Sum.elim] at ha hb ⊢
              simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
              rw [← ha, ← hb]; simp
            · dsimp only [Sum.elim]
              simp only [heq, ite_false]
              dsimp only [evalStat, Sum.elim] at ha hb ⊢
              simp only [step, ← hlen8, hgetD_snoc_eq, hEvalAnd,
                List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
              rw [ha, hb]
      · simp [hgi] at hlen
    · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · dsimp only [simpGate]; rw [hOr, hgi]; rfl
      · dsimp only [simpGate]; rw [hOr, hgi]; dsimp only
        have ha := hsound a
        simpa [hEvalOr] using ha
      · dsimp only [simpGate]; rw [hOr, hgi]; dsimp only [simpOr2]
        have ha := hsound a
        have hb := hsound b
        cases hsa : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [hsa] at ha
          cases ba
          · dsimp only [Sum.elim, evalStat, id] at ha ⊢
            simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
            rw [← ha, Bool.false_or]; exact hb
          · dsimp only [Sum.elim, evalStat] at ha ⊢
            simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
            rw [← ha]; rfl
        | inr wa =>
          rw [hsa] at ha
          cases hsb : env.getD b (Sum.inl false) with
          | inl bb =>
            rw [hsb] at hb
            cases bb
            · dsimp only [Sum.elim, evalStat] at ha hb ⊢
              simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
              rw [← ha, ← hb]; simp
            · dsimp only [Sum.elim, evalStat] at hb ⊢
              simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
              rw [← hb]; simp
          | inr wb =>
            rw [hsb] at hb
            by_cases heq : wa = wb
            · subst heq
              dsimp only [Sum.elim]
              simp only [ite_true]
              dsimp only [evalStat, Sum.elim] at ha hb ⊢
              simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
              rw [← ha, ← hb]; simp
            · dsimp only [Sum.elim]
              simp only [heq, ite_false]
              dsimp only [evalStat, Sum.elim] at ha hb ⊢
              simp only [step, ← hlen8, hgetD_snoc_eq, hEvalOr,
                List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
              rw [ha, hb]
      · simp [hgi] at hlen
    · cases hgi : g.inputs with
      | nil => dsimp only [simpGate]; rw [hNot, hgi]; rfl
      | cons a rest =>
        dsimp only [simpGate]; rw [hNot, hgi]; dsimp only
        have ha := hsound a
        cases hsa : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [hsa] at ha
          dsimp only [Sum.elim, evalStat, id] at ha ⊢
          simp only [hEvalNot, List.map_cons, List.headD_cons, ha]
        | inr wa =>
          rw [hsa] at ha
          dsimp only [Sum.elim, evalStat] at ha ⊢
          simp only [step, ← hlen8, hgetD_snoc_eq, hEvalNot, List.map_cons, List.headD_cons, ha]
  have hsimpGate_const_drop : ∀ (nextW : ℕ) (env : List (Sum Bool ℕ)) (g : Gate) (w : ℕ) (b : Bool),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      reads w g = true → env.getD w (Sum.inl false) = Sum.inl b →
      (simpGate nextW env g).2 = none := by
    intro nextW env g w b hop hlen hread hconst
    rcases hop with hAnd | hOr | hNot
    · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩
      · simp only [reads, hAnd, hEvalAndF, Bool.cond_false, hgi, List.take_nil] at hread
        exact absurd ((hcontains_true [] w).mp hread) (List.not_mem_nil)
      · dsimp only [simpGate]; rw [hAnd, hgi]
      · have hmem : w = a ∨ w = c := by
          simp only [reads, hAnd, hEvalAndF, Bool.cond_false, hgi, List.take_succ_cons, List.take_nil] at hread
          simpa using (hcontains_true [a, c] w).mp hread
        rcases hmem with rfl | rfl
        · dsimp only [simpGate]; rw [hAnd, hgi]; dsimp only [simpAnd2]
          rw [hconst]; cases b <;> rfl
        · dsimp only [simpGate]; rw [hAnd, hgi]; dsimp only [simpAnd2]
          rw [hconst]; cases env.getD a (Sum.inl false) with
          | inl ba => cases ba <;> rfl
          | inr _ => cases b <;> rfl
      · simp [hgi] at hlen
    · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩
      · simp only [reads, hOr, hEvalOrF, Bool.cond_false, hgi, List.take_nil] at hread
        exact absurd ((hcontains_true [] w).mp hread) (List.not_mem_nil)
      · dsimp only [simpGate]; rw [hOr, hgi]
      · have hmem : w = a ∨ w = c := by
          simp only [reads, hOr, hEvalOrF, Bool.cond_false, hgi, List.take_succ_cons, List.take_nil] at hread
          simpa using (hcontains_true [a, c] w).mp hread
        rcases hmem with rfl | rfl
        · dsimp only [simpGate]; rw [hOr, hgi]; dsimp only [simpOr2]
          rw [hconst]; cases b <;> rfl
        · dsimp only [simpGate]; rw [hOr, hgi]; dsimp only [simpOr2]
          rw [hconst]; cases env.getD a (Sum.inl false) with
          | inl ba => cases ba <;> rfl
          | inr _ => cases b <;> rfl
      · simp [hgi] at hlen
    · change g.op = GateOp.not at hNot
      cases hgi : g.inputs with
      | nil =>
        simp only [reads, hNot, hEvalNotF, Bool.cond_true, hgi, List.take_nil] at hread
        exact absurd ((hcontains_true [] w).mp hread) (List.not_mem_nil)
      | cons a rest =>
        have hwa : w = a := by
          simp only [reads, hNot, hEvalNotF, Bool.cond_true, hgi, List.take_succ_cons, List.take_zero] at hread
          simpa using (hcontains_true [a] w).mp hread
        subst hwa
        dsimp only [simpGate]; rw [hNot, hgi]; dsimp only
        rw [hconst]; rfl
  have hsimpRun_append : ∀ (gs1 gs2 : List Gate) (st : List (Sum Bool ℕ) × List Gate),
      simpRun (gs1 ++ gs2) st = simpRun gs2 (simpRun gs1 st) := by
    intro gs1 gs2 st; simp [simpRun, List.foldl_append]
  have hsimpRun_env_len : ∀ (gs : List Gate) (st : List (Sum Bool ℕ) × List Gate),
      (simpRun gs st).1.length = st.1.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro st; simp [simpRun]
    | cons g gs ih =>
      intro st
      change (simpRun gs (simpStep st g)).1.length = st.1.length + (gs.length + 1)
      rw [ih]
      simp only [simpStep]
      cases (simpGate (8 + st.2.length) st.1 g).2 <;> simp <;> omega
  have hsimpRun_env_lt : ∀ (gs : List Gate) (st : List (Sum Bool ℕ) × List Gate) (i : ℕ),
      i < st.1.length → (simpRun gs st).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
    intro gs
    induction gs with
    | nil => intro st i _; rfl
    | cons g gs ih =>
      intro st i hi
      change (simpRun gs (simpStep st g)).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false)
      have hlen : (simpStep st g).1.length = st.1.length + 1 := by
        simp only [simpStep]; cases (simpGate (8 + st.2.length) st.1 g).2 <;> simp
      rw [ih (simpStep st g) i (by omega)]
      simp only [simpStep]
      cases (simpGate (8 + st.2.length) st.1 g).2 <;> exact hgetD_snoc_lt _ _ _ _ hi
  have hsimpRun_drop : ∀ (w : ℕ) (b : Bool) (gs : List Gate) (st : List (Sum Bool ℕ) × List Gate),
      w < st.1.length → st.1.getD w (Sum.inl false) = Sum.inl b →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (simpRun gs st).2.length + (gs.filter (reads w)).length ≤ st.2.length + gs.length := by
    intro w b gs
    induction gs with
    | nil => intro st _ _ _; simp [simpRun]
    | cons g gs ih =>
      intro st hwl hwc hok
      have hgok := hok g List.mem_cons_self
      have hlen1 : (simpStep st g).1.length = st.1.length + 1 := by
        simp only [simpStep]; cases (simpGate (8 + st.2.length) st.1 g).2 <;> simp
      have hwc1 : (simpStep st g).1.getD w (Sum.inl false) = Sum.inl b := by
        simp only [simpStep]
        cases (simpGate (8 + st.2.length) st.1 g).2 <;>
          rw [hgetD_snoc_lt _ _ _ _ hwl, hwc]
      have hih := ih (simpStep st g) (by omega) hwc1 (fun h hh => hok h (List.mem_cons_of_mem _ hh))
      change (simpRun gs (simpStep st g)).2.length + ((g :: gs).filter (reads w)).length ≤
        st.2.length + (g :: gs).length
      simp only [List.filter_cons, List.length_cons]
      cases hrg : reads w g
      · simp only [Bool.false_eq_true, ite_false]
        have hstep_le : (simpStep st g).2.length ≤ st.2.length + 1 := by
          simp only [simpStep]
          cases (simpGate (8 + st.2.length) st.1 g).2 <;> simp
        omega
      · simp only [ite_true, List.length_cons]
        have hnone := hsimpGate_const_drop (8 + st.2.length) st.1 g w b hgok.1 hgok.2 hrg hwc
        have hstep_eq : (simpStep st g).2.length = st.2.length := by
          simp only [simpStep, hnone]
        omega
  have hsimpRun_sound : ∀ (gs : List Gate) (st : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ st.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i w, st.1.getD i (Sum.inl false) = Sum.inr w → w < 8 + st.2.length) →
      (∀ g ∈ (simpRun gs st).2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ (y : Fin 8 → Bool) (w10 : List Bool),
        st.1.length = w10.length →
        (∀ i, evalStat (run st.2 (List.ofFn y)) (st.1.getD i (Sum.inl false)) = w10.getD i false) →
        ∀ i, evalStat (run (simpRun gs st).2 (List.ofFn y)) ((simpRun gs st).1.getD i (Sum.inl false)) =
             (run gs w10).getD i false) := by
    intro gs
    induction gs with
    | nil =>
      intro st _ hst2 _
      exact ⟨hst2, fun y w10 _ hs i => hs i⟩
    | cons g gs ih =>
      intro st hok hst2 hbdd
      have hgok := hok g List.mem_cons_self
      obtain ⟨hgb_w, hgb_g⟩ := hsimpGate_bdd (8 + st.2.length) st.1 g hgok.1 hgok.2 hbdd
      have hst_next_ok : ∀ h ∈ (simpStep st g).2,
          h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2 := by
        intro h hh
        simp only [simpStep] at hh
        cases hopt : (simpGate (8 + st.2.length) st.1 g).2 with
        | none => rw [hopt] at hh; exact hst2 h hh
        | some g' =>
          rw [hopt] at hh
          rcases List.mem_append.mp hh with hh1 | hh2
          · exact hst2 h hh1
          · simp only [List.mem_singleton] at hh2; subst hh2
            exact hgb_g h hopt
      have hst_next_bdd : ∀ i w, (simpStep st g).1.getD i (Sum.inl false) = Sum.inr w →
          w < 8 + (simpStep st g).2.length := by
        intro i w hw
        simp only [simpStep] at hw ⊢
        cases hopt : (simpGate (8 + st.2.length) st.1 g).2 with
        | none =>
          rw [hopt] at hw hgb_w
          rcases Nat.lt_trichotomy i st.1.length with hlt | heq | hgt
          · rw [hgetD_snoc_lt _ _ _ _ hlt] at hw; exact hbdd i w hw
          · subst heq; rw [hgetD_snoc_eq] at hw; have := hgb_w w hw; omega
          · rw [hgetD_snoc_gt _ _ _ _ hgt] at hw; cases hw
        | some g' =>
          rw [hopt] at hw hgb_w
          simp only [List.length_append, List.length_singleton]
          rcases Nat.lt_trichotomy i st.1.length with hlt | heq | hgt
          · rw [hgetD_snoc_lt _ _ _ _ hlt] at hw; have := hbdd i w hw; omega
          · subst heq; rw [hgetD_snoc_eq] at hw; have := hgb_w w hw; omega
          · rw [hgetD_snoc_gt _ _ _ _ hgt] at hw; cases hw
      have hih := ih (simpStep st g) (fun h hh => hok h (List.mem_cons_of_mem _ hh)) hst_next_ok hst_next_bdd
      refine ⟨hih.1, ?_⟩
      intro y w10 hlen hs i
      change evalStat (run (simpRun gs (simpStep st g)).2 (List.ofFn y))
          ((simpRun gs (simpStep st g)).1.getD i (Sum.inl false)) =
          (run gs (step w10 g)).getD i false
      apply hih.2 y (step w10 g)
      · simp only [simpStep, step]
        cases (simpGate (8 + st.2.length) st.1 g).2 <;> simp [hlen]
      · intro idx
        have hstep_ok := hsimpGate_ok (8 + st.2.length) st.1 g hgok.1 hgok.2
          (run st.2 (List.ofFn y)) w10 (by rw [hrun_len]; simp) hs
        simp only [simpStep]
        cases hopt : (simpGate (8 + st.2.length) st.1 g).2 with
        | none =>
          rw [hopt] at hstep_ok
          rcases Nat.lt_trichotomy idx st.1.length with hlt | heq | hgt
          · rw [hgetD_snoc_lt _ _ _ _ hlt, hgetD_snoc_lt _ _ _ _ (by omega)]
            exact hs idx
          · subst heq
            rw [hgetD_snoc_eq, hlen, hgetD_snoc_eq]
            exact hstep_ok
          · rw [hgetD_snoc_gt _ _ _ _ hgt, hgetD_snoc_gt _ _ _ _ (by omega)]; rfl
        | some g' =>
          rw [hopt] at hstep_ok
          have hrapp : run (st.2 ++ [g']) (List.ofFn y) = step (run st.2 (List.ofFn y)) g' := by
            rw [hrun_append]; rfl
          rw [hrapp]
          rcases Nat.lt_trichotomy idx st.1.length with hlt | heq | hgt
          · rw [hgetD_snoc_lt _ _ _ _ hlt, hgetD_snoc_lt _ _ _ _ (by omega)]
            have hprev := hs idx
            cases hsi : st.1.getD idx (Sum.inl false) with
            | inl b => rw [hsi] at hprev; exact hprev
            | inr w =>
              rw [hsi] at hprev
              have hwb : w < (run st.2 (List.ofFn y)).length := by
                rw [hrun_len]; simp only [List.length_ofFn]; exact hbdd idx w hsi
              dsimp only [evalStat, Sum.elim] at hprev ⊢
              rw [hgetD_snoc_lt _ _ _ _ hwb]
              exact hprev
          · subst heq
            rw [hgetD_snoc_eq, hlen, hgetD_snoc_eq]
            exact hstep_ok
          · rw [hgetD_snoc_gt _ _ _ _ hgt, hgetD_snoc_gt _ _ _ _ (by omega)]; rfl
  have hminor_ge13 : ∀ (D : Circuit), FanInTwo D →
      (∀ y : Fin 8 → Bool, D.eval (X (lift8 y)) = minor y) →
      13 ≤ (simpRun D.gates (initEnv, [])).2.length ∧
      ∃ out' : ℕ, (simpRun D.gates (initEnv, [])).1.getD D.output (Sum.inl false) = Sum.inr out' := by
    intro D hDFan hDEval
    obtain ⟨hOutFan, hSound⟩ := hsimpRun_sound D.gates (initEnv, []) hDFan (by simp) hinit_bdd
    have hEv : ∀ y : Fin 8 → Bool,
        evalStat (run (simpRun D.gates (initEnv, [])).2 (List.ofFn y))
          ((simpRun D.gates (initEnv, [])).1.getD D.output (Sum.inl false)) = minor y := by
      intro y
      have h1 := hSound y (X (lift8 y)) (by simp [initEnv, X]) (hinit_sound y) D.output
      exact h1.trans (hDEval y)
    cases hstOut : (simpRun D.gates (initEnv, [])).1.getD D.output (Sum.inl false) with
    | inl b =>
      exfalso
      let y0 : Fin 8 → Bool := fun _ => false
      let y1 : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have e0 := hEv y0
      have e1 := hEv y1
      rw [hstOut] at e0 e1
      have m0 : minor y0 = false := by decide
      have m1 : minor y1 = true := by decide
      dsimp only [evalStat, Sum.elim, id] at e0 e1
      rw [m0] at e0
      rw [m1] at e1
      rw [e0] at e1
      exact Bool.noConfusion e1
    | inr out' =>
      refine ⟨?_, out', rfl⟩
      by_contra hlt
      apply h_minor
      refine ⟨⟨(simpRun D.gates (initEnv, [])).2, out'⟩, hOutFan, ?_, ?_⟩
      · change (simpRun D.gates (initEnv, [])).2.length ≤ 12; omega
      · intro y
        have h1 := hEv y
        rw [hstOut] at h1
        exact h1
  -- Step D: Derive the normalized structural conditions for h_norm
  let xA : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 8)
  let xB : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 6 ∨ i = 8)
  let x6only : Fin 9 → Bool := fun i => decide (i = 6)
  have hFxA : F xA = false := by decide
  have hFxB : F xB = true := by decide
  have hFx6 : F x6only = false := by decide
  have hXAB_agree : ∀ i, i ≠ 6 → (X xA).getD i false = (X xB).getD i false := by
    intro i hi
    by_cases hlt : i < 10
    · interval_cases i <;> first | exact absurd rfl hi | decide
    · rw [List.getD_eq_default (X xA) _ (by rw [hX_len]; omega),
          List.getD_eq_default (X xB) _ (by rw [hX_len]; omega)]
  have hC1_out_ne6 : C1.output ≠ 6 := by
    intro ho6
    have h1 := hC1_eval x6only
    have h2 : C1.eval (X x6only) = true := by
      change (run C1.gates (X x6only)).getD C1.output false = true
      rw [ho6, hrun_lt C1.gates (X x6only) 6 (by rw [hX_len]; omega)]
      have h6 := hX_lt x6only 6
      exact h6.trans (by decide)
    rw [h2, hFx6] at h1
    exact Bool.noConfusion h1
  have hfilter6_eq : (C1.gates.filter (reads 6)).length = (C.gates.filter (reads 6)).length := by
    have hgj6 : reads 6 gj = false := by
      have hjne : j.val ≠ 6 := fun e => hj6 (Fin.ext e)
      cases d
      · simp only [reads, gj, Bool.false_eq_true, ite_false, hEvalAndF, Bool.cond_false]
        rw [hcontains_false]; simp; omega
      · simp only [reads, gj, ite_true, hEvalOrF, Bool.cond_false]
        rw [hcontains_false]; simp; omega
    have hpost6 : (post'.filter (reads 6)).length = (post.filter (reads 6)).length := by
      have hmap : ∀ (l : List Gate),
          ((l.map fun g => ⟨g.op, g.inputs.map remap⟩).filter (reads 6)).length =
          (l.filter (reads 6)).length := by
        intro l
        induction l with
        | nil => rfl
        | cons g gs ih =>
          simp only [List.map_cons, List.filter_cons,
            hreads_remap 6 (by omega) (fun e => hj6 (Fin.ext e.symm)) g]
          cases reads 6 g <;> simp [ih]
      exact hmap post
    change ((pre ++ gj :: post').filter (reads 6)).length = (C.gates.filter (reads 6)).length
    rw [← hpre_post, List.filter_append, List.filter_append, List.filter_cons, hgj6]
    simp only [Bool.false_eq_true, ite_false, List.length_append, hpost6]
  have hreads6_pos : 1 ≤ (C.gates.filter (reads 6)).length := by
    by_contra hzero
    have hlen0 : (C1.gates.filter (reads 6)).length = 0 := by omega
    have hno6 : ∀ g ∈ C1.gates, reads 6 g = false := by
      intro g hg
      cases hr : reads 6 g
      · rfl
      · exfalso
        have hmem : g ∈ C1.gates.filter (reads 6) := List.mem_filter.mpr ⟨hg, hr⟩
        have hpos : 0 < (C1.gates.filter (reads 6)).length := List.length_pos_of_mem hmem
        omega
    have heq := hrun_agree_off C1.gates (X xA) (X xB) (fun i => i = 6) (by simp [X])
      hC1_fan hXAB_agree (fun g hg i hi => hi ▸ hno6 g hg) C1.output hC1_out_ne6
    have h1 := hC1_eval xA
    have h2 := hC1_eval xB
    change (run C1.gates (X xA)).getD C1.output false = F xA at h1
    change (run C1.gates (X xB)).getD C1.output false = F xB at h2
    rw [heq, hFxA] at h1
    rw [hFxB] at h2
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hC1_minor : ∀ y : Fin 8 → Bool, C1.eval (X (lift8 y)) = minor y := by
    intro y; exact (hC1_eval (lift8 y)).trans (hlift_minor y)
  obtain ⟨hC1_ge13, _⟩ := hminor_ge13 C1 hC1_fan hC1_minor
  have hC1_drop := hsimpRun_drop 6 false C1.gates (initEnv, []) (by simp [initEnv]) rfl hC1_fan
  simp only [List.length_nil, Nat.zero_add] at hC1_drop
  have hSize13 : C.size = 13 := by
    have : C1.size = C1.gates.length := rfl
    omega
  have hFilter6_len1 : (C.gates.filter (reads 6)).length = 1 := by
    have : C1.size = C1.gates.length := rfl
    omega
  have hFilter6_C1_len1 : (C1.gates.filter (reads 6)).length = 1 := by omega
  cases hfltC : C.gates.filter (reads 6) with
  | nil => simp [hfltC] at hFilter6_len1
  | cons g6 tailC =>
    have htailC : tailC = [] := by
      have : (g6 :: tailC).length = 1 := hfltC ▸ hFilter6_len1
      cases tailC with
      | nil => rfl
      | cons _ _ => simp at this
    subst htailC
    have hg6_mem : g6 ∈ C.gates := (List.mem_filter.mp (hfltC ▸ List.mem_cons_self)).1
    have hsplit_unique : ∀ (l : List Gate), (l.filter (reads 6)).length = 1 →
        ∃ gs1 g1 gs2, l = gs1 ++ g1 :: gs2 ∧
          reads 6 g1 = true ∧
          (∀ h ∈ gs1, reads 6 h = false) ∧
          (∀ h ∈ gs2, reads 6 h = false) := by
      intro l
      induction l with
      | nil => intro h; simp at h
      | cons a rest ih =>
        intro h
        simp only [List.filter_cons] at h
        cases ha : reads 6 a
        · rw [ha] at h; simp only [Bool.false_eq_true, ite_false] at h
          obtain ⟨gs1, g1, gs2, heq, hg1, h1, h2⟩ := ih h
          exact ⟨a :: gs1, g1, gs2, by simp [heq], hg1,
            fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact ha
              · exact h1 x hx',
            h2⟩
        · rw [ha] at h; simp only [ite_true, List.length_cons] at h
          have hr0 : (rest.filter (reads 6)).length = 0 := by omega
          refine ⟨[], a, rest, rfl, ha, by simp, ?_⟩
          intro x hx
          cases hrx : reads 6 x
          · rfl
          · exfalso
            have hm : x ∈ rest.filter (reads 6) := List.mem_filter.mpr ⟨hx, hrx⟩
            have hp := List.length_pos_of_mem hm
            omega
    obtain ⟨gs1, g6_1, gs2, hC1_split, hg61_r, hgs1_no6, hgs2_no6⟩ :=
      hsplit_unique C1.gates hFilter6_C1_len1
    have hg61_rel : g6_1 = g6 ∨ g6_1 = ⟨g6.op, g6.inputs.map remap⟩ := by
      have hg61_mem : g6_1 ∈ pre ++ gj :: post' := by
        change g6_1 ∈ C1.gates; rw [hC1_split]; simp
      simp only [List.mem_append, List.mem_cons] at hg61_mem
      rcases hg61_mem with hp | rfl | hq
      · have hmemC : g6_1 ∈ C.gates := hpre_post ▸ List.mem_append_left _ hp
        have hmemF : g6_1 ∈ C.gates.filter (reads 6) := List.mem_filter.mpr ⟨hmemC, hg61_r⟩
        rw [hfltC, List.mem_singleton] at hmemF
        exact Or.inl hmemF
      · exfalso
        have hjne : j.val ≠ 6 := fun e => hj6 (Fin.ext e)
        cases d
        · simp only [reads, gj, Bool.false_eq_true, ite_false, hEvalAndF, Bool.cond_false] at hg61_r
          have hm := (hcontains_true _ _).mp hg61_r; simp at hm; omega
        · simp only [reads, gj, ite_true, hEvalOrF, Bool.cond_false] at hg61_r
          have hm := (hcontains_true _ _).mp hg61_r; simp at hm; omega
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hq
        have hr0 : reads 6 g0 = true := by
          rwa [← hreads_remap 6 (by omega) (fun e => hj6 (Fin.ext e.symm)) g0]
        have hmemC : g0 ∈ C.gates := hpre_post ▸ List.mem_append_right _ hg0
        have hmemF : g0 ∈ C.gates.filter (reads 6) := List.mem_filter.mpr ⟨hmemC, hr0⟩
        rw [hfltC, List.mem_singleton] at hmemF
        subst hmemF
        exact Or.inr rfl
    let st1 := simpRun gs1 (initEnv, [])
    let w6 : ℕ := 10 + gs1.length
    have hst1_len : st1.1.length = w6 := by
      have := hsimpRun_env_len gs1 (initEnv, [])
      simpa [st1, w6, initEnv] using this
    have hst1_6 : st1.1.getD 6 (Sum.inl false) = Sum.inl false := by
      exact hsimpRun_env_lt gs1 (initEnv, []) 6 (by simp [initEnv])
    have hg61_fan : g6_1.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g6_1.inputs.length ≤ 2 :=
      hC1_fan g6_1 (hC1_split ▸ by simp)
    have hg61_not_const : ∀ b : Bool, (simpGate (8 + st1.2.length) st1.1 g6_1).1 ≠ Sum.inl b := by
      intro b hconst
      have hnone := hsimpGate_const_drop (8 + st1.2.length) st1.1 g6_1 6 false hg61_fan.1 hg61_fan.2 hg61_r hst1_6
      let st2 := simpStep st1 g6_1
      have hst2_len : st2.1.length = w6 + 1 := by
        simp only [st2, simpStep, hnone, List.length_append, List.length_singleton, hst1_len]
      have hst2_w6 : st2.1.getD w6 (Sum.inl false) = Sum.inl b := by
        simp only [st2, simpStep, hnone, ← hst1_len, hgetD_snoc_eq, hconst]
      have hst2_out_len : st2.2.length = st1.2.length := by
        simp only [st2, simpStep, hnone]
      have hst1_out_le : st1.2.length ≤ gs1.length := by
        have hd := hsimpRun_drop 6 false gs1 (initEnv, []) (by simp [initEnv]) rfl
          (fun h hh => hC1_fan h (hC1_split ▸ List.mem_append_left _ hh))
        simp only [List.length_nil, Nat.zero_add] at hd
        change (simpRun gs1 (initEnv, [])).2.length ≤ gs1.length
        omega
      by_cases hread_w6 : ∃ h ∈ gs2, reads w6 h = true
      · obtain ⟨h0, hh0, hrw6⟩ := hread_w6
        have hflt_pos : 1 ≤ (gs2.filter (reads w6)).length :=
          List.length_pos_of_mem (List.mem_filter.mpr ⟨hh0, hrw6⟩)
        have hdrop2 := hsimpRun_drop w6 b gs2 st2 (by omega) hst2_w6
          (fun h hh => hC1_fan h (hC1_split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
        have htot : simpRun C1.gates (initEnv, []) = simpRun gs2 st2 := by
          rw [hC1_split, hsimpRun_append]
          rfl
        have hlenC1 : gs1.length + 1 + gs2.length = 14 := by
          have := congrArg List.length hC1_split
          simp only [List.length_append, List.length_cons] at this
          have hsz : C1.size = C1.gates.length := rfl
          omega
        rw [htot] at hC1_ge13
        omega
      · push Not at hread_w6
        have hgs2_now6 : ∀ h ∈ gs2, reads w6 h = false := fun h hh =>
          Bool.eq_false_iff.mpr (hread_w6 h hh)
        by_cases hout_w6 : C1.output = w6
        · obtain ⟨_, out', hout'⟩ := hminor_ge13 C1 hC1_fan hC1_minor
          have htot : simpRun C1.gates (initEnv, []) = simpRun gs2 st2 := by
            rw [hC1_split, hsimpRun_append]; rfl
          rw [htot, hout_w6, hsimpRun_env_lt gs2 st2 w6 (by omega), hst2_w6] at hout'
          cases hout'
        · have hpre_AB : ∀ i, i ≠ 6 → (run gs1 (X xA)).getD i false = (run gs1 (X xB)).getD i false :=
            hrun_agree_off gs1 (X xA) (X xB) (fun i => i = 6) (by simp [X])
              (fun h hh => hC1_fan h (hC1_split ▸ List.mem_append_left _ hh))
              hXAB_agree (fun h hh i hi => hi ▸ hgs1_no6 h hh)
          have hstep_AB : ∀ i, ¬ (i = 6 ∨ i = w6) →
              (step (run gs1 (X xA)) g6_1).getD i false = (step (run gs1 (X xB)) g6_1).getD i false := by
            intro i hi
            have hne6 : i ≠ 6 := fun e => hi (Or.inl e)
            have hnew6 : i ≠ w6 := fun e => hi (Or.inr e)
            have hlenA : (run gs1 (X xA)).length = w6 := by rw [hrun_len, hX_len]
            have hlenB : (run gs1 (X xB)).length = w6 := by rw [hrun_len, hX_len]
            rcases Nat.lt_trichotomy i w6 with hlt | heq | hgt
            · rw [hgetD_snoc_lt _ _ _ _ (by omega), hgetD_snoc_lt _ _ _ _ (by omega)]
              exact hpre_AB i hne6
            · exact absurd heq hnew6
            · rw [hgetD_snoc_gt _ _ _ _ (by omega), hgetD_snoc_gt _ _ _ _ (by omega)]
          have hfin_AB : (run gs2 (step (run gs1 (X xA)) g6_1)).getD C1.output false =
                         (run gs2 (step (run gs1 (X xB)) g6_1)).getD C1.output false := by
            apply hrun_agree_off gs2 (step (run gs1 (X xA)) g6_1) (step (run gs1 (X xB)) g6_1)
              (fun i => i = 6 ∨ i = w6)
            · simp [step, hrun_len, X]
            · intro h hh; exact hC1_fan h (hC1_split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
            · exact hstep_AB
            · intro h hh i hi
              rcases hi with rfl | rfl
              · exact hgs2_no6 h hh
              · exact hgs2_now6 h hh
            · intro hbad; rcases hbad with h1 | h2
              · exact hC1_out_ne6 h1
              · exact hout_w6 h2
          have h1 := hC1_eval xA
          have h2 := hC1_eval xB
          change (run C1.gates (X xA)).getD C1.output false = F xA at h1
          change (run C1.gates (X xB)).getD C1.output false = F xB at h2
          rw [hC1_split, hrun_append] at h1 h2
          change (run gs2 (step (run gs1 (X xA)) g6_1)).getD C1.output false = F xA at h1
          change (run gs2 (step (run gs1 (X xB)) g6_1)).getD C1.output false = F xB at h2
          rw [hfin_AB, hFxA] at h1
          rw [hFxB] at h2
          rw [h1] at h2
          exact Bool.noConfusion h2
    have hg61_shape : g6_1.op = GateOp.or ∧ ∃ u1 : ℕ, u1 ≠ 6 ∧ (g6_1.inputs = [6, u1] ∨ g6_1.inputs = [u1, 6]) := by
      rcases hg61_fan.1 with hAnd | hOr | hNot
      · exfalso
        rcases hgi : g6_1.inputs with _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩
        · simp only [reads, hAnd, hEvalAndF, Bool.cond_false, hgi, List.take_nil] at hg61_r
          exact absurd ((hcontains_true [] 6).mp hg61_r) List.not_mem_nil
        · have ha6 : 6 = a := by
            simp only [reads, hAnd, hEvalAndF, Bool.cond_false, hgi, List.take_succ_cons, List.take_nil] at hg61_r
            simpa using (hcontains_true [a] 6).mp hg61_r
          subst ha6
          have hnc := hg61_not_const false
          dsimp only [simpGate] at hnc; rw [hAnd, hgi] at hnc; dsimp only at hnc
          exact hnc hst1_6
        · have hmem : 6 = a ∨ 6 = c := by
            simp only [reads, hAnd, hEvalAndF, Bool.cond_false, hgi, List.take_succ_cons, List.take_nil] at hg61_r
            simpa using (hcontains_true [a, c] 6).mp hg61_r
          have hnc := hg61_not_const false
          dsimp only [simpGate] at hnc; rw [hAnd, hgi] at hnc; dsimp only [simpAnd2] at hnc
          rcases hmem with rfl | rfl
          · rw [hst1_6] at hnc; exact hnc rfl
          · rw [hst1_6] at hnc
            cases h_a : st1.1.getD a (Sum.inl false) with
            | inl ba => rw [h_a] at hnc; cases ba <;> exact hnc rfl
            | inr _ => rw [h_a] at hnc; exact hnc rfl
        · have := hg61_fan.2; simp [hgi] at this
      · refine ⟨hOr, ?_⟩
        rcases hgi : g6_1.inputs with _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩
        · simp only [reads, hOr, hEvalOrF, Bool.cond_false, hgi, List.take_nil] at hg61_r
          exact absurd ((hcontains_true [] 6).mp hg61_r) List.not_mem_nil
        · exfalso
          have ha6 : 6 = a := by
            simp only [reads, hOr, hEvalOrF, Bool.cond_false, hgi, List.take_succ_cons, List.take_nil] at hg61_r
            simpa using (hcontains_true [a] 6).mp hg61_r
          subst ha6
          have hnc := hg61_not_const false
          dsimp only [simpGate] at hnc; rw [hOr, hgi] at hnc; dsimp only at hnc
          exact hnc hst1_6
        · have hmem : 6 = a ∨ 6 = c := by
            simp only [reads, hOr, hEvalOrF, Bool.cond_false, hgi, List.take_succ_cons, List.take_nil] at hg61_r
            simpa using (hcontains_true [a, c] 6).mp hg61_r
          rcases hmem with rfl | rfl
          · refine ⟨c, ?_, Or.inl rfl⟩
            intro hc6; subst hc6
            have hnc := hg61_not_const false
            dsimp only [simpGate] at hnc; rw [hOr, hgi] at hnc; dsimp only [simpOr2] at hnc
            rw [hst1_6] at hnc; exact hnc rfl
          · refine ⟨a, ?_, Or.inr rfl⟩
            intro ha6; subst ha6
            have hnc := hg61_not_const false
            dsimp only [simpGate] at hnc; rw [hOr, hgi] at hnc; dsimp only [simpOr2] at hnc
            rw [hst1_6] at hnc; exact hnc rfl
        · have := hg61_fan.2; simp [hgi] at this
      · exfalso
        change g6_1.op = GateOp.not at hNot
        cases hgi : g6_1.inputs with
        | nil =>
          simp only [reads, hNot, hEvalNotF, Bool.cond_true, hgi, List.take_nil] at hg61_r
          exact absurd ((hcontains_true [] 6).mp hg61_r) List.not_mem_nil
        | cons a rest =>
          have ha6 : 6 = a := by
            simp only [reads, hNot, hEvalNotF, Bool.cond_true, hgi, List.take_succ_cons, List.take_zero] at hg61_r
            simpa using (hcontains_true [a] 6).mp hg61_r
          subst ha6
          have hnc := hg61_not_const true
          dsimp only [simpGate] at hnc; rw [hNot, hgi] at hnc; dsimp only at hnc
          rw [hst1_6] at hnc; exact hnc rfl
    obtain ⟨hg61_or, u1, hu1_ne6, hu1_ins⟩ := hg61_shape
    have hu1_ne09 : u1 ≠ 0 ∧ u1 ≠ 9 := by
      have hbad : u1 = 0 ∨ u1 = 9 → False := by
        intro hu09
        have hpre_AB : ∀ i, i ≠ 6 → (run gs1 (X xA)).getD i false = (run gs1 (X xB)).getD i false :=
          hrun_agree_off gs1 (X xA) (X xB) (fun i => i = 6) (by simp [X])
            (fun h hh => hC1_fan h (hC1_split ▸ List.mem_append_left _ hh))
            hXAB_agree (fun h hh i hi => hi ▸ hgs1_no6 h hh)
        have hu1_true : ∀ x : Fin 9 → Bool, x 0 = true → (run gs1 (X x)).getD u1 false = true := by
          intro x hx0
          rcases hu09 with rfl | rfl
          · rw [hrun_lt gs1 (X x) 0 (by rw [hX_len]; omega)]
            have h0 := hX_lt x 0
            exact h0.trans hx0
          · rw [hrun_lt gs1 (X x) 9 (by rw [hX_len]; omega), hX_9, hx0]; rfl
        have hg61_true : ∀ x : Fin 9 → Bool, x 0 = true →
            g6_1.op.eval (g6_1.inputs.map fun i => (run gs1 (X x)).getD i false) = true := by
          intro x hx0
          have ht := hu1_true x hx0
          rw [hg61_or]
          rcases hu1_ins with hi | hi <;> rw [hi] <;>
            simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
              ht, Bool.or_true, Bool.true_or, Bool.or_false]
        have hstep_AB : ∀ i, i ≠ 6 →
            (step (run gs1 (X xA)) g6_1).getD i false = (step (run gs1 (X xB)) g6_1).getD i false := by
          intro i hi
          have hlenA : (run gs1 (X xA)).length = w6 := by rw [hrun_len, hX_len]
          have hlenB : (run gs1 (X xB)).length = w6 := by rw [hrun_len, hX_len]
          rcases Nat.lt_trichotomy i w6 with hlt | heq | hgt
          · rw [hgetD_snoc_lt _ _ _ _ (by omega), hgetD_snoc_lt _ _ _ _ (by omega)]
            exact hpre_AB i hi
          · subst heq
            rw [← hlenA, hgetD_snoc_eq, hlenA, ← hlenB, hgetD_snoc_eq]
            rw [hg61_true xA (by decide), hg61_true xB (by decide)]
          · rw [hgetD_snoc_gt _ _ _ _ (by omega), hgetD_snoc_gt _ _ _ _ (by omega)]
        have hfin_AB := hrun_agree_off gs2 (step (run gs1 (X xA)) g6_1) (step (run gs1 (X xB)) g6_1)
          (fun i => i = 6) (by simp [step, hrun_len, X])
          (fun h hh => hC1_fan h (hC1_split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
          hstep_AB (fun h hh i hi => hi ▸ hgs2_no6 h hh) C1.output hC1_out_ne6
        have h1 := hC1_eval xA
        have h2 := hC1_eval xB
        change (run C1.gates (X xA)).getD C1.output false = F xA at h1
        change (run C1.gates (X xB)).getD C1.output false = F xB at h2
        rw [hC1_split, hrun_append] at h1 h2
        change (run gs2 (step (run gs1 (X xA)) g6_1)).getD C1.output false = F xA at h1
        change (run gs2 (step (run gs1 (X xB)) g6_1)).getD C1.output false = F xB at h2
        rw [hfin_AB, hFxA] at h1
        rw [hFxB] at h2
        rw [h1] at h2
        exact Bool.noConfusion h2
      exact ⟨fun h => hbad (Or.inl h), fun h => hbad (Or.inr h)⟩
    have hg6_shape : g6.op = GateOp.or ∧
        ∃ u : ℕ, u ∉ ([0, 6, 9] : List ℕ) ∧ (g6.inputs = [6, u] ∨ g6.inputs = [u, 6]) := by
      rcases hg61_rel with heq | hmap
      · subst heq
        refine ⟨hg61_or, u1, ?_, hu1_ins⟩
        simp [hu1_ne6, hu1_ne09.1, hu1_ne09.2]
      · have hg6_or : g6.op = GateOp.or := by
          have := congrArg Gate.op hmap; simpa [hg61_or] using this.symm
        have hgi_map : g6.inputs.map remap = g6_1.inputs := by
          have := congrArg Gate.inputs hmap; exact this.symm
        rcases hgi : g6.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · rw [hgi] at hgi_map; rcases hu1_ins with h | h <;> rw [h] at hgi_map <;> simp at hgi_map
        · rw [hgi] at hgi_map; rcases hu1_ins with h | h <;> rw [h] at hgi_map <;> simp at hgi_map
        · rw [hgi] at hgi_map
          have h0_iff := hremap_iff 0 (by omega) (fun e => hj0 (Fin.ext e.symm))
          have h6_iff := hremap_iff 6 (by omega) (fun e => hj6 (Fin.ext e.symm))
          have h9_iff := hremap_iff 9 (by omega) (by have := j.isLt; omega)
          rcases hu1_ins with h | h
          · rw [h] at hgi_map
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hgi_map
            have ha6 : a = 6 := (h6_iff a).mp hgi_map.1
            subst ha6
            refine ⟨hg6_or, b, ?_, Or.inl rfl⟩
            have hb6 : b ≠ 6 := fun h => hu1_ne6 (hgi_map.2.symm.trans ((h6_iff b).mpr h))
            have hb0 : b ≠ 0 := fun h => hu1_ne09.1 (hgi_map.2.symm.trans ((h0_iff b).mpr h))
            have hb9 : b ≠ 9 := fun h => hu1_ne09.2 (hgi_map.2.symm.trans ((h9_iff b).mpr h))
            simp [hb0, hb6, hb9]
          · rw [h] at hgi_map
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hgi_map
            have hb6 : b = 6 := (h6_iff b).mp hgi_map.2
            subst hb6
            refine ⟨hg6_or, a, ?_, Or.inr rfl⟩
            have ha6 : a ≠ 6 := fun h => hu1_ne6 (hgi_map.1.symm.trans ((h6_iff a).mpr h))
            have ha0 : a ≠ 0 := fun h => hu1_ne09.1 (hgi_map.1.symm.trans ((h0_iff a).mpr h))
            have ha9 : a ≠ 9 := fun h => hu1_ne09.2 (hgi_map.1.symm.trans ((h9_iff a).mpr h))
            simp [ha0, ha6, ha9]
        · have := (hFan g6 hg6_mem).2; simp [hgi] at this
    have hNonConstA : ∃ x : Fin 9 → Bool, x 6 = false ∧ (C.wires (X x)).getD k false = d := by
      by_contra hca
      push Not at hca
      have hca' : ∀ x : Fin 9 → Bool, x 6 = false → (C.wires (X x)).getD k false = !d := by
        intro x hx6
        have hne := hca x hx6
        cases hval : (C.wires (X x)).getD k false <;> cases d <;> simp only [hval] at hne ⊢
        · exact absurd rfl hne
        · rfl
        · rfl
        · exact absurd rfl hne
      have hC_minor : ∀ y : Fin 8 → Bool, C.eval (X (lift8 y)) = minor y := by
        intro y
        have h1 := hAll (lift8 y)
        have h2 := hca' (lift8 y) rfl
        have hmod : (if d = true then lift8 y j || (C.wires (X (lift8 y))).getD k false
                     else lift8 y j && (C.wires (X (lift8 y))).getD k false) = lift8 y j := by
          rw [h2]; cases d <;> simp
        rw [hmod] at h1
        have hset : (X (lift8 y)).set j.val (lift8 y j) = X (lift8 y) := by
          apply List.ext_getElem (by simp)
          intro idx hi1 hi2
          by_cases heq : idx = j.val
          · subst heq
            simp only [List.getElem_set_self]
            have hlt := hX_lt (lift8 y) j
            rw [List.getD_eq_getElem _ _ hi2] at hlt
            exact hlt.symm
          · rw [List.getElem_set_ne (Ne.symm heq)]
        rw [hset] at h1
        exact h1.trans (hlift_minor y)
      obtain ⟨hC_ge13, _⟩ := hminor_ge13 C hFan hC_minor
      have hC_drop := hsimpRun_drop 6 false C.gates (initEnv, []) (by simp [initEnv]) rfl hFan
      simp only [List.length_nil, Nat.zero_add] at hC_drop
      have : C.size = C.gates.length := rfl
      omega
    obtain ⟨xBad, hxBad⟩ := h_norm j C k d hj0 hj6 hFan hSize13 hk10 (by omega)
      hPreNoJ hDom hReads9 ⟨g6, hg6_shape.1, hg6_shape.2, hfltC⟩ hNonConstA
    exact hxBad (hAll xBad)
