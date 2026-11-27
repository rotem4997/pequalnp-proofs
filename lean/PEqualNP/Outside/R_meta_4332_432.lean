import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4332_432
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (15 : ℕ) →
      ∃ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x) ≠
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) ||
         x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) ||
         x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) ||
         x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
         x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
         x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (15 : ℕ) →
      (2 : ℕ) ≤ C.gates.countP (fun g => g.op.eval [Bool.false]) →
      ∃ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x) ≠
        !(x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) ||
          x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) ||
          x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) ||
          x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
          x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
          x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8 := by
  dsimp only
  intro E u' b' hfanE hszE
  by_contra hno
  push Not at hno
  let f10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let fP9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have hf10_P9 : ∀ y : Fin 9 → Bool, f10 (Fin.lastCases false y) = fP9 y := by
    intro y
    dsimp [f10, fP9]
    have hl0 : Fin.lastCases false y (0 : Fin 10) = y 0 := Fin.lastCases_castSucc (0 : Fin 9)
    have hl1 : Fin.lastCases false y (1 : Fin 10) = y 1 := Fin.lastCases_castSucc (1 : Fin 9)
    have hl2 : Fin.lastCases false y (2 : Fin 10) = y 2 := Fin.lastCases_castSucc (2 : Fin 9)
    have hl3 : Fin.lastCases false y (3 : Fin 10) = y 3 := Fin.lastCases_castSucc (3 : Fin 9)
    have hl4 : Fin.lastCases false y (4 : Fin 10) = y 4 := Fin.lastCases_castSucc (4 : Fin 9)
    have hl5 : Fin.lastCases false y (5 : Fin 10) = y 5 := Fin.lastCases_castSucc (5 : Fin 9)
    have hl6 : Fin.lastCases false y (6 : Fin 10) = y 6 := Fin.lastCases_castSucc (6 : Fin 9)
    have hl7 : Fin.lastCases false y (7 : Fin 10) = y 7 := Fin.lastCases_castSucc (7 : Fin 9)
    have hl8 : Fin.lastCases false y (8 : Fin 10) = y 8 := Fin.lastCases_castSucc (8 : Fin 9)
    have hl9 : Fin.lastCases false y (9 : Fin 10) = false := Fin.lastCases_last
    rw [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9]
    simp only [Bool.and_false, Bool.false_and, Bool.or_false]
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have hrun_cons : ∀ (g : Gate) (gs : List Gate) (w : List Bool), run (g :: gs) w = run gs (step w g) :=
    fun _ _ _ => rfl
  have hrun_append : ∀ (gs hs : List Gate) (w : List Bool), run (gs ++ hs) w = run hs (run gs w) := by
    intro gs hs w
    simp [run, List.foldl_append]
  have hrun_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      rw [hrun_cons, ih]
      simp [step]
      omega
  have hstep_len : ∀ (w : List Bool) (g : Gate), (step w g).length = w.length + 1 := by
    intro w g
    simp [step]
  have hgetD_append_len : ∀ {α : Type} (xs ys : List α) (d : α), (xs ++ ys).getD xs.length d = ys.getD 0 d := by
    intro α xs ys d
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  let remap : ℕ → ℕ := fun i => if i < 9 then i else if i = 9 then 100 else i - 1
  let mapG : Gate → Gate := fun g => ⟨g.op, g.inputs.map remap⟩
  let C : Circuit := ⟨E.gates.map mapG, remap u'⟩
  have hfanC : FanInTwo C := by
    intro g hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    have hf := hfanE g0 hg0
    exact ⟨hf.1, by simpa [mapG] using hf.2⟩
  have hszC : C.size ≤ 15 := by
    change (E.gates.map mapG).length ≤ 15
    rw [List.length_map]
    exact hszE
  have hremap_run : ∀ (gs : List Gate) (u v : List Bool),
      v.length = u.length + 1 → 9 ≤ u.length → u.length + gs.length < 100 →
      (∀ i, u.getD (remap i) false = v.getD i false) →
      ∀ i, (run (gs.map mapG) u).getD (remap i) false = (run gs v).getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro u v _ _ _ hmap i
      exact hmap i
    | cons g gs ih =>
      intro u v huv hu9 hlt hmap i
      rw [List.map_cons, hrun_cons, hrun_cons]
      apply ih (step u (mapG g)) (step v g)
      · rw [hstep_len, hstep_len, huv]
      · rw [hstep_len]; omega
      · rw [hstep_len]; simp only [List.length_cons] at hlt; omega
      · intro k
        by_cases hk9 : k = 9
        · subst hk9
          have hrm9 : remap 9 = 100 := rfl
          have hlhs : (step u (mapG g)).getD (remap 9) false = false := by
            rw [hrm9]
            exact List.getD_eq_default (step u (mapG g)) false (by rw [hstep_len]; simp only [List.length_cons] at hlt; omega)
          have hrhs : (step v g).getD 9 false = false := by
            have hv9 : 9 < v.length := by omega
            rw [List.getD_append _ _ _ _ hv9, ← hmap 9, hrm9]
            exact List.getD_eq_default u false (by omega)
          exact hlhs.trans hrhs.symm
        · by_cases hkv : k = v.length
          · subst hkv
            have hv10 : 10 ≤ v.length := by omega
            have hrmv : remap v.length = u.length := by
              dsimp [remap]
              split_ifs <;> omega
            rw [hrmv, hgetD_append_len u _, hgetD_append_len v _]
            change (mapG g).op.eval ((mapG g).inputs.map fun j => u.getD j false) =
              g.op.eval (g.inputs.map fun j => v.getD j false)
            dsimp [mapG]
            rw [List.map_map]
            apply congrArg g.op.eval
            apply List.map_congr_left
            intro j _
            exact hmap j
          · by_cases hklt : k < v.length
            · have hrm_lt : remap k < u.length := by
                dsimp [remap]
                split_ifs <;> omega
              rw [List.getD_append _ _ _ _ hrm_lt, List.getD_append _ _ _ _ hklt]
              exact hmap k
            · have hkgt : v.length < k := by omega
              have hk10 : 10 ≤ k := by omega
              have hrm_ge : (step u (mapG g)).length ≤ remap k := by
                rw [hstep_len]
                dsimp [remap]
                split_ifs <;> omega
              have hv_ge : (step v g).length ≤ k := by
                rw [hstep_len]; omega
              rw [List.getD_eq_default (step u (mapG g)) false hrm_ge, List.getD_eq_default (step v g) false hv_ge]
  have hC_eval : ∀ y : Fin 9 → Bool,
      C.eval (List.ofFn y) = (E.wires (List.ofFn (Fin.lastCases false y))).getD u' false := by
    intro y
    change (run C.gates (List.ofFn y)).getD (remap u') false =
      (run E.gates (List.ofFn (Fin.lastCases false y))).getD u' false
    apply hremap_run E.gates (List.ofFn y) (List.ofFn (Fin.lastCases false y))
    · rw [List.length_ofFn, List.length_ofFn]
    · rw [List.length_ofFn]
    · rw [List.length_ofFn]; change 9 + E.size < 100; omega
    · intro i
      by_cases hi9 : i < 9
      · have hrm : remap i = i := by simp [remap, hi9]
        have hi10 : i < 10 := by omega
        have hlu : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact hi9
        have hlv : i < (List.ofFn (Fin.lastCases false y)).length := by rw [List.length_ofFn]; exact hi10
        rw [hrm, List.getD_eq_getElem _ _ hlu, List.getElem_ofFn, List.getD_eq_getElem _ _ hlv, List.getElem_ofFn]
        have hcast : (⟨i, hi10⟩ : Fin 10) = (⟨i, hi9⟩ : Fin 9).castSucc := Fin.ext rfl
        rw [hcast, Fin.lastCases_castSucc]
      · by_cases heq9 : i = 9
        · subst heq9
          have hrm : remap 9 = 100 := rfl
          have hlv : 9 < (List.ofFn (Fin.lastCases false y)).length := by rw [List.length_ofFn]; decide
          rw [hrm, List.getD_eq_default (List.ofFn y) false (by rw [List.length_ofFn]; omega),
            List.getD_eq_getElem _ _ hlv, List.getElem_ofFn]
          have h9eq : (⟨9, by decide⟩ : Fin 10) = Fin.last 9 := rfl
          rw [h9eq, Fin.lastCases_last]
        · have hi10 : 10 ≤ i := by omega
          have hrm : remap i = i - 1 := by simp [remap, hi9, heq9]
          rw [hrm, List.getD_eq_default (List.ofFn y) false (by rw [List.length_ofFn]; omega),
            List.getD_eq_default (List.ofFn (Fin.lastCases false y)) false (by rw [List.length_ofFn]; omega)]
  have hC_comp : ∀ y : Fin 9 → Bool,
      (if b' = true then !(C.eval (List.ofFn y)) else C.eval (List.ofFn y)) = fP9 y := by
    intro y
    have h1y := hno (Fin.lastCases false y) (by exact Fin.lastCases_last)
    change _ = f10 (Fin.lastCases false y) at h1y
    rw [hf10_P9 y] at h1y
    rw [hC_eval y]
    exact h1y
  cases hb : b' with
  | false =>
    obtain ⟨y, hy⟩ := h1 C hfanC hszC
    have hCy := hC_comp y
    rw [hb] at hCy
    exact hy hCy
  | true =>
    have hneg : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = !(fP9 y) := by
      intro y
      have hCy := hC_comp y
      rw [hb] at hCy
      cases hcv : C.eval (List.ofFn y) <;> cases hfv : fP9 y <;> simp_all
    let isNot : Gate → Bool := fun g => g.op.eval [Bool.false]
    by_cases hnot2 : 2 ≤ C.gates.countP isNot
    · obtain ⟨y, hy⟩ := h2 C hfanC hszC hnot2
      exact hy (hneg y)
    · have hnot_lt2 : C.gates.countP isNot < 2 := by omega
      let leList : List Bool → List Bool → Prop := fun u v =>
        u.length = v.length ∧ ∀ i, u.getD i false = true → v.getD i false = true
      have hop_ao : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          isNot g = false → g.op = GateOp.and ∨ g.op = GateOp.or := by
        intro g hop hnf
        rcases hop with ha | ho | hn
        · exact Or.inl ha
        · exact Or.inr ho
        · exfalso
          have ht : isNot g = true := by dsimp [isNot]; rw [hn]; rfl
          rw [ht] at hnf
          cases hnf
      have hgate_mono : ∀ (g : Gate), (g.op = GateOp.and ∨ g.op = GateOp.or) →
          ∀ u v : List Bool, leList u v → leList (step u g) (step v g) := by
        intro g hop u v huv
        refine ⟨by simp [step, huv.1], ?_⟩
        intro i hi
        by_cases hiu : i < u.length
        · rw [List.getD_append _ _ _ _ hiu] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact huv.2 i hi
        · by_cases hieq : i = u.length
          · subst hieq
            rw [hgetD_append_len u _] at hi
            rw [huv.1, hgetD_append_len v _]
            simp only [List.getD_cons_zero] at hi ⊢
            rcases hop with hand | hor
            · rw [hand] at hi ⊢
              change (List.map (fun j => u.getD j false) g.inputs).all id = true at hi
              change (List.map (fun j => v.getD j false) g.inputs).all id = true
              simp only [List.all_eq_true, List.mem_map, id_eq] at hi ⊢
              intro b hbmem
              rcases hbmem with ⟨j, hj, rfl⟩
              exact huv.2 j (hi (u.getD j false) ⟨j, hj, rfl⟩)
            · rw [hor] at hi ⊢
              change (List.map (fun j => u.getD j false) g.inputs).any id = true at hi
              change (List.map (fun j => v.getD j false) g.inputs).any id = true
              simp only [List.any_eq_true, List.mem_map, id_eq] at hi ⊢
              rcases hi with ⟨b, hbmem, hbt⟩
              rcases hbmem with ⟨j, hj, rfl⟩
              exact ⟨v.getD j false, ⟨j, hj, rfl⟩, huv.2 j hbt⟩
          · rw [List.getD_eq_default (step u g) false (by rw [hstep_len]; omega)] at hi
            cases hi
      have hrun_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
          ∀ u v : List Bool, leList u v → leList (run gs u) (run gs v) := by
        intro gs
        induction gs with
        | nil => intro _ u v huv; exact huv
        | cons g gs ih =>
          intro hgs u v huv
          rw [hrun_cons, hrun_cons]
          exact ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (step u g) (step v g)
            (hgate_mono g (hgs g List.mem_cons_self) u v huv)
      have hofFn_mono : ∀ x y : Fin 9 → Bool, (∀ i : Fin 9, x i = true → y i = true) →
          leList (List.ofFn x) (List.ofFn y) := by
        intro x y hxy
        refine ⟨by rw [List.length_ofFn, List.length_ofFn], ?_⟩
        intro i hi
        by_cases hi9 : i < 9
        · have hx9 : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hi9
          have hy9 : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact hi9
          rw [List.getD_eq_getElem _ _ hx9, List.getElem_ofFn] at hi
          rw [List.getD_eq_getElem _ _ hy9, List.getElem_ofFn]
          exact hxy ⟨i, hi9⟩ hi
        · rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)] at hi
          cases hi
      let x0 : Fin 9 → Bool := fun _ => false
      let x1 : Fin 9 → Bool := fun _ => true
      have hfP9_0 : fP9 x0 = false := by decide
      have hfP9_1 : fP9 x1 = true := by decide
      by_cases hzero : C.gates.countP isNot = 0
      · have hnone : ∀ g ∈ C.gates, isNot g = false := fun g hg =>
          Bool.eq_false_iff.mpr (List.countP_eq_zero.mp hzero g hg)
        have hao : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg =>
          hop_ao g (hfanC g hg).1 (hnone g hg)
        have hm01 := hrun_mono C.gates hao (List.ofFn x0) (List.ofFn x1)
          (hofFn_mono x0 x1 (fun i hi => by cases hi))
        have h0t : C.eval (List.ofFn x0) = true := by
          rw [hneg x0, hfP9_0]; rfl
        have h1f : C.eval (List.ofFn x1) = false := by
          rw [hneg x1, hfP9_1]; rfl
        have h1t := hm01.2 C.output h0t
        change C.eval (List.ofFn x1) = true at h1t
        rw [h1f] at h1t
        cases h1t
      · have hone : C.gates.countP isNot = 1 := by omega
        have hsplit_one : ∀ gs : List Gate, gs.countP isNot = 1 →
            ∃ pre gk post, gs = pre ++ gk :: post ∧ isNot gk = true ∧
              (∀ a ∈ pre, isNot a = false) ∧ (∀ a ∈ post, isNot a = false) := by
          intro gs
          induction gs with
          | nil => intro h; simp at h
          | cons g tl ih =>
            intro h
            simp only [List.countP_cons] at h
            cases hpg : isNot g with
            | false =>
              rw [hpg] at h
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨pre, gk, post, htl, hgk, hpre, hpost⟩ := ih h
              refine ⟨g :: pre, gk, post, by rw [htl]; rfl, hgk, ?_, hpost⟩
              intro a ha
              rcases List.mem_cons.mp ha with rfl | hat
              · exact hpg
              · exact hpre a hat
            | true =>
              rw [hpg] at h
              simp only [↓reduceIte] at h
              have htl0 : tl.countP isNot = 0 := by omega
              refine ⟨[], g, tl, rfl, hpg, (fun _ hmem => by cases hmem), ?_⟩
              exact fun a ha => Bool.eq_false_iff.mpr (List.countP_eq_zero.mp htl0 a ha)
        obtain ⟨pre, gk, post, hgs_eq, hgk_isNot, hpre_no, hpost_no⟩ := hsplit_one C.gates hone
        have hgk_inC : gk ∈ C.gates := by
          rw [hgs_eq]; exact List.mem_append_right _ List.mem_cons_self
        have hgk_op : gk.op = GateOp.not := by
          rcases (hfanC gk hgk_inC).1 with ha | ho | hn
          · exfalso; dsimp [isNot] at hgk_isNot; rw [ha] at hgk_isNot; cases hgk_isNot
          · exfalso; dsimp [isNot] at hgk_isNot; rw [ho] at hgk_isNot; cases hgk_isNot
          · exact hn
        have hpre_ao : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
          intro g hg
          have hgC : g ∈ C.gates := by rw [hgs_eq]; exact List.mem_append_left _ hg
          exact hop_ao g (hfanC g hgC).1 (hpre_no g hg)
        have hpost_ao : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
          intro g hg
          have hgC : g ∈ C.gates := by rw [hgs_eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
          exact hop_ao g (hfanC g hgC).1 (hpost_no g hg)
        let wPre : (Fin 9 → Bool) → List Bool := fun x => run pre (List.ofFn x)
        let outA : ℕ := gk.inputs.headD (9 + pre.length)
        let CA : Circuit := ⟨pre, outA⟩
        let A : (Fin 9 → Bool) → Bool := fun x => CA.eval (List.ofFn x)
        let H : (Fin 9 → Bool) → Bool → Bool := fun x z => (run post (wPre x ++ [z])).getD C.output false
        have hwPre_len : ∀ x, (wPre x).length = 9 + pre.length := by
          intro x; dsimp [wPre]; rw [hrun_len, List.length_ofFn]
        have hgk_eval : ∀ x : Fin 9 → Bool,
            gk.op.eval (gk.inputs.map fun i => (wPre x).getD i false) = !(A x) := by
          intro x
          rw [hgk_op]
          cases hgi : gk.inputs with
          | nil =>
            have hdef : (wPre x).getD outA false = false := by
              dsimp [outA]
              rw [hgi]
              exact List.getD_eq_default (wPre x) false (by rw [hwPre_len, List.headD_nil])
            change GateOp.not.eval (List.map (fun i => (wPre x).getD i false) []) = !((wPre x).getD outA false)
            rw [hdef]
            rfl
          | cons a t =>
            dsimp [A, CA, Circuit.eval, Circuit.wires, outA]
            rw [hgi]
            rfl
        have hC_eq_H : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = H x (!(A x)) := by
          intro x
          change (run C.gates (List.ofFn x)).getD C.output false = (run post (wPre x ++ [!(A x)])).getD C.output false
          rw [hgs_eq, hrun_append, hrun_cons]
          change (run post (step (wPre x) gk)).getD C.output false = _
          dsimp [step]
          rw [hgk_eval x]
        have hwPre_mono : ∀ x y : Fin 9 → Bool, (∀ i : Fin 9, x i = true → y i = true) →
            leList (wPre x) (wPre y) := fun x y hxy =>
          hrun_mono pre hpre_ao (List.ofFn x) (List.ofFn y) (hofFn_mono x y hxy)
        have hH_mono : ∀ (x y : Fin 9 → Bool) (z w : Bool),
            (∀ i : Fin 9, x i = true → y i = true) → (z = true → w = true) →
            H x z = true → H y w = true := by
          intro x y z w hxy hzw hxz
          have hpre_xy := hwPre_mono x y hxy
          have happ : leList (wPre x ++ [z]) (wPre y ++ [w]) := by
            refine ⟨by simp [hpre_xy.1], ?_⟩
            intro i hi
            by_cases hip : i < (wPre x).length
            · rw [List.getD_append _ _ _ _ hip] at hi
              rw [List.getD_append _ _ _ _ (by omega)]
              exact hpre_xy.2 i hi
            · by_cases hieq : i = (wPre x).length
              · subst hieq
                rw [hgetD_append_len (wPre x) _] at hi
                rw [hpre_xy.1, hgetD_append_len (wPre y) _]
                exact hzw hi
              · rw [List.getD_eq_default (wPre x ++ [z]) false (by simp; omega)] at hi
                cases hi
          exact (hrun_mono post hpost_ao _ _ happ).2 C.output hxz
        have hH0f : H x0 false = false := by
          by_contra hf
          have ht : H x0 false = true := by cases h : H x0 false <;> simp_all
          have h1t : H x1 (!(A x1)) = true :=
            hH_mono x0 x1 false (!(A x1)) (fun _ h => by cases h) (fun h => by cases h) ht
          rw [← hC_eq_H x1, hneg x1, hfP9_1] at h1t
          cases h1t
        have hA0_and_H0t : A x0 = false ∧ H x0 true = true := by
          have hc0 := hneg x0
          rw [hfP9_0, hC_eq_H x0] at hc0
          cases ha0 : A x0 with
          | true =>
            rw [ha0] at hc0
            change H x0 false = true at hc0
            rw [hH0f] at hc0
            cases hc0
          | false =>
            rw [ha0] at hc0
            exact ⟨rfl, hc0⟩
        have hHt : ∀ x : Fin 9 → Bool, H x true = true := fun x =>
          hH_mono x0 x true true (fun _ h => by cases h) (fun h => h) hA0_and_H0t.2
        have hH1f : H x1 false = false := by
          have hc1 := hneg x1
          rw [hfP9_1, hC_eq_H x1] at hc1
          cases ha1 : A x1 with
          | false =>
            rw [ha1] at hc1
            change H x1 true = false at hc1
            rw [hHt x1] at hc1
            cases hc1
          | true =>
            rw [ha1] at hc1
            exact hc1
        have hHf : ∀ x : Fin 9 → Bool, H x false = false := by
          intro x
          by_contra hf
          have hxt : H x false = true := by cases h : H x false <;> simp_all
          have h1t : H x1 false = true :=
            hH_mono x x1 false false (fun _ _ => rfl) (fun h => h) hxt
          rw [hH1f] at h1t
          cases h1t
        have hHz : ∀ (x : Fin 9 → Bool) (z : Bool), H x z = z := by
          intro x z
          cases z with
          | false => exact hHf x
          | true => exact hHt x
        have hA_eq : ∀ x : Fin 9 → Bool, CA.eval (List.ofFn x) = fP9 x := by
          intro x
          have hcx := hneg x
          rw [hC_eq_H x, hHz x (!(A x))] at hcx
          cases ha : A x <;> cases hfx : fP9 x <;> simp_all [A]
        have hfanCA : FanInTwo CA := by
          intro g hg
          exact hfanC g (by rw [hgs_eq]; exact List.mem_append_left _ hg)
        have hszCA : CA.size ≤ 15 := by
          change pre.length ≤ 15
          have hlen_sum : C.gates.length = pre.length + 1 + post.length := by
            rw [hgs_eq, List.length_append, List.length_cons]
            omega
          have hCs : C.gates.length ≤ 15 := hszC
          omega
        obtain ⟨y, hy⟩ := h1 CA hfanCA hszCA
        exact hy (hA_eq y)
