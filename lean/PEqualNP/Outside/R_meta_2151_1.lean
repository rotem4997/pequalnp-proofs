import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2151_1
    (hTheta : ¬ HasCircuitSize 7
      (fun y : Fin 7 → Bool =>
        (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 4) || (y 1 && y 5) ||
        (y 2 && y 6) || (y 3 && y 5) || (y 4 && y 6) || (y 6 && y 3)) 10)
    (hFourteen : ¬ HasCircuitSize 9
      (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14)
    (hDisjoint : ∀ (a b : Fin 9) (R : Circuit),
      a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
      FanInTwo R → R.size ≤ 13 →
      (∀ x : Fin 9 → Bool,
        R.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → False)
    (hSpecial : ∀ (R : Circuit),
      let f : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      FanInTwo R → R.size ≤ 13 →
      ((∀ x : Fin 9 → Bool, R.eval (List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]) = f x) ∨
       (∀ x : Fin 9 → Bool, R.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = f x) ∨
       (∀ x : Fin 9 → Bool, R.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 5]) = f x) ∨
       (∃ v : Fin 9, v ≠ 0 ∧ v ≠ 4 ∧
         ∀ x : Fin 9 → Bool, R.eval (List.ofFn x ++ [false, x 0 || x 4 || x v]) = f x)) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  classical
  let f : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let theta : (Fin 7 → Bool) → Bool := fun y =>
    (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 4) || (y 1 && y 5) ||
    (y 2 && y 6) || (y 3 && y 5) || (y 4 && y 6) || (y 6 && y 3)
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih]
      · simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
  have atEnd : ∀ (w : List Bool) (b : Bool), (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl w.length),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  let normG (g : Gate) : Gate :=
    if g.op = .not then ⟨.not, g.inputs.take 1⟩ else g
  have normG_step : ∀ (w : List Bool) (g : Gate), step w (normG g) = step w g := by
    intro w g
    obtain ⟨op, ins⟩ := g
    cases op with
    | not =>
      simp only [normG, ite_true]
      cases ins with
      | nil => rfl
      | cons a l => rfl
    | and => simp [normG]
    | or => simp [normG]
    | mod m => simp [normG]
    | maj => simp [normG]
  have normG_foldl : ∀ (gs : List Gate) (w : List Bool),
      (gs.map normG).foldl step w = gs.foldl step w := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      simp only [List.map_cons, List.foldl_cons, normG_step, ih]
  let live (n : ℕ) (gs : List Gate) (o : ℕ) : Finset ℕ :=
    (gs.zipIdx n).foldr (fun p S => if p.2 ∈ S then (S.erase p.2) ∪ p.1.inputs.toFinset else S) {o}
  have live_nil : ∀ (n o : ℕ), live n [] o = {o} := fun _ _ => rfl
  have live_cons : ∀ (n : ℕ) (g : Gate) (gs : List Gate) (o : ℕ),
      live n (g :: gs) o =
        if n ∈ live (n + 1) gs o then (live (n + 1) gs o).erase n ∪ g.inputs.toFinset
        else live (n + 1) gs o := by
    intro n g gs o
    simp only [live, List.zipIdx_cons, List.foldr_cons]
  have agree_eval : ∀ (gs : List Gate) (w₁ w₂ : List Bool) (o : ℕ),
      w₁.length = w₂.length →
      (∀ i ∈ live w₁.length gs o, w₁.getD i false = w₂.getD i false) →
      (gs.foldl step w₁).getD o false = (gs.foldl step w₂).getD o false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁ w₂ o _ h
      exact h o (by rw [live_nil]; simp)
    | cons g gs ih =>
      intro w₁ w₂ o hlen h
      rw [List.foldl_cons, List.foldl_cons]
      have hlen' : (step w₁ g).length = (step w₂ g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
      apply ih (step w₁ g) (step w₂ g) o hlen'
      intro i hi
      have hl1 : (step w₁ g).length = w₁.length + 1 := by simp [step]
      rw [hl1] at hi
      by_cases hlive : w₁.length ∈ live (w₁.length + 1) gs o
      · have hsub : ∀ j ∈ g.inputs, w₁.getD j false = w₂.getD j false := by
          intro j hj
          apply h j
          rw [live_cons, if_pos hlive]
          exact Finset.mem_union_right _ (List.mem_toFinset.mpr hj)
        have hmap : g.inputs.map (fun j => w₁.getD j false) = g.inputs.map (fun j => w₂.getD j false) :=
          List.map_congr_left hsub
        by_cases hiw : i = w₁.length
        · subst hiw
          have h1 := atEnd w₁ (g.op.eval (g.inputs.map fun j => w₁.getD j false))
          have h2 := atEnd w₂ (g.op.eval (g.inputs.map fun j => w₂.getD j false))
          rw [← hlen] at h2
          simp only [step]
          rw [h1, h2, hmap]
        · have him : i ∈ live w₁.length (g :: gs) o := by
            rw [live_cons, if_pos hlive]
            exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiw, hi⟩)
          have hwi := h i him
          by_cases hilt : i < w₁.length
          · have hilt2 : i < w₂.length := hlen ▸ hilt
            simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hilt,
              List.getElem?_append_left hilt2] at hwi ⊢
            exact hwi
          · have hge1 : (step w₁ g).length ≤ i := by
              simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            have hge2 : (step w₂ g).length ≤ i := by rw [← hlen']; exact hge1
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
              List.getElem?_eq_none hge2]
      · have hiw : i ≠ w₁.length := fun heq => hlive (heq ▸ hi)
        have him : i ∈ live w₁.length (g :: gs) o := by
          rw [live_cons, if_neg hlive]; exact hi
        have hwi := h i him
        by_cases hilt : i < w₁.length
        · have hilt2 : i < w₂.length := hlen ▸ hilt
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hilt,
            List.getElem?_append_left hilt2] at hwi ⊢
          exact hwi
        · have hge1 : (step w₁ g).length ≤ i := by
            simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          have hge2 : (step w₂ g).length ≤ i := by rw [← hlen']; exact hge1
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
            List.getElem?_eq_none hge2]
  let valA (n : ℕ) (A : ℕ → Option Bool) (i : ℕ) : Option Bool :=
    if i < n then A i else some false
  let cCount (n : ℕ) (A : ℕ → Option Bool) (S : Finset ℕ) : ℕ :=
    (S.filter (fun i => i < n ∧ (A i).isSome)).card
  let AgreeOn (S : Finset ℕ) (n : ℕ) (A : ℕ → Option Bool) (ρ : ℕ → ℕ) (w u : List Bool) : Prop :=
    ∀ i ∈ S, Option.elim (valA n A i) (w.getD i false = u.getD (ρ i) false) (fun b => w.getD i false = b)
  have elim_consts : ∀ (gs : List Gate) (n m o : ℕ) (A : ℕ → Option Bool) (ρ : ℕ → ℕ),
      (∀ i < n, A i = none → ρ i < m) →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      (∃ b : Bool, ∀ w u : List Bool, w.length = n → u.length = m →
        AgreeOn (live n gs o) n A ρ w u → (gs.foldl step w).getD o false = b) ∨
      (∃ D : Circuit, FanInTwo D ∧ D.size + cCount n A (live n gs o) ≤ gs.length ∧
        ∀ w u : List Bool, w.length = n → u.length = m →
          AgreeOn (live n gs o) n A ρ w u → D.eval u = (gs.foldl step w).getD o false) := by
    intro gs
    induction gs with
    | nil =>
      intro n m o A ρ _ _
      cases hv : valA n A o with
      | some b =>
        left
        refine ⟨b, fun w u _ _ hag => ?_⟩
        have h1 := hag o (by rw [live_nil]; simp)
        rw [hv] at h1
        exact h1
      | none =>
        right
        have hc0 : cCount n A (live n [] o) = 0 := by
          simp only [cCount, live_nil, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
            Finset.mem_singleton, forall_eq]
          intro h
          have : valA n A o = A o := if_pos h.1
          rw [hv] at this
          rw [← this] at h
          simp at h
        refine ⟨⟨[], ρ o⟩, ?_, ?_, fun w u _ _ hag => ?_⟩
        · intro g hg; cases hg
        · change ([] : List Gate).length + cCount n A (live n [] o) ≤ ([] : List Gate).length
          simp [hc0]
        · have h1 := hag o (by rw [live_nil]; simp)
          rw [hv] at h1
          exact h1.symm
    | cons g gs ih =>
      intro n m o A ρ hρ hgs
      have hg := hgs g (by simp)
      have htail : ∀ h ∈ gs, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          h.inputs.length ≤ 2 ∧ (h.op = GateOp.not → h.inputs.length ≤ 1) :=
        fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      let S := live (n + 1) gs o
      by_cases hlive : n ∈ S
      · have hS0 : live n (g :: gs) o = S.erase n ∪ g.inputs.toFinset := by
          rw [live_cons, if_pos hlive]
        have hGate : (∃ b : Bool, ∀ w u : List Bool, w.length = n →
              AgreeOn (live n (g :: gs) o) n A ρ w u →
              g.op.eval (g.inputs.map fun i => w.getD i false) = b) ∨
            (∃ j : ℕ, j ∈ g.inputs ∧ valA n A j = none ∧
              (g.inputs.toFinset.filter (fun i => i < n ∧ (A i).isSome)).card ≤ 1 ∧
              ∀ w u : List Bool, w.length = n →
                AgreeOn (live n (g :: gs) o) n A ρ w u →
                g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD j false) ∨
            (∀ j ∈ g.inputs, valA n A j = none) := by
          obtain ⟨hop, hlen, hnot⟩ := hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          have hmem : ∀ j ∈ g.inputs, j ∈ live n (g :: gs) o := fun j hj => by
            rw [hS0]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hj)
          have hval : ∀ (j : ℕ) (hj : j ∈ g.inputs) (b : Bool), valA n A j = some b →
              ∀ w u : List Bool, AgreeOn (live n (g :: gs) o) n A ρ w u → w.getD j false = b := by
            intro j hj b hvb w u hag
            have := hag j (hmem j hj)
            rwa [hvb] at this
          rcases hop with hop | hop | hop
          · cases hi : g.inputs with
            | nil => left; exact ⟨true, fun _ _ _ _ => by rw [hop]; rfl⟩
            | cons a l =>
              cases l with
              | nil =>
                cases ha : valA n A a with
                | some b =>
                  left
                  refine ⟨b, fun w u _ hag => ?_⟩
                  have hwa := hval a (by rw [hi]; simp) b ha w u hag
                  rw [hop]; change (w.getD a false && true) = b; rw [hwa, Bool.and_true]
                | none =>
                  right; left
                  have hcard : (([a] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome)).card ≤ 1 := by
                    calc _ ≤ ([a] : List ℕ).toFinset.card := Finset.card_filter_le _ _
                      _ ≤ 1 := by simp
                  refine ⟨a, by simp, ha, hcard, fun w u _ _ => by rw [hop]; change (w.getD a false && true) = _; exact Bool.and_true _⟩
              | cons b l =>
                cases l with
                | cons _ _ => simp [hi] at hlen
                | nil =>
                  cases ha : valA n A a with
                  | some ba =>
                    cases ba with
                    | false =>
                      left
                      refine ⟨false, fun w u _ hag => ?_⟩
                      have hwa := hval a (by rw [hi]; simp) false ha w u hag
                      rw [hop]; change (w.getD a false && (w.getD b false && true)) = false; rw [hwa]; rfl
                    | true =>
                      cases hb : valA n A b with
                      | some bb =>
                        left
                        refine ⟨bb, fun w u _ hag => ?_⟩
                        have hwa := hval a (by rw [hi]; simp) true ha w u hag
                        have hwb := hval b (by rw [hi]; simp) bb hb w u hag
                        rw [hop]; change (w.getD a false && (w.getD b false && true)) = bb; rw [hwa, hwb, Bool.true_and, Bool.and_true]
                      | none =>
                        right; left
                        have hbn : ¬ (b < n ∧ (A b).isSome) := by
                          intro h; have : valA n A b = A b := if_pos h.1
                          rw [hb] at this; rw [← this] at h; simp at h
                        have hcard : (([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome)).card ≤ 1 := by
                          have hsub : ([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome) ⊆ {a} := by
                            intro x hx
                            simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
                              List.not_mem_nil, or_false] at hx
                            rcases hx.1 with rfl | rfl
                            · simp
                            · exact False.elim (hbn hx.2)
                          exact (Finset.card_le_card hsub).trans (by simp)
                        refine ⟨b, by simp, hb, hcard, fun w u _ hag => ?_⟩
                        have hwa := hval a (by rw [hi]; simp) true ha w u hag
                        rw [hop]; change (w.getD a false && (w.getD b false && true)) = w.getD b false; rw [hwa, Bool.true_and, Bool.and_true]
                  | none =>
                    cases hb : valA n A b with
                    | some bb =>
                      cases bb with
                      | false =>
                        left
                        refine ⟨false, fun w u _ hag => ?_⟩
                        have hwb := hval b (by rw [hi]; simp) false hb w u hag
                        rw [hop]; change (w.getD a false && (w.getD b false && true)) = false; rw [hwb, Bool.false_and, Bool.and_false]
                      | true =>
                        right; left
                        have han : ¬ (a < n ∧ (A a).isSome) := by
                          intro h; have : valA n A a = A a := if_pos h.1
                          rw [ha] at this; rw [← this] at h; simp at h
                        have hcard : (([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome)).card ≤ 1 := by
                          have hsub : ([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome) ⊆ {b} := by
                            intro x hx
                            simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
                              List.not_mem_nil, or_false] at hx
                            rcases hx.1 with rfl | rfl
                            · exact False.elim (han hx.2)
                            · simp
                          exact (Finset.card_le_card hsub).trans (by simp)
                        refine ⟨a, by simp, ha, hcard, fun w u _ hag => ?_⟩
                        have hwb := hval b (by rw [hi]; simp) true hb w u hag
                        rw [hop]; change (w.getD a false && (w.getD b false && true)) = w.getD a false; rw [hwb, Bool.and_true, Bool.and_true]
                    | none =>
                      right; right
                      intro j hj
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                      rcases hj with rfl | rfl <;> assumption
          · cases hi : g.inputs with
            | nil => left; exact ⟨false, fun _ _ _ _ => by rw [hop]; rfl⟩
            | cons a l =>
              cases l with
              | nil =>
                cases ha : valA n A a with
                | some b =>
                  left
                  refine ⟨b, fun w u _ hag => ?_⟩
                  have hwa := hval a (by rw [hi]; simp) b ha w u hag
                  rw [hop]; change (w.getD a false || false) = b; rw [hwa, Bool.or_false]
                | none =>
                  right; left
                  have hcard : (([a] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome)).card ≤ 1 := by
                    calc _ ≤ ([a] : List ℕ).toFinset.card := Finset.card_filter_le _ _
                      _ ≤ 1 := by simp
                  refine ⟨a, by simp, ha, hcard, fun w u _ _ => by rw [hop]; change (w.getD a false || false) = _; exact Bool.or_false _⟩
              | cons b l =>
                cases l with
                | cons _ _ => simp [hi] at hlen
                | nil =>
                  cases ha : valA n A a with
                  | some ba =>
                    cases ba with
                    | true =>
                      left
                      refine ⟨true, fun w u _ hag => ?_⟩
                      have hwa := hval a (by rw [hi]; simp) true ha w u hag
                      rw [hop]; change (w.getD a false || (w.getD b false || false)) = true; rw [hwa]; rfl
                    | false =>
                      cases hb : valA n A b with
                      | some bb =>
                        left
                        refine ⟨bb, fun w u _ hag => ?_⟩
                        have hwa := hval a (by rw [hi]; simp) false ha w u hag
                        have hwb := hval b (by rw [hi]; simp) bb hb w u hag
                        rw [hop]; change (w.getD a false || (w.getD b false || false)) = bb; rw [hwa, hwb, Bool.false_or, Bool.or_false]
                      | none =>
                        right; left
                        have hbn : ¬ (b < n ∧ (A b).isSome) := by
                          intro h; have : valA n A b = A b := if_pos h.1
                          rw [hb] at this; rw [← this] at h; simp at h
                        have hcard : (([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome)).card ≤ 1 := by
                          have hsub : ([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome) ⊆ {a} := by
                            intro x hx
                            simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
                              List.not_mem_nil, or_false] at hx
                            rcases hx.1 with rfl | rfl
                            · simp
                            · exact False.elim (hbn hx.2)
                          exact (Finset.card_le_card hsub).trans (by simp)
                        refine ⟨b, by simp, hb, hcard, fun w u _ hag => ?_⟩
                        have hwa := hval a (by rw [hi]; simp) false ha w u hag
                        rw [hop]; change (w.getD a false || (w.getD b false || false)) = w.getD b false; rw [hwa, Bool.false_or, Bool.or_false]
                  | none =>
                    cases hb : valA n A b with
                    | some bb =>
                      cases bb with
                      | true =>
                        left
                        refine ⟨true, fun w u _ hag => ?_⟩
                        have hwb := hval b (by rw [hi]; simp) true hb w u hag
                        rw [hop]; change (w.getD a false || (w.getD b false || false)) = true; rw [hwb, Bool.true_or, Bool.or_true]
                      | false =>
                        right; left
                        have han : ¬ (a < n ∧ (A a).isSome) := by
                          intro h; have : valA n A a = A a := if_pos h.1
                          rw [ha] at this; rw [← this] at h; simp at h
                        have hcard : (([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome)).card ≤ 1 := by
                          have hsub : ([a, b] : List ℕ).toFinset.filter (fun i => i < n ∧ (A i).isSome) ⊆ {b} := by
                            intro x hx
                            simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
                              List.not_mem_nil, or_false] at hx
                            rcases hx.1 with rfl | rfl
                            · exact False.elim (han hx.2)
                            · simp
                          exact (Finset.card_le_card hsub).trans (by simp)
                        refine ⟨a, by simp, ha, hcard, fun w u _ hag => ?_⟩
                        have hwb := hval b (by rw [hi]; simp) false hb w u hag
                        rw [hop]; change (w.getD a false || (w.getD b false || false)) = w.getD a false; rw [hwb, Bool.or_false, Bool.or_false]
                    | none =>
                      right; right
                      intro j hj
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                      rcases hj with rfl | rfl <;> assumption
          · have h1 := hnot hop
            cases hi : g.inputs with
            | nil => left; exact ⟨true, fun _ _ _ _ => by rw [hop]; rfl⟩
            | cons a l =>
              cases l with
              | cons _ _ => simp [hi] at h1
              | nil =>
                cases ha : valA n A a with
                | some ba =>
                  left
                  refine ⟨!ba, fun w u _ hag => ?_⟩
                  have hwa := hval a (by rw [hi]; simp) ba ha w u hag
                  rw [hop]; change (!(w.getD a false)) = !ba; rw [hwa]
                | none =>
                  right; right
                  intro j hj
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  subst hj; exact ha
        rcases hGate with ⟨b, hb⟩ | ⟨j, hjmem, hjnone, hcard1, hj⟩ | hallnone
        · let A' : ℕ → Option Bool := Function.update A n (some b)
          have hρ' : ∀ i < n + 1, A' i = none → ρ i < m := by
            intro i hi hAi
            by_cases hin : i = n
            · subst hin; simp [A'] at hAi
            · simp only [A', Function.update_of_ne hin] at hAi
              exact hρ i (by omega) hAi
          have hcc : cCount n A (live n (g :: gs) o) ≤ cCount (n + 1) A' S + 1 := by
            have h1 : cCount n A (live n (g :: gs) o) ≤ cCount n A (S.erase n) + 2 := by
              rw [hS0]
              calc cCount n A (S.erase n ∪ g.inputs.toFinset)
                  ≤ cCount n A (S.erase n) + cCount n A g.inputs.toFinset := by
                    simp only [cCount, Finset.filter_union]
                    exact Finset.card_union_le _ _
                _ ≤ cCount n A (S.erase n) + g.inputs.toFinset.card := by
                    gcongr; exact Finset.card_filter_le _ _
                _ ≤ cCount n A (S.erase n) + g.inputs.length := by
                    gcongr; exact List.toFinset_card_le _
                _ ≤ cCount n A (S.erase n) + 2 := by have := hg.2.1; omega
            have h2 : cCount n A (S.erase n) + 1 = cCount (n + 1) A' S := by
              have hsub : (S.filter (fun i => i < n + 1 ∧ (A' i).isSome)) =
                  insert n ((S.erase n).filter (fun i => i < n ∧ (A i).isSome)) := by
                ext x
                simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase, A']
                by_cases hxn : x = n
                · subst hxn; simp [hlive]
                · simp only [hxn, false_or, ne_eq, not_false_eq_true, true_and,
                    Function.update_of_ne hxn]
                  constructor
                  · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
                  · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
              have hnot : n ∉ (S.erase n).filter (fun i => i < n ∧ (A i).isSome) := by simp
              simp only [cCount, hsub, Finset.card_insert_of_notMem hnot]
            omega
          have hAg : ∀ w u : List Bool, w.length = n → AgreeOn (live n (g :: gs) o) n A ρ w u →
              AgreeOn S (n + 1) A' ρ (step w g) u := by
            intro w u hwlen hag i hi
            by_cases hin : i = n
            · subst i
              have hv : valA (n + 1) A' n = some b := by simp [valA, A']
              rw [hv]
              dsimp only [Option.elim]
              have hbg := hb w u hwlen hag
              have hend := atEnd w (g.op.eval (g.inputs.map fun k => w.getD k false))
              rw [hwlen] at hend
              simp only [step]
              rw [hend, hbg]
            · have hi0 : i ∈ live n (g :: gs) o := by
                rw [hS0]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hin, hi⟩)
              have hag0 := hag i hi0
              by_cases hilt : i < n
              · have hv1 : valA (n + 1) A' i = valA n A i := by
                  simp only [valA, hilt, show i < n + 1 by omega, ite_true, A',
                    Function.update_of_ne hin]
                rw [hv1]
                have hget : (step w g).getD i false = w.getD i false := by
                  simp only [step, List.getD_eq_getElem?_getD,
                    List.getElem?_append_left (hwlen.symm ▸ hilt)]
                rw [hget]; exact hag0
              · have hge : ¬ (i < n + 1) := by omega
                have hv1 : valA (n + 1) A' i = some false := by simp [valA, hge]
                rw [hv1]
                have hge2 : (step w g).length ≤ i := by simp [step, hwlen]; omega
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
          rcases ih (n + 1) m o A' ρ hρ' htail with ⟨c, hc⟩ | ⟨D, hDF, hDsz, hDeval⟩
          · left
            refine ⟨c, fun w u hw hu hag => ?_⟩
            rw [List.foldl_cons]
            exact hc (step w g) u (by simp [step, hw]) hu (hAg w u hw hag)
          · right
            refine ⟨D, hDF, by dsimp only [S] at hcc; simp only [List.length_cons]; omega, fun w u hw hu hag => ?_⟩
            rw [List.foldl_cons]
            exact hDeval (step w g) u (by simp [step, hw]) hu (hAg w u hw hag)
        · let A' : ℕ → Option Bool := Function.update A n none
          let ρ' : ℕ → ℕ := Function.update ρ n (ρ j)
          have hjlt : j < n ∧ A j = none := by
            by_cases h : j < n
            · refine ⟨h, ?_⟩
              have : valA n A j = A j := if_pos h
              rw [hjnone] at this
              exact this.symm
            · exfalso
              have : valA n A j = some false := if_neg h
              rw [hjnone] at this; cases this
          have hρ' : ∀ i < n + 1, A' i = none → ρ' i < m := by
            intro i hi hAi
            by_cases hin : i = n
            · subst i
              simp only [ρ', Function.update_self]
              exact hρ j hjlt.1 hjlt.2
            · simp only [A', Function.update_of_ne hin] at hAi
              simp only [ρ', Function.update_of_ne hin]
              exact hρ i (by omega) hAi
          have hcc : cCount n A (live n (g :: gs) o) ≤ cCount (n + 1) A' S + 1 := by
            have h1 : cCount n A (live n (g :: gs) o) ≤ cCount n A (S.erase n) + 1 := by
              rw [hS0]
              calc cCount n A (S.erase n ∪ g.inputs.toFinset)
                  ≤ cCount n A (S.erase n) + cCount n A g.inputs.toFinset := by
                    simp only [cCount, Finset.filter_union]
                    exact Finset.card_union_le _ _
                _ ≤ cCount n A (S.erase n) + 1 := Nat.add_le_add_left hcard1 _
            have h2 : cCount n A (S.erase n) = cCount (n + 1) A' S := by
              simp only [cCount]
              congr 1
              ext x
              simp only [Finset.mem_filter, Finset.mem_erase, A']
              by_cases hxn : x = n
              · subst hxn; simp
              · simp only [hxn, ne_eq, not_false_eq_true, true_and, Function.update_of_ne hxn]
                constructor
                · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
                · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
            omega
          have hAg : ∀ w u : List Bool, w.length = n → AgreeOn (live n (g :: gs) o) n A ρ w u →
              AgreeOn S (n + 1) A' ρ' (step w g) u := by
            intro w u hwlen hag i hi
            by_cases hin : i = n
            · subst i
              have hv : valA (n + 1) A' n = none := by simp [valA, A']
              rw [hv]
              dsimp only [Option.elim]
              have hbg := hj w u hwlen hag
              have hend := atEnd w (g.op.eval (g.inputs.map fun k => w.getD k false))
              rw [hwlen] at hend
              have hj0 : j ∈ live n (g :: gs) o := by
                rw [hS0]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hjmem)
              have hagj := hag j hj0
              rw [hjnone] at hagj
              simp only [step, ρ', Function.update_self]
              rw [hend, hbg, hagj]
            · have hi0 : i ∈ live n (g :: gs) o := by
                rw [hS0]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hin, hi⟩)
              have hag0 := hag i hi0
              by_cases hilt : i < n
              · have hv1 : valA (n + 1) A' i = valA n A i := by
                  simp only [valA, hilt, show i < n + 1 by omega, ite_true, A',
                    Function.update_of_ne hin]
                rw [hv1]
                have hget : (step w g).getD i false = w.getD i false := by
                  simp only [step, List.getD_eq_getElem?_getD,
                    List.getElem?_append_left (hwlen.symm ▸ hilt)]
                rw [hget]
                simp only [ρ', Function.update_of_ne hin]
                exact hag0
              · have hge : ¬ (i < n + 1) := by omega
                have hv1 : valA (n + 1) A' i = some false := by simp [valA, hge]
                rw [hv1]
                have hge2 : (step w g).length ≤ i := by simp [step, hwlen]; omega
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
          rcases ih (n + 1) m o A' ρ' hρ' htail with ⟨c, hc⟩ | ⟨D, hDF, hDsz, hDeval⟩
          · left
            refine ⟨c, fun w u hw hu hag => ?_⟩
            rw [List.foldl_cons]
            exact hc (step w g) u (by simp [step, hw]) hu (hAg w u hw hag)
          · right
            refine ⟨D, hDF, by dsimp only [S] at hcc; simp only [List.length_cons]; omega, fun w u hw hu hag => ?_⟩
            rw [List.foldl_cons]
            exact hDeval (step w g) u (by simp [step, hw]) hu (hAg w u hw hag)
        · let g' : Gate := ⟨g.op, g.inputs.map ρ⟩
          let A' : ℕ → Option Bool := Function.update A n none
          let ρ' : ℕ → ℕ := Function.update ρ n m
          have hρ' : ∀ i < n + 1, A' i = none → ρ' i < m + 1 := by
            intro i hi hAi
            by_cases hin : i = n
            · subst i; simp [ρ']
            · simp only [A', Function.update_of_ne hin] at hAi
              simp only [ρ', Function.update_of_ne hin]
              have := hρ i (by omega) hAi
              omega
          have hcc : cCount n A (live n (g :: gs) o) = cCount (n + 1) A' S := by
            have hzero : cCount n A g.inputs.toFinset = 0 := by
              simp only [cCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, List.mem_toFinset]
              intro j hj h
              have := hallnone j hj
              have hvalj : valA n A j = A j := if_pos h.1
              rw [this] at hvalj
              rw [← hvalj] at h
              simp at h
            have h1 : cCount n A (live n (g :: gs) o) = cCount n A (S.erase n) := by
              rw [hS0]
              simp only [cCount, Finset.filter_union]
              have hemp : g.inputs.toFinset.filter (fun i => i < n ∧ (A i).isSome) = ∅ :=
                Finset.card_eq_zero.mp hzero
              rw [hemp, Finset.union_empty]
            rw [h1]
            simp only [cCount]
            congr 1
            ext x
            simp only [Finset.mem_filter, Finset.mem_erase, A']
            by_cases hxn : x = n
            · subst hxn; simp
            · simp only [hxn, ne_eq, not_false_eq_true, true_and, Function.update_of_ne hxn]
              constructor
              · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
              · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
          have hAg : ∀ w u : List Bool, w.length = n → u.length = m →
              AgreeOn (live n (g :: gs) o) n A ρ w u →
              AgreeOn S (n + 1) A' ρ' (step w g) (step u g') := by
            intro w u hwlen hulen hag i hi
            by_cases hin : i = n
            · subst i
              have hv : valA (n + 1) A' n = none := by simp [valA, A']
              rw [hv]
              dsimp only [Option.elim]
              have hmap : g.inputs.map (fun k => w.getD k false) =
                  g'.inputs.map (fun k => u.getD k false) := by
                simp only [g', List.map_map]
                apply List.map_congr_left
                intro k hk
                have hk0 : k ∈ live n (g :: gs) o := by
                  rw [hS0]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hk)
                have hagk := hag k hk0
                rw [hallnone k hk] at hagk
                exact hagk
              have hend1 := atEnd w (g.op.eval (g.inputs.map fun k => w.getD k false))
              have hend2 := atEnd u (g'.op.eval (g'.inputs.map fun k => u.getD k false))
              rw [hwlen] at hend1
              rw [hulen] at hend2
              simp only [step, ρ', Function.update_self]
              rw [hend1, hend2]
              simp only [g', hmap]
            · have hi0 : i ∈ live n (g :: gs) o := by
                rw [hS0]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hin, hi⟩)
              have hag0 := hag i hi0
              by_cases hilt : i < n
              · have hv1 : valA (n + 1) A' i = valA n A i := by
                  simp only [valA, hilt, show i < n + 1 by omega, ite_true, A',
                    Function.update_of_ne hin]
                rw [hv1]
                have hget : (step w g).getD i false = w.getD i false := by
                  simp only [step, List.getD_eq_getElem?_getD,
                    List.getElem?_append_left (hwlen.symm ▸ hilt)]
                rw [hget]
                simp only [ρ', Function.update_of_ne hin]
                cases hvi : valA n A i with
                | some b => rwa [hvi] at hag0
                | none =>
                  rw [hvi] at hag0
                  have hAi : A i = none := by
                    have : valA n A i = A i := if_pos hilt
                    rw [hvi] at this
                    exact this.symm
                  have hru : ρ i < m := hρ i hilt hAi
                  have hgetu : (step u g').getD (ρ i) false = u.getD (ρ i) false := by
                    simp only [step, List.getD_eq_getElem?_getD,
                      List.getElem?_append_left (hulen.symm ▸ hru)]
                  rw [hgetu]; exact hag0
              · have hge : ¬ (i < n + 1) := by omega
                have hv1 : valA (n + 1) A' i = some false := by simp [valA, hge]
                rw [hv1]
                have hge2 : (step w g).length ≤ i := by simp [step, hwlen]; omega
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
          rcases ih (n + 1) (m + 1) o A' ρ' hρ' htail with ⟨c, hc⟩ | ⟨D, hDF, hDsz, hDeval⟩
          · left
            refine ⟨c, fun w u hw hu hag => ?_⟩
            rw [List.foldl_cons]
            exact hc (step w g) (step u g') (by simp [step, hw]) (by simp [step, hu]) (hAg w u hw hu hag)
          · right
            refine ⟨⟨g' :: D.gates, D.output⟩, ?_, ?_, fun w u hw hu hag => ?_⟩
            · intro h hh
              simp only [List.mem_cons] at hh
              rcases hh with rfl | hh
              · exact ⟨hg.1, by simp [g', hg.2.1]⟩
              · exact hDF h hh
            · dsimp only [S] at hcc
              change (g' :: D.gates).length + cCount n A (live n (g :: gs) o) ≤ (g :: gs).length
              change D.gates.length + cCount (n + 1) A' (live (n + 1) gs o) ≤ gs.length at hDsz
              simp only [List.length_cons]
              omega
            · change (D.gates.foldl step (step u g')).getD D.output false =
                (gs.foldl step (step w g)).getD o false
              exact hDeval (step w g) (step u g') (by simp [step, hw]) (by simp [step, hu]) (hAg w u hw hu hag)
      · have hS0 : live n (g :: gs) o = S := by rw [live_cons, if_neg hlive]
        let A' : ℕ → Option Bool := Function.update A n (some false)
        have hρ' : ∀ i < n + 1, A' i = none → ρ i < m := by
          intro i hi hAi
          by_cases hin : i = n
          · subst i; simp [A'] at hAi
          · simp only [A', Function.update_of_ne hin] at hAi
            exact hρ i (by omega) hAi
        have hcc : cCount n A (live n (g :: gs) o) = cCount (n + 1) A' S := by
          rw [hS0]
          simp only [cCount]
          congr 1
          ext x
          simp only [Finset.mem_filter, A']
          by_cases hxn : x = n
          · subst hxn; simp [hlive]
          · simp only [Function.update_of_ne hxn]
            constructor
            · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
            · intro hx; exact ⟨hx.1, by omega, hx.2.2⟩
        have hAg : ∀ w u : List Bool, w.length = n → AgreeOn (live n (g :: gs) o) n A ρ w u →
            AgreeOn S (n + 1) A' ρ (step w g) u := by
          intro w u hwlen hag i hi
          have hin : i ≠ n := fun heq => hlive (heq ▸ hi)
          have hi0 : i ∈ live n (g :: gs) o := hS0.symm ▸ hi
          have hag0 := hag i hi0
          by_cases hilt : i < n
          · have hv1 : valA (n + 1) A' i = valA n A i := by
              simp only [valA, hilt, show i < n + 1 by omega, ite_true, A',
                Function.update_of_ne hin]
            rw [hv1]
            have hget : (step w g).getD i false = w.getD i false := by
              simp only [step, List.getD_eq_getElem?_getD,
                List.getElem?_append_left (hwlen.symm ▸ hilt)]
            rw [hget]; exact hag0
          · have hge : ¬ (i < n + 1) := by omega
            have hv1 : valA (n + 1) A' i = some false := by simp [valA, hge]
            rw [hv1]
            have hge2 : (step w g).length ≤ i := by simp [step, hwlen]; omega
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
        rcases ih (n + 1) m o A' ρ hρ' htail with ⟨c, hc⟩ | ⟨D, hDF, hDsz, hDeval⟩
        · left
          refine ⟨c, fun w u hw hu hag => ?_⟩
          rw [List.foldl_cons]
          exact hc (step w g) u (by simp [step, hw]) hu (hAg w u hw hag)
        · right
          refine ⟨D, hDF, by dsimp only [S] at hcc; simp only [List.length_cons]; omega, fun w u hw hu hag => ?_⟩
          rw [List.foldl_cons]
          exact hDeval (step w g) u (by simp [step, hw]) hu (hAg w u hw hag)
  intro C hFan hFirst hFun hOp1
  by_contra! hlt
  have hSize : C.size ≤ 15 := by omega
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil => simp at hOp1
  | cons g0 gs1 =>
    cases gs1 with
    | nil => simp at hOp1
    | cons g1 rest =>
      have hg1op : g1.op = GateOp.or := by simpa using hOp1
      have hRestLen : rest.length ≤ 13 := by
        change (g0 :: g1 :: rest).length ≤ 15 at hSize
        simp at hSize; omega
      have hRestFan : ∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
        fun g hg => hFan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
      let rs : List Gate := rest.map normG
      have hRsLen : rs.length ≤ 13 := by simpa [rs] using hRestLen
      have hRsFan : FanInTwo ⟨rs, out⟩ := by
        intro g hg
        obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
        obtain ⟨hop, hlen⟩ := hRestFan h hh
        by_cases hnot : h.op = GateOp.not
        · simp only [normG, hnot, ite_true]
          exact ⟨by simpa [hnot] using hop, by simp⟩
        · simp only [normG, hnot, ite_false]
          exact ⟨hop, hlen⟩
      have hRsNorm : ∀ g ∈ rs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
        intro g hg
        obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
        obtain ⟨hop, hlen⟩ := hRestFan h hh
        by_cases hnot : h.op = GateOp.not
        · simp only [normG, hnot, ite_true]
          exact ⟨by simpa [hnot] using hop, by simp, fun _ => by simp⟩
        · simp only [normG, hnot, ite_false]
          exact ⟨hop, hlen, fun hc => False.elim hc⟩
      have hStep0 : ∀ x : Fin 9 → Bool, step (List.ofFn x) g0 = List.ofFn x ++ [x 0 || x 4] := by
        intro x
        have hv := hFirst x
        change ((g0 :: g1 :: rest).foldl step (List.ofFn x)).getD 9 false = (x 0 || x 4) at hv
        rw [List.foldl_cons] at hv
        rw [keep (g1 :: rest) (step (List.ofFn x) g0) 9 (by simp [step])] at hv
        have he := atEnd (List.ofFn x) (g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false))
        rw [List.length_ofFn] at he
        change (List.ofFn x ++ [_]).getD 9 false = _ at hv
        rw [he] at hv
        simp only [step, hv]
      let b1 (x : Fin 9 → Bool) : Bool :=
        g1.op.eval (g1.inputs.map fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false)
      have hEval : ∀ x : Fin 9 → Bool,
          (rs.foldl step (List.ofFn x ++ [x 0 || x 4, b1 x])).getD out false = f x := by
        intro x
        have he := congrFun hFun x
        change ((g0 :: g1 :: rest).foldl step (List.ofFn x)).getD out false = f x at he
        rw [List.foldl_cons, hStep0 x, List.foldl_cons] at he
        have hcat : step (List.ofFn x ++ [x 0 || x 4]) g1 = List.ofFn x ++ [x 0 || x 4, b1 x] := by
          simp [step, b1]
        rw [hcat] at he
        rw [normG_foldl]
        exact he
      let S : Finset ℕ := live 11 rs out
      let map7 (i : ℕ) : ℕ :=
        if i ≤ 3 then i - 1 else i - 2
      let embed (y : Fin 7 → Bool) : Fin 9 → Bool := fun i =>
        if i.val = 0 ∨ i.val = 4 then false
        else if h1 : i.val ≤ 3 then y ⟨i.val - 1, by omega⟩
        else y ⟨i.val - 2, by have := i.isLt; omega⟩
      have hEmbedF : ∀ y : Fin 7 → Bool, f (embed y) = theta y := by
        intro y
        have e0 : embed y 0 = false := rfl
        have e1 : embed y 1 = y 0 := rfl
        have e2 : embed y 2 = y 1 := rfl
        have e3 : embed y 3 = y 2 := rfl
        have e4 : embed y 4 = false := rfl
        have e5 : embed y 5 = y 3 := rfl
        have e6 : embed y 6 = y 4 := rfl
        have e7 : embed y 7 = y 5 := rfl
        have e8 : embed y 8 = y 6 := rfl
        dsimp only [f, theta]
        rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]
        simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
      have kill_theta : ∀ (A : ℕ → Option Bool) (ρ : ℕ → ℕ),
          (∀ i < 11, A i = none → ρ i < 7) →
          (∀ y : Fin 7 → Bool,
            AgreeOn S 11 A ρ (List.ofFn (embed y) ++ [embed y 0 || embed y 4, b1 (embed y)]) (List.ofFn y)) →
          3 ≤ cCount 11 A S → False := by
        intro A ρ hρ hAg hcnt
        rcases elim_consts rs 11 7 out A ρ hρ hRsNorm with ⟨c, hc⟩ | ⟨D, hDF, hDsz, hDeval⟩
        · let y0 : Fin 7 → Bool := fun _ => false
          let y1 : Fin 7 → Bool := fun i => decide (i = 0 ∨ i = 1)
          have h0 := hc _ (List.ofFn y0) (by simp) (by simp) (hAg y0)
          have h1 := hc _ (List.ofFn y1) (by simp) (by simp) (hAg y1)
          rw [hEval (embed y0), hEmbedF y0] at h0
          rw [hEval (embed y1), hEmbedF y1] at h1
          have ht0 : theta y0 = false := by decide
          have ht1 : theta y1 = true := by decide
          rw [ht0] at h0; rw [ht1] at h1
          exact Bool.false_ne_true (h0.trans h1.symm)
        · apply hTheta
          refine ⟨D, hDF, by dsimp only [S] at hcnt; omega, fun y => ?_⟩
          have hd := hDeval _ (List.ofFn y) (by simp) (by simp) (hAg y)
          rw [hEval (embed y), hEmbedF y] at hd
          exact hd
      have kill_fourteen_g1 : 9 ∉ S → 9 ∉ g1.inputs → False := by
        intro h9S h9g1
        let A9 : ℕ → Option Bool := fun i => if i = 9 then some false else none
        have h9L : 9 ∉ live 10 (g1 :: rs) out := by
          rw [live_cons]
          split
          · simp only [Finset.mem_union, Finset.mem_erase, List.mem_toFinset, not_or]
            exact ⟨fun h => h9S h.2, h9g1⟩
          · exact h9S
        have hNorm1 : ∀ g ∈ g1 :: rs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
          intro g hg
          rcases List.mem_cons.mp hg with hEq | hg
          · subst g
            have hfg := hFan g1 (List.mem_cons_of_mem _ (List.mem_cons_self))
            exact ⟨hfg.1, hfg.2, fun h => by rw [hg1op] at h; cases h⟩
          · exact hRsNorm g hg
        have hρ9 : ∀ i < 10, A9 i = none → i < 9 := by
          intro i hi hAi
          by_cases h9 : i = 9
          · subst h9; simp [A9] at hAi
          · omega
        have hAg9 : ∀ x : Fin 9 → Bool,
            AgreeOn (live 10 (g1 :: rs) out) 10 A9 id (List.ofFn x ++ [x 0 || x 4]) (List.ofFn x) := by
          intro x i hi
          have hi9 : i ≠ 9 := fun heq => h9L (heq ▸ hi)
          by_cases hlt9 : i < 9
          · have hv : valA 10 A9 i = none := by simp [valA, A9, hi9, show i < 10 by omega]
            rw [hv]
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp [hlt9])]
            rfl
          · have hge10 : ¬ (i < 10) := by omega
            have hv : valA 10 A9 i = some false := by simp [valA, hge10]
            rw [hv]
            have hlen : (List.ofFn x ++ [x 0 || x 4]).length ≤ i := by simp; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
            rfl
        have hEval1 : ∀ x : Fin 9 → Bool,
            ((g1 :: rs).foldl step (List.ofFn x ++ [x 0 || x 4])).getD out false = f x := by
          intro x
          rw [List.foldl_cons]
          have hcat : step (List.ofFn x ++ [x 0 || x 4]) g1 = List.ofFn x ++ [x 0 || x 4, b1 x] := by
            simp [step, b1]
          rw [hcat]
          exact hEval x
        rcases elim_consts (g1 :: rs) 10 9 out A9 id hρ9 hNorm1 with ⟨c, hc⟩ | ⟨D, hDF, hDsz, hDeval⟩
        · let x0 : Fin 9 → Bool := fun _ => false
          let x1 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
          have h0 := hc _ (List.ofFn x0) (by simp) (by simp) (hAg9 x0)
          have h1 := hc _ (List.ofFn x1) (by simp) (by simp) (hAg9 x1)
          rw [hEval1 x0] at h0; rw [hEval1 x1] at h1
          have hf0 : f x0 = false := by decide
          have hf1 : f x1 = true := by decide
          rw [hf0] at h0; rw [hf1] at h1
          exact Bool.false_ne_true (h0.trans h1.symm)
        · apply hFourteen
          refine ⟨D, hDF, by simp only [List.length_cons] at hDsz; omega, fun x => ?_⟩
          have hd := hDeval _ (List.ofFn x) (by simp) (by simp) (hAg9 x)
          rw [hEval1 x] at hd
          exact hd
      have kill_fourteen_rs : 9 ∉ S → 10 ∉ S → False := by
        intro h9S h10S
        let A11 : ℕ → Option Bool := fun i => if i = 9 ∨ i = 10 then some false else none
        have hρ11 : ∀ i < 11, A11 i = none → i < 9 := by
          intro i hi hAi
          by_cases h9 : i = 9
          · subst h9; simp [A11] at hAi
          · by_cases h10 : i = 10
            · subst h10; simp [A11] at hAi
            · omega
        have hAg11 : ∀ x : Fin 9 → Bool,
            AgreeOn S 11 A11 id (List.ofFn x ++ [x 0 || x 4, b1 x]) (List.ofFn x) := by
          intro x i hi
          have hi9 : i ≠ 9 := fun heq => h9S (heq ▸ hi)
          have hi10 : i ≠ 10 := fun heq => h10S (heq ▸ hi)
          by_cases hlt9 : i < 9
          · have hv : valA 11 A11 i = none := by simp [valA, A11, hi9, hi10, show i < 11 by omega]
            rw [hv]
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp [hlt9])]
            rfl
          · have hge11 : ¬ (i < 11) := by omega
            have hv : valA 11 A11 i = some false := by simp [valA, hge11]
            rw [hv]
            have hlen : (List.ofFn x ++ [x 0 || x 4, b1 x]).length ≤ i := by simp; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
            rfl
        rcases elim_consts rs 11 9 out A11 id hρ11 hRsNorm with ⟨c, hc⟩ | ⟨D, hDF, hDsz, hDeval⟩
        · let x0 : Fin 9 → Bool := fun _ => false
          let x1 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
          have h0 := hc _ (List.ofFn x0) (by simp) (by simp) (hAg11 x0)
          have h1 := hc _ (List.ofFn x1) (by simp) (by simp) (hAg11 x1)
          rw [hEval x0] at h0; rw [hEval x1] at h1
          have hf0 : f x0 = false := by decide
          have hf1 : f x1 = true := by decide
          rw [hf0] at h0; rw [hf1] at h1
          exact Bool.false_ne_true (h0.trans h1.symm)
        · apply hFourteen
          refine ⟨D, hDF, by omega, fun x => ?_⟩
          have hd := hDeval _ (List.ofFn x) (by simp) (by simp) (hAg11 x)
          rw [hEval x] at hd
          exact hd
      have force_mem : ∀ (idx : ℕ) (x₁ x₂ : Fin 9 → Bool),
          f x₁ ≠ f x₂ →
          (∀ i < 11, i ≠ idx →
            (List.ofFn x₁ ++ [x₁ 0 || x₁ 4, b1 x₁]).getD i false =
            (List.ofFn x₂ ++ [x₂ 0 || x₂ 4, b1 x₂]).getD i false) →
          idx ∈ S := by
        intro idx x₁ x₂ hne hag
        by_contra hnot
        have hEq := agree_eval rs (List.ofFn x₁ ++ [x₁ 0 || x₁ 4, b1 x₁])
          (List.ofFn x₂ ++ [x₂ 0 || x₂ 4, b1 x₂]) out (by simp) (by
            intro i hi
            by_cases hilt : i < 11
            · exact hag i hilt (fun heq => hnot (heq ▸ hi))
            · have hge1 : (List.ofFn x₁ ++ [x₁ 0 || x₁ 4, b1 x₁]).length ≤ i := by simp; omega
              have hge2 : (List.ofFn x₂ ++ [x₂ 0 || x₂ 4, b1 x₂]).length ≤ i := by simp; omega
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_none hge1, List.getElem?_eq_none hge2])
        rw [hEval x₁, hEval x₂] at hEq
        exact hne hEq
      have make_theta_const : (∀ y : Fin 7 → Bool, b1 (embed y) = false) →
          (∃ k ∈ S, k < 11 ∧ (k = 0 ∨ k = 4 ∨ k = 9 ∨ k = 10)) →
          3 ≤ (S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10)).card → False := by
        intro hb10 _ hcard
        let A : ℕ → Option Bool := fun i =>
          if i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10 then some false else none
        apply kill_theta A map7
        · intro i hi hAi
          have hne : ¬ (i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
            intro h; simp [A, h] at hAi
          interval_cases i <;> simp [map7] at hne ⊢
        · intro y i hi
          rw [hb10 y]
          by_cases hilt : i < 11
          · interval_cases i <;>
              simp [valA, A, map7, embed, Option.elim, List.getD_eq_getElem?_getD,
                List.ofFn_succ]
          · have hge : (List.ofFn (embed y) ++ [embed y 0 || embed y 4, false]).length ≤ i := by
              simp; omega
            rw [show valA 11 A i = some false from if_neg hilt]
            dsimp only [Option.elim]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
            rfl
        · have hsub : S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) ⊆
              S.filter (fun i => i < 11 ∧ (A i).isSome) := by
            intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, ?_, ?_⟩
            · rcases hx.2 with rfl | rfl | rfl | rfl <;> omega
            · simp [A, hx.2]
          exact hcard.trans (Finset.card_le_card hsub)
      have make_theta_alias : ∀ (v : Fin 9), v ≠ 0 → v ≠ 4 →
          (∀ y : Fin 7 → Bool, b1 (embed y) = embed y v) →
          0 ∈ S → 4 ∈ S → 9 ∈ S → False := by
        intro v hv0 hv4 hb1v h0S h4S h9S
        let A : ℕ → Option Bool := fun i =>
          if i = 0 ∨ i = 4 ∨ i = 9 then some false else none
        let ρ : ℕ → ℕ := fun i => if i = 10 then map7 v.val else map7 i
        apply kill_theta A ρ
        · intro i hi hAi
          have hne : ¬ (i = 0 ∨ i = 4 ∨ i = 9) := by
            intro h; simp [A, h] at hAi
          interval_cases i
          all_goals simp [ρ, map7] at hne ⊢
          · fin_cases v <;> simp at hv0 hv4 ⊢
        · intro y i hi
          rw [hb1v y]
          by_cases hilt : i < 11
          · interval_cases i
            all_goals simp [valA, A, ρ, map7, embed, Option.elim, List.getD_eq_getElem?_getD,
              List.ofFn_succ]
            · fin_cases v <;> simp at hv0 hv4 ⊢
          · have hge : (List.ofFn (embed y) ++ [embed y 0 || embed y 4, embed y v]).length ≤ i := by
              simp; omega
            rw [show valA 11 A i = some false from if_neg hilt]
            dsimp only [Option.elim]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
            rfl
        · have hsub : ({0, 4, 9} : Finset ℕ) ⊆ S.filter (fun i => i < 11 ∧ (A i).isSome) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp only [Finset.mem_filter]
            rcases hx with rfl | rfl | rfl
            · exact ⟨h0S, by omega, by simp [A]⟩
            · exact ⟨h4S, by omega, by simp [A]⟩
            · exact ⟨h9S, by omega, by simp [A]⟩
          exact (show (3 : ℕ) ≤ ({0, 4, 9} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub)
      have case_false : (∀ x, b1 x = false) → 9 ∉ g1.inputs → False := by
        intro hb h9g1
        by_cases h9S : 9 ∈ S
        · have h0S : 0 ∈ S := force_mem 0 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 4))
            (by decide) (fun i hi hne => by interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          have h4S : 4 ∈ S := force_mem 4 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 0))
            (by decide) (fun i hi hne => by interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          have hsub : ({0, 4, 9} : Finset ℕ) ⊆ S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp only [Finset.mem_filter]; rcases hx with rfl | rfl | rfl <;> simp [h0S, h4S, h9S]
          exact make_theta_const (fun y => hb (embed y)) ⟨0, h0S, by omega, Or.inl rfl⟩
            ((show (3 : ℕ) ≤ ({0, 4, 9} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub))
        · exact kill_fourteen_g1 h9S h9g1
      have case_x0 : (∀ x, b1 x = x 0) → 9 ∉ g1.inputs → False := by
        intro hb h9g1
        by_cases h9S : 9 ∈ S
        · have h4S : 4 ∈ S := force_mem 4 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 0))
            (by decide) (fun i hi hne => by interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          by_cases h10S : 10 ∈ S
          · have hsub : ({4, 9, 10} : Finset ℕ) ⊆ S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp only [Finset.mem_filter]; rcases hx with rfl | rfl | rfl <;> simp [h4S, h9S, h10S]
            exact make_theta_const (fun y => by simp [hb, embed]) ⟨4, h4S, by omega, by simp⟩
              ((show (3 : ℕ) ≤ ({4, 9, 10} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub))
          · have h0S : 0 ∈ S := by
              by_contra h0not
              let x₁ : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)
              let x₂ : Fin 9 → Bool := fun i => decide (i = 4)
              have hEq := agree_eval rs (List.ofFn x₁ ++ [x₁ 0 || x₁ 4, b1 x₁])
                (List.ofFn x₂ ++ [x₂ 0 || x₂ 4, b1 x₂]) out (by simp) (by
                  intro i hi
                  have hne0 : i ≠ 0 := fun e => h0not (e ▸ hi)
                  have hne10 : i ≠ 10 := fun e => h10S (e ▸ hi)
                  by_cases hilt : i < 11
                  · interval_cases i <;> simp [x₁, x₂, hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne0 hne10 ⊢
                  · have h1 : (List.ofFn x₁ ++ [x₁ 0 || x₁ 4, b1 x₁]).length ≤ i := by simp; omega
                    have h2 : (List.ofFn x₂ ++ [x₂ 0 || x₂ 4, b1 x₂]).length ≤ i := by simp; omega
                    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                      List.getElem?_eq_none h1, List.getElem?_eq_none h2])
              rw [hEval x₁, hEval x₂] at hEq
              exact (show f x₁ ≠ f x₂ by decide) hEq
            have hsub : ({0, 4, 9} : Finset ℕ) ⊆ S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp only [Finset.mem_filter]; rcases hx with rfl | rfl | rfl <;> simp [h0S, h4S, h9S]
            exact make_theta_const (fun y => by simp [hb, embed]) ⟨0, h0S, by omega, by simp⟩
              ((show (3 : ℕ) ≤ ({0, 4, 9} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub))
        · exact kill_fourteen_g1 h9S h9g1
      have case_x4 : (∀ x, b1 x = x 4) → 9 ∉ g1.inputs → False := by
        intro hb h9g1
        by_cases h9S : 9 ∈ S
        · have h0S : 0 ∈ S := force_mem 0 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 4))
            (by decide) (fun i hi hne => by interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          by_cases h10S : 10 ∈ S
          · have hsub : ({0, 9, 10} : Finset ℕ) ⊆ S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp only [Finset.mem_filter]; rcases hx with rfl | rfl | rfl <;> simp [h0S, h9S, h10S]
            exact make_theta_const (fun y => by simp [hb, embed]) ⟨0, h0S, by omega, by simp⟩
              ((show (3 : ℕ) ≤ ({0, 9, 10} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub))
          · have h4S : 4 ∈ S := by
              by_contra h4not
              let x₁ : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)
              let x₂ : Fin 9 → Bool := fun i => decide (i = 0)
              have hEq := agree_eval rs (List.ofFn x₁ ++ [x₁ 0 || x₁ 4, b1 x₁])
                (List.ofFn x₂ ++ [x₂ 0 || x₂ 4, b1 x₂]) out (by simp) (by
                  intro i hi
                  have hne4 : i ≠ 4 := fun e => h4not (e ▸ hi)
                  have hne10 : i ≠ 10 := fun e => h10S (e ▸ hi)
                  by_cases hilt : i < 11
                  · interval_cases i <;> simp [x₁, x₂, hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne4 hne10 ⊢
                  · have h1 : (List.ofFn x₁ ++ [x₁ 0 || x₁ 4, b1 x₁]).length ≤ i := by simp; omega
                    have h2 : (List.ofFn x₂ ++ [x₂ 0 || x₂ 4, b1 x₂]).length ≤ i := by simp; omega
                    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                      List.getElem?_eq_none h1, List.getElem?_eq_none h2])
              rw [hEval x₁, hEval x₂] at hEq
              exact (show f x₁ ≠ f x₂ by decide) hEq
            have hsub : ({0, 4, 9} : Finset ℕ) ⊆ S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp only [Finset.mem_filter]; rcases hx with rfl | rfl | rfl <;> simp [h0S, h4S, h9S]
            exact make_theta_const (fun y => by simp [hb, embed]) ⟨0, h0S, by omega, by simp⟩
              ((show (3 : ℕ) ≤ ({0, 4, 9} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub))
        · exact kill_fourteen_g1 h9S h9g1
      have case_w9 : (∀ x, b1 x = (x 0 || x 4)) → False := by
        intro hb
        have h0S : 0 ∈ S := force_mem 0 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 4))
          (by decide) (fun i hi hne => by interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
        have h4S : 4 ∈ S := force_mem 4 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 0))
          (by decide) (fun i hi hne => by interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
        by_cases h9S : 9 ∈ S
        · have hsub : ({0, 4, 9} : Finset ℕ) ⊆ S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp only [Finset.mem_filter]; rcases hx with rfl | rfl | rfl <;> simp [h0S, h4S, h9S]
          exact make_theta_const (fun y => by simp [hb, embed]) ⟨0, h0S, by omega, by simp⟩
            ((show (3 : ℕ) ≤ ({0, 4, 9} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub))
        · by_cases h10S : 10 ∈ S
          · have hsub : ({0, 4, 10} : Finset ℕ) ⊆ S.filter (fun i => i = 0 ∨ i = 4 ∨ i = 9 ∨ i = 10) := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp only [Finset.mem_filter]; rcases hx with rfl | rfl | rfl <;> simp [h0S, h4S, h10S]
            exact make_theta_const (fun y => by simp [hb, embed]) ⟨0, h0S, by omega, by simp⟩
              ((show (3 : ℕ) ≤ ({0, 4, 10} : Finset ℕ).card by decide).trans (Finset.card_le_card hsub))
          · exact kill_fourteen_rs h9S h10S
      have case_xv : ∀ (v : Fin 9), v ≠ 0 → v ≠ 4 → (∀ x, b1 x = x v) → 9 ∉ g1.inputs → False := by
        intro v hv0 hv4 hb h9g1
        by_cases h9S : 9 ∈ S
        · have h0S : 0 ∈ S := force_mem 0 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 4))
            (by decide) (fun i hi hne => by
              interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢
              · simp [hv0])
          have h4S : 4 ∈ S := force_mem 4 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 0))
            (by decide) (fun i hi hne => by
              interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢
              · simp [hv4])
          exact make_theta_alias v hv0 hv4 (fun y => hb (embed y)) h0S h4S h9S
        · exact kill_fourteen_g1 h9S h9g1
      have case_0v : ∀ (v : Fin 9), v ≠ 0 → v ≠ 4 → (∀ x, b1 x = (x 0 || x v)) → 9 ∉ g1.inputs → False := by
        intro v hv0 hv4 hb h9g1
        by_cases h9S : 9 ∈ S
        · have h4S : 4 ∈ S := force_mem 4 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 0))
            (by decide) (fun i hi hne => by
              interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          by_cases h0S : 0 ∈ S
          · exact make_theta_alias v hv0 hv4 (fun y => by simp [hb, embed]) h0S h4S h9S
          · by_cases hv3 : v = 3
            · subst hv3
              apply hSpecial ⟨rs, out⟩ hRsFan hRsLen
              left
              intro x
              have hEq := agree_eval rs (List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3])
                (List.ofFn x ++ [x 0 || x 4, b1 x]) out (by simp) (by
                  intro i hi
                  have hi0 : i ≠ 0 := fun e => h0S (e ▸ hi)
                  by_cases hilt : i < 11
                  · interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ,
                      Function.update_of_ne] at hi0 ⊢
                  · have h1 : (List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]).length ≤ i := by simp; omega
                    have h2 : (List.ofFn x ++ [x 0 || x 4, b1 x]).length ≤ i := by simp; omega
                    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                      List.getElem?_eq_none h1, List.getElem?_eq_none h2])
              exact hEq.trans (hEval x)
            · apply h0S
              refine force_mem 0 (fun i => decide (i = 0 ∨ i = 4 ∨ i = v)) (fun i => decide (i = 4 ∨ i = v))
                (by fin_cases v <;> simp at hv0 hv4 hv3 ⊢ <;> decide) (fun i hi hne => ?_)
              interval_cases i
              all_goals simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢
        · exact kill_fourteen_g1 h9S h9g1
      have case_4v : ∀ (v : Fin 9), v ≠ 0 → v ≠ 4 → (∀ x, b1 x = (x 4 || x v)) → 9 ∉ g1.inputs → False := by
        intro v hv0 hv4 hb h9g1
        by_cases h9S : 9 ∈ S
        · have h0S : 0 ∈ S := force_mem 0 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 4))
            (by decide) (fun i hi hne => by
              interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          by_cases h4S : 4 ∈ S
          · exact make_theta_alias v hv0 hv4 (fun y => by simp [hb, embed]) h0S h4S h9S
          · by_cases hv1 : v = 1
            · subst hv1
              apply hSpecial ⟨rs, out⟩ hRsFan hRsLen
              right; left
              intro x
              have hEq := agree_eval rs (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1])
                (List.ofFn x ++ [x 0 || x 4, b1 x]) out (by simp) (by
                  intro i hi
                  have hi4 : i ≠ 4 := fun e => h4S (e ▸ hi)
                  by_cases hilt : i < 11
                  · interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ,
                      Function.update_of_ne] at hi4 ⊢
                  · have h1 : (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]).length ≤ i := by simp; omega
                    have h2 : (List.ofFn x ++ [x 0 || x 4, b1 x]).length ≤ i := by simp; omega
                    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                      List.getElem?_eq_none h1, List.getElem?_eq_none h2])
              exact hEq.trans (hEval x)
            · by_cases hv5 : v = 5
              · subst hv5
                apply hSpecial ⟨rs, out⟩ hRsFan hRsLen
                right; right; left
                intro x
                have hEq := agree_eval rs (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 5])
                  (List.ofFn x ++ [x 0 || x 4, b1 x]) out (by simp) (by
                    intro i hi
                    have hi4 : i ≠ 4 := fun e => h4S (e ▸ hi)
                    by_cases hilt : i < 11
                    · interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ,
                        Function.update_of_ne] at hi4 ⊢
                    · have h1 : (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 5]).length ≤ i := by simp; omega
                      have h2 : (List.ofFn x ++ [x 0 || x 4, b1 x]).length ≤ i := by simp; omega
                      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                        List.getElem?_eq_none h1, List.getElem?_eq_none h2])
                exact hEq.trans (hEval x)
              · apply h4S
                refine force_mem 4 (fun i => decide (i = 0 ∨ i = 4 ∨ i = v)) (fun i => decide (i = 0 ∨ i = v))
                  (by fin_cases v <;> simp at hv0 hv4 hv1 hv5 ⊢ <;> decide) (fun i hi hne => ?_)
                interval_cases i
                all_goals simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢
        · exact kill_fourteen_g1 h9S h9g1
      have case_w9v : ∀ (v : Fin 9), v ≠ 0 → v ≠ 4 → (∀ x, b1 x = (x 0 || x 4 || x v)) → False := by
        intro v hv0 hv4 hb
        by_cases h9S : 9 ∈ S
        · have h0S : 0 ∈ S := force_mem 0 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 4))
            (by decide) (fun i hi hne => by
              interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          have h4S : 4 ∈ S := force_mem 4 (fun i => decide (i = 0 ∨ i = 4)) (fun i => decide (i = 0))
            (by decide) (fun i hi hne => by
              interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hne ⊢)
          exact make_theta_alias v hv0 hv4 (fun y => by simp [hb, embed]) h0S h4S h9S
        · apply hSpecial ⟨rs, out⟩ hRsFan hRsLen
          right; right; right
          refine ⟨v, hv0, hv4, fun x => ?_⟩
          have hEq := agree_eval rs (List.ofFn x ++ [false, x 0 || x 4 || x v])
            (List.ofFn x ++ [x 0 || x 4, b1 x]) out (by simp) (by
              intro i hi
              have hi9 : i ≠ 9 := fun e => h9S (e ▸ hi)
              by_cases hilt : i < 11
              · interval_cases i <;> simp [hb, List.getD_eq_getElem?_getD, List.ofFn_succ] at hi9 ⊢
              · have h1 : (List.ofFn x ++ [false, x 0 || x 4 || x v]).length ≤ i := by simp; omega
                have h2 : (List.ofFn x ++ [x 0 || x 4, b1 x]).length ≤ i := by simp; omega
                rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none h1, List.getElem?_eq_none h2])
          exact hEq.trans (hEval x)
      have hRead : ∀ (i : ℕ) (x : Fin 9 → Bool),
          (List.ofFn x ++ [x 0 || x 4]).getD i false =
          if hi : i < 9 then x ⟨i, hi⟩ else if i = 9 then (x 0 || x 4) else false := by
        intro i x
        by_cases hi : i < 9
        · simp only [hi, dite_true, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp [hi] : i < (List.ofFn x).length),
            List.getElem?_ofFn, Option.getD_some]
        · simp only [hi, dite_false]
          by_cases h9 : i = 9
          · subst h9
            have h := atEnd (List.ofFn x) (x 0 || x 4)
            simpa using h
          · simp only [h9, ite_false]
            have hge : (List.ofFn x ++ [x 0 || x 4]).length ≤ i := by simp; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
            rfl
      have hg1len : g1.inputs.length ≤ 2 :=
        (hFan g1 (List.mem_cons_of_mem _ (List.mem_cons_self))).2
      cases hi : g1.inputs with
      | nil =>
        exact case_false (fun x => by simp only [b1, hg1op, hi]; rfl) (by simp [hi])
      | cons a l =>
        cases l with
        | nil =>
          have hb1a : ∀ x, b1 x = (List.ofFn x ++ [x 0 || x 4]).getD a false := by
            intro x
            simp only [b1, hg1op, hi]
            change ((List.ofFn x ++ [x 0 || x 4]).getD a false || false) = _
            exact Bool.or_false _
          by_cases ha9 : a < 9
          · have h9not : 9 ∉ g1.inputs := by rw [hi]; simp; omega
            let va : Fin 9 := ⟨a, ha9⟩
            have hbv : ∀ x, b1 x = x va := fun x => by rw [hb1a, hRead]; simp [ha9, va]
            by_cases ha0 : va = 0
            · exact case_x0 (fun x => by rw [hbv, ha0]) h9not
            · by_cases ha4 : va = 4
              · exact case_x4 (fun x => by rw [hbv, ha4]) h9not
              · exact case_xv va ha0 ha4 hbv h9not
          · by_cases haeq9 : a = 9
            · exact case_w9 (fun x => by rw [hb1a, hRead]; simp [haeq9])
            · exact case_false (fun x => by rw [hb1a, hRead]; simp [ha9, haeq9]) (by rw [hi]; simp [Ne.symm haeq9])
        | cons b l =>
          cases l with
          | cons _ _ => simp [hi] at hg1len
          | nil =>
            have hb1ab : ∀ x, b1 x = ((List.ofFn x ++ [x 0 || x 4]).getD a false ||
                (List.ofFn x ++ [x 0 || x 4]).getD b false) := by
              intro x
              simp only [b1, hg1op, hi]
              change ((List.ofFn x ++ [x 0 || x 4]).getD a false ||
                ((List.ofFn x ++ [x 0 || x 4]).getD b false || false)) = _
              rw [Bool.or_false]
            have handle_pair : ∀ (p q : ℕ),
                (∀ x, b1 x = ((List.ofFn x ++ [x 0 || x 4]).getD p false ||
                  (List.ofFn x ++ [x 0 || x 4]).getD q false)) →
                (p ≠ 9 → q ≠ 9 → 9 ∉ g1.inputs) → False := by
              intro p q hbpq h9pq
              by_cases hp9 : p < 9
              · by_cases hq9 : q < 9
                · have h9not : 9 ∉ g1.inputs := h9pq (by omega) (by omega)
                  let vp : Fin 9 := ⟨p, hp9⟩
                  let vq : Fin 9 := ⟨q, hq9⟩
                  have hbv : ∀ x, b1 x = (x vp || x vq) := fun x => by
                    rw [hbpq, hRead, hRead]; simp [hp9, hq9, vp, vq]
                  by_cases heq : vp = vq
                  · have h1 : ∀ x, b1 x = x vp := fun x => by rw [hbv, heq, Bool.or_self]
                    by_cases hp0 : vp = 0
                    · exact case_x0 (fun x => by rw [h1, hp0]) h9not
                    · by_cases hp4 : vp = 4
                      · exact case_x4 (fun x => by rw [h1, hp4]) h9not
                      · exact case_xv vp hp0 hp4 h1 h9not
                  · by_cases hp0 : vp = 0
                    · by_cases hq4 : vq = 4
                      · exact case_w9 (fun x => by rw [hbv, hp0, hq4])
                      · exact case_0v vq (fun e => heq (hp0.trans e.symm)) hq4 (fun x => by rw [hbv, hp0]) h9not
                    · by_cases hp4 : vp = 4
                      · by_cases hq0 : vq = 0
                        · exact case_w9 (fun x => by rw [hbv, hp4, hq0, Bool.or_comm])
                        · exact case_4v vq hq0 (fun e => heq (hp4.trans e.symm)) (fun x => by rw [hbv, hp4]) h9not
                      · by_cases hq0 : vq = 0
                        · exact case_0v vp hp0 hp4 (fun x => by rw [hbv, hq0, Bool.or_comm]) h9not
                        · by_cases hq4 : vq = 4
                          · exact case_4v vp hp0 hp4 (fun x => by rw [hbv, hq4, Bool.or_comm]) h9not
                          · exact hDisjoint vp vq ⟨rs, out⟩ hp0 hp4 hq0 hq4 heq hRsFan hRsLen
                              (fun x => by
                                have he := hEval x
                                rw [hbv x] at he
                                exact he)
                · by_cases hqeq9 : q = 9
                  · let vp : Fin 9 := ⟨p, hp9⟩
                    have hbv : ∀ x, b1 x = (x vp || (x 0 || x 4)) := fun x => by
                      rw [hbpq, hRead, hRead]; simp [hp9, hq9, hqeq9, vp]
                    by_cases hp0 : vp = 0
                    · exact case_w9 (fun x => by rw [hbv, hp0]; cases x 0 <;> cases x 4 <;> rfl)
                    · by_cases hp4 : vp = 4
                      · exact case_w9 (fun x => by rw [hbv, hp4]; cases x 0 <;> cases x 4 <;> rfl)
                      · exact case_w9v vp hp0 hp4 (fun x => by rw [hbv]; cases x 0 <;> cases x 4 <;> cases x vp <;> rfl)
                  · have h9not : 9 ∉ g1.inputs := h9pq (by omega) hqeq9
                    let vp : Fin 9 := ⟨p, hp9⟩
                    have hbv : ∀ x, b1 x = x vp := fun x => by
                      rw [hbpq, hRead, hRead]; simp [hp9, hq9, hqeq9, vp]
                    by_cases hp0 : vp = 0
                    · exact case_x0 (fun x => by rw [hbv, hp0]) h9not
                    · by_cases hp4 : vp = 4
                      · exact case_x4 (fun x => by rw [hbv, hp4]) h9not
                      · exact case_xv vp hp0 hp4 hbv h9not
              · by_cases hpeq9 : p = 9
                · by_cases hq9 : q < 9
                  · let vq : Fin 9 := ⟨q, hq9⟩
                    have hbv : ∀ x, b1 x = ((x 0 || x 4) || x vq) := fun x => by
                      rw [hbpq, hRead, hRead]; simp [hp9, hpeq9, hq9, vq]
                    by_cases hq0 : vq = 0
                    · exact case_w9 (fun x => by rw [hbv, hq0]; cases x 0 <;> cases x 4 <;> rfl)
                    · by_cases hq4 : vq = 4
                      · exact case_w9 (fun x => by rw [hbv, hq4]; cases x 0 <;> cases x 4 <;> rfl)
                      · exact case_w9v vq hq0 hq4 hbv
                  · by_cases hqeq9 : q = 9
                    · exact case_w9 (fun x => by rw [hbpq, hRead, hRead]; simp [hp9, hpeq9, hq9, hqeq9])
                    · exact case_w9 (fun x => by rw [hbpq, hRead, hRead]; simp [hp9, hpeq9, hq9, hqeq9])
                · by_cases hq9 : q < 9
                  · have h9not : 9 ∉ g1.inputs := h9pq hpeq9 (by omega)
                    let vq : Fin 9 := ⟨q, hq9⟩
                    have hbv : ∀ x, b1 x = x vq := fun x => by
                      rw [hbpq, hRead, hRead]; simp [hp9, hpeq9, hq9, vq]
                    by_cases hq0 : vq = 0
                    · exact case_x0 (fun x => by rw [hbv, hq0]) h9not
                    · by_cases hq4 : vq = 4
                      · exact case_x4 (fun x => by rw [hbv, hq4]) h9not
                      · exact case_xv vq hq0 hq4 hbv h9not
                  · by_cases hqeq9 : q = 9
                    · exact case_w9 (fun x => by rw [hbpq, hRead, hRead]; simp [hp9, hpeq9, hq9, hqeq9])
                    · exact case_false (fun x => by rw [hbpq, hRead, hRead]; simp [hp9, hpeq9, hq9, hqeq9])
                        (h9pq hpeq9 hqeq9)
            exact handle_pair a b hb1ab (fun ha hb => by rw [hi]; simp [Ne.symm ha, Ne.symm hb])
