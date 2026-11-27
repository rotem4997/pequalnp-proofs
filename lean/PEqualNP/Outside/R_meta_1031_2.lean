import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_1031_2 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∃ C : Circuit, Monotone2 C ∧
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        (∀ D : Circuit, Monotone2 D →
          (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
            decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
          C.size ≤ D.size) ∧
        ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = true →
            ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (∀ D : Circuit, Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
        C.size ≤ D.size) →
      (∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = true →
          ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        ∀ (t : ℕ) (g : Gate), C'.gates[t]? = some g → g.op = GateOp.and →
          (∀ x : Fin n → Bool, (C'.wires (List.ofFn x)).getD (n + t) false = true →
            ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ∧
          ∃ u v : Fin n, G.Adj u v ∧ Owns n C' t u v) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  intro hSoundLeast hCleanOwn n G instDec htri hc4
  obtain ⟨C0, hM0, hE0, hMin0, hS0⟩ := hSoundLeast n G htri hc4
  obtain ⟨C, hM, hSz, hE, hSO⟩ := hCleanOwn n G C0 htri hc4 hM0 hE0 hMin0 hS0
  have hM_unfold : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hM g hg
  have hMin : ∀ D : Circuit,
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      C.size ≤ D.size := fun D hDM hDE => hSz.trans (hMin0 D hDM hDE)
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have getD_app_lt : ∀ (w t : List Bool) (i : ℕ), i < w.length →
      (w ++ t).getD i false = w.getD i false := by
    intro w t i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_self : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g0 gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      have hlt : i < (stepW w g0).length := by
        change i < (w ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (stepW w g0) i hlt]
      exact getD_app_lt w _ i hi
  have foldl_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl stepW w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro w j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (stepW w g0).length := by
          change w.length < (w ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [foldl_getD_lt gs (stepW w g0) w.length hlt]
        rw [getD_app_self w _]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · have hilt : i < (stepW w g0).length := by
            change i < (w ++ [_]).length
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          simp only [hi, ↓reduceIte, foldl_getD_lt gs (stepW w g0) i hilt]
          exact (getD_app_lt w _ i hi).symm
        · simp only [hi, ↓reduceIte]
          exact getD_ge w i (Nat.le_of_not_lt hi)
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (stepW w g0).length + j' = w.length + (j' + 1) := by
          change (w ++ [_]).length + j' = w.length + (j' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (stepW w g0) j' g hj
  have wires_gate : ∀ (x : Fin n → Bool) (j : ℕ) (g : Gate),
      C.gates[j]? = some g →
      (C.wires (List.ofFn x)).getD (n + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
    intro x j g hj
    have h := foldl_gate C.gates (List.ofFn x) j g hj
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [hlen] at h
    exact h
  have wires_inp : ∀ (x : Fin n → Bool) (w : ℕ) (hw : w < n),
      (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro x w hw
    have h := foldl_getD_lt C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw)
    change (C.gates.foldl stepW (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]
  let stepRel : ℕ → ℕ → Prop := fun a b =>
    a < b ∧ ∃ (k : ℕ) (h : Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs
  have cone_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
      (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
    intro gs
    induction gs with
    | nil => intro cs j _; rfl
    | cons g0 gs ih =>
      intro cs j hj
      rw [List.foldl_cons]
      have hlt : j < (coneStep n cs g0).length := by
        change j < (cs ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (coneStep n cs g0) j hlt]
      change (cs ++ [_]).getD j [] = cs.getD j []
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have cone_gate : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ) (h : Gate),
      gs[k]? = some h →
      (gs.foldl (coneStep n) cs).getD (cs.length + k) [] =
        (h.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + k)))).flatMap
          (fun w => (w - n) :: (gs.foldl (coneStep n) cs).getD (w - n) []) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro cs k h hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : cs.length < (coneStep n cs g0).length := by
          change cs.length < (cs ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [cone_getD_lt gs (coneStep n cs g0) cs.length hlt]
        have hself : (coneStep n cs g0).getD cs.length [] =
            (g0.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) []) := by
          change (cs ++ [_]).getD cs.length [] = _
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwlt : w - n < cs.length := by omega
        have hwlt2 : w - n < (coneStep n cs g0).length := by
          change w - n < (cs ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [cone_getD_lt gs (coneStep n cs g0) (w - n) hwlt2]
        change (w - n) :: cs.getD (w - n) [] = (w - n) :: (cs ++ [_]).getD (w - n) []
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        have hlen : (coneStep n cs g0).length + k' = cs.length + (k' + 1) := by
          change (cs ++ [_]).length + k' = cs.length + (k' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (coneStep n cs g0) k' h hk
  have inCone_iff_rec : ∀ (k : ℕ) (h : Gate) (i : ℕ), C.gates[k]? = some h →
      (InCone n C i k ↔ ∃ w ∈ h.inputs, n ≤ w ∧ w < n + k ∧ (i = w - n ∨ InCone n C i (w - n))) := by
    intro k h i hk
    change i ∈ (C.gates.foldl (coneStep n) []).getD k [] ↔ _
    have hcg := cone_gate C.gates [] k h hk
    simp only [List.length_nil, Nat.zero_add] at hcg
    rw [hcg, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hi⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hi
      exact ⟨w, hw.1, hw.2.1, hw.2.2, hi⟩
    · rintro ⟨w, hwin, hle, hlt, hi⟩
      refine ⟨w, ?_, ?_⟩
      · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hwin, hle, hlt⟩
      · rw [List.mem_cons]; exact hi
  have transGen_ge : ∀ {a b : ℕ}, Relation.TransGen stepRel a b → a < b := by
    intro a b hab
    induction hab with
    | single h => exact h.1
    | tail _ hbc ih => exact lt_trans ih hbc.1
  have inCone_of_transGen : ∀ {a b : ℕ}, Relation.TransGen stepRel a b →
      ∀ i j : ℕ, a = n + i → b = n + j → InCone n C i j := by
    intro a b hab
    induction hab with
    | single h =>
      intro i j ha hb
      rcases h with ⟨hlt, k, g, hbk, hgk, hain⟩
      have hjk : j = k := by omega
      subst hjk
      rw [inCone_iff_rec j g i hgk]
      exact ⟨n + i, ha ▸ hain, by omega, by omega, Or.inl (by omega)⟩
    | tail hab hbc ih =>
      rename_i b' c'
      intro i j ha hc
      have hlt_a : a < b' := transGen_ge hab
      have hnb : n ≤ b' := by omega
      rcases hbc with ⟨hlt_b, k, g, hck, hgk, hbin⟩
      have hjk : j = k := by omega
      subst hjk
      have hib : InCone n C i (b' - n) := ih i (b' - n) ha (by omega)
      rw [inCone_iff_rec j g i hgk]
      exact ⟨b', hbin, hnb, by omega, Or.inr hib⟩
  have or_cone_input : ∀ (w : ℕ) (x : Fin n → Bool),
      w < n + C.gates.length →
      (C.wires (List.ofFn x)).getD w false = true →
      (∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → g.op = GateOp.and →
        Relation.ReflTransGen stepRel (n + k) w →
        (C.wires (List.ofFn x)).getD (n + k) false = false) →
      ∃ p : Fin n, x p = true ∧
        ∀ y : Fin n → Bool, y p = true → (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x hw_lt hw_true hno_and
      by_cases hw_n : w < n
      · refine ⟨⟨w, hw_n⟩, ?_, ?_⟩
        · rwa [wires_inp x w hw_n] at hw_true
        · intro y hy
          rw [wires_inp y w hw_n]
          exact hy
      · let k := w - n
        have hk_lt : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        obtain ⟨g, hgk⟩ : ∃ g, C.gates[k]? = some g := ⟨C.gates[k], List.getElem?_eq_getElem hk_lt⟩
        have hg_op := (hM_unfold g (List.mem_of_getElem? hgk)).1
        rcases hg_op with hand | hor
        · have hf := hno_and k g hgk hand (by rw [hwk])
          rw [hwk] at hw_true
          rw [hf] at hw_true
          exact Bool.noConfusion hw_true
        · have hwg := wires_gate x k g hgk
          rw [hwk] at hw_true
          rw [hw_true, hor] at hwg
          have hwg' : (g.inputs.map fun i =>
              if i < n + k then (C.wires (List.ofFn x)).getD i false else false).any id = true :=
            hwg.symm
          rw [List.any_eq_true] at hwg'
          rcases hwg' with ⟨_, hmem, hval⟩
          rw [List.mem_map] at hmem
          rcases hmem with ⟨a, hain, haeq⟩
          rw [id_eq] at hval
          rw [← haeq] at hval
          have ha_lt : a < n + k := by
            by_contra hge
            simp only [hge, ↓reduceIte] at hval
            exact Bool.noConfusion hval
          simp only [ha_lt, ↓reduceIte] at hval
          have ha_no_and : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
              Relation.ReflTransGen stepRel (n + k') a →
              (C.wires (List.ofFn x)).getD (n + k') false = false := by
            intro k' g' hgk' hand' hreach
            apply hno_and k' g' hgk' hand'
            rw [hwk]
            exact Relation.ReflTransGen.tail hreach ⟨ha_lt, k, g, rfl, hgk, hain⟩
          obtain ⟨p, hxp, hp_wire⟩ := ih a (by omega) x (by omega) hval ha_no_and
          refine ⟨p, hxp, ?_⟩
          intro y hyp
          rw [hwk, wires_gate y k g hgk, hor]
          change (g.inputs.map fun i =>
            if i < n + k then (C.wires (List.ofFn y)).getD i false else false).any id = true
          rw [List.any_eq_true]
          refine ⟨true, List.mem_map.mpr ⟨a, hain, ?_⟩, rfl⟩
          simp only [ha_lt, ↓reduceIte]
          exact hp_wire y hyp
  refine ⟨C, hM_unfold, hE, hMin, ?_⟩
  intro t g hgt hand
  have ht_lt : t < C.gates.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hgt
    simp at hgt
  obtain ⟨hsound, u0, v0, hadj0, howns0⟩ := hSO t g hgt hand
  have inline_of_owns : ∀ u v : Fin n, Owns n C t u v →
      (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
      ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
        Relation.TransGen stepRel (n + t') (n + t) →
        (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false := by
    intro u v ho
    refine ⟨ho.2.2.1, ?_⟩
    intro t' g' hgt' hand' htr
    have hlt_t' : t' < t := by
      have := transGen_ge htr
      omega
    have hcone : InCone n C t' t := inCone_of_transGen htr t' t rfl rfl
    have hgateAt : (PEqualNP.MetaComplexity.NestedCover.gateAt C t').op = GateOp.and := by
      change (C.gates.getD t' ⟨GateOp.or, []⟩).op = GateOp.and
      have hget : C.gates.getD t' ⟨GateOp.or, []⟩ = g' := by
        simp only [List.getD_eq_getElem?_getD, hgt', Option.getD_some]
      rw [hget]
      exact hand'
    exact ho.2.2.2 t' hlt_t' hcone hgateAt
  have h0_inline := inline_of_owns u0 v0 howns0
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hlen_le : g.inputs.length ≤ 2 := (hM_unfold g (List.mem_of_getElem? hgt)).2
  have hex_ab : ∃ a b : ℕ, g.inputs = [a, b] := by
    have hcases : g.inputs = [] ∨ (∃ a, g.inputs = [a]) ∨ (∃ a b, g.inputs = [a, b]) := by
      have aux : ∀ l : List ℕ, l.length ≤ 2 → l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b]) := by
        intro l hl
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨a, rfl⟩)
        · exact Or.inr (Or.inr ⟨a, b, rfl⟩)
        · simp at hl
      exact aux g.inputs hlen_le
    rcases hcases with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
    · have hf := wires_gate (fun _ : Fin n => false) t g hgt
      rw [hand, hins, eval_and] at hf
      simp only [List.map_nil, List.all_nil] at hf
      obtain ⟨i, j, _, hi, _⟩ := hsound (fun _ => false) hf
      exact Bool.noConfusion hi
    · have hf0 := wires_gate (fun k : Fin n => decide (k = u0 ∨ k = v0)) t g hgt
      rw [hand, hins, h0_inline.1, eval_and] at hf0
      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at hf0
      have ha_lt : a < n + t := by
        by_contra hge
        simp only [hge, ↓reduceIte] at hf0
        exact Bool.noConfusion hf0
      simp only [ha_lt, ↓reduceIte] at hf0
      have ha_no_and : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
          Relation.ReflTransGen stepRel (n + k') a →
          (C.wires (List.ofFn (fun k : Fin n => decide (k = u0 ∨ k = v0)))).getD (n + k') false = false := by
        intro k' g' hgk' hand' hreach
        apply h0_inline.2 k' g' hgk' hand'
        have hstep : stepRel a (n + t) := ⟨ha_lt, t, g, rfl, hgt, by rw [hins]; exact List.mem_singleton_self a⟩
        exact Relation.TransGen.tail' hreach hstep
      obtain ⟨p, _, hp_wire⟩ := or_cone_input a (fun k : Fin n => decide (k = u0 ∨ k = v0)) (by omega) hf0.symm ha_no_and
      let yp : Fin n → Bool := fun w => decide (w = p)
      have hta : (C.wires (List.ofFn yp)).getD (n + t) false = true := by
        rw [wires_gate yp t g hgt, hand, hins, eval_and]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, ha_lt, ↓reduceIte]
        exact hp_wire yp (by simp [yp])
      obtain ⟨i, j, hij, hi, hj⟩ := hsound yp hta
      simp only [yp, decide_eq_true_eq] at hi hj
      subst hi; subst hj
      exact False.elim (G.ne_of_adj hij rfl)
    · exact ⟨a, b, hins⟩
  obtain ⟨a, b, hab⟩ := hex_ab
  have split_owned : ∀ u v : Fin n, G.Adj u v →
      ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
        ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
          Relation.TransGen stepRel (n + t') (n + t) →
          (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) →
      ∃ x y : Fin n, ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧ G.Adj x y ∧
        (∀ z : Fin n → Bool, z x = true → (C.wires (List.ofFn z)).getD a false = true) ∧
        (∀ z : Fin n → Bool, z y = true → (C.wires (List.ofFn z)).getD b false = true) ∧
        a < n + t ∧ b < n + t := by
    intro u v huv hown
    have htrue := hown.1
    have hbelow := hown.2
    let puv : Fin n → Bool := fun k => decide (k = u ∨ k = v)
    have hwg := wires_gate puv t g hgt
    rw [htrue, hand, hab, eval_and] at hwg
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true] at hwg
    have hwg' := Bool.and_eq_true_iff.mp hwg.symm
    have ha_lt : a < n + t := by
      by_contra hge
      have h1 := hwg'.1
      simp only [hge, ↓reduceIte] at h1
      exact Bool.noConfusion h1
    have hb_lt : b < n + t := by
      by_contra hge
      have h2 := hwg'.2
      simp only [hge, ↓reduceIte] at h2
      exact Bool.noConfusion h2
    have ha_true : (C.wires (List.ofFn puv)).getD a false = true := by
      simpa only [ha_lt, ↓reduceIte] using hwg'.1
    have hb_true : (C.wires (List.ofFn puv)).getD b false = true := by
      simpa only [hb_lt, ↓reduceIte] using hwg'.2
    have ha_no : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
        Relation.ReflTransGen stepRel (n + k') a →
        (C.wires (List.ofFn puv)).getD (n + k') false = false := by
      intro k' g' hgk' hand' hreach
      exact hbelow k' g' hgk' hand'
        (Relation.TransGen.tail' hreach ⟨ha_lt, t, g, rfl, hgt, by rw [hab]; simp⟩)
    have hb_no : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
        Relation.ReflTransGen stepRel (n + k') b →
        (C.wires (List.ofFn puv)).getD (n + k') false = false := by
      intro k' g' hgk' hand' hreach
      exact hbelow k' g' hgk' hand'
        (Relation.TransGen.tail' hreach ⟨hb_lt, t, g, rfl, hgt, by rw [hab]; simp⟩)
    obtain ⟨pa, hpa_in, hpa_w⟩ := or_cone_input a puv (by omega) ha_true ha_no
    obtain ⟨pb, hpb_in, hpb_w⟩ := or_cone_input b puv (by omega) hb_true hb_no
    have hne : pa ≠ pb := by
      intro heq
      subst heq
      let yp : Fin n → Bool := fun w => decide (w = pa)
      have hta : (C.wires (List.ofFn yp)).getD (n + t) false = true := by
        rw [wires_gate yp t g hgt, hand, hab, eval_and]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, ha_lt, hb_lt, ↓reduceIte, Bool.and_eq_true]
        exact ⟨hpa_w yp (by simp [yp]), hpb_w yp (by simp [yp])⟩
      obtain ⟨i, j, hij, hi, hj⟩ := hsound yp hta
      simp only [yp, decide_eq_true_eq] at hi hj
      subst hi; subst hj
      exact G.ne_of_adj hij rfl
    simp only [puv, decide_eq_true_eq] at hpa_in hpb_in
    rcases hpa_in with rfl | rfl <;> rcases hpb_in with rfl | rfl
    · exact False.elim (hne rfl)
    · exact ⟨pa, pb, Or.inl ⟨rfl, rfl⟩, huv, hpa_w, hpb_w, ha_lt, hb_lt⟩
    · exact ⟨pa, pb, Or.inr ⟨rfl, rfl⟩, huv.symm, hpa_w, hpb_w, ha_lt, hb_lt⟩
    · exact False.elim (hne rfl)
  have pair_compat : ∀ (x1 y1 x2 y2 : Fin n),
      G.Adj x1 y1 → G.Adj x2 y2 →
      (∀ z : Fin n → Bool, z x1 = true → (C.wires (List.ofFn z)).getD a false = true) →
      (∀ z : Fin n → Bool, z y1 = true → (C.wires (List.ofFn z)).getD b false = true) →
      (∀ z : Fin n → Bool, z x2 = true → (C.wires (List.ofFn z)).getD a false = true) →
      (∀ z : Fin n → Bool, z y2 = true → (C.wires (List.ofFn z)).getD b false = true) →
      a < n + t → b < n + t →
      x1 = x2 ∨ y1 = y2 := by
    intro x1 y1 x2 y2 h12 h34 hx1 hy1 hx2 hy2 ha_lt hb_lt
    have adj_cross : ∀ (x y : Fin n),
        (∀ z : Fin n → Bool, z x = true → (C.wires (List.ofFn z)).getD a false = true) →
        (∀ z : Fin n → Bool, z y = true → (C.wires (List.ofFn z)).getD b false = true) →
        G.Adj x y := by
      intro x y hxw hyw
      let pxy : Fin n → Bool := fun k => decide (k = x ∨ k = y)
      have hta : (C.wires (List.ofFn pxy)).getD (n + t) false = true := by
        rw [wires_gate pxy t g hgt, hand, hab, eval_and]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, ha_lt, hb_lt, ↓reduceIte, Bool.and_eq_true]
        exact ⟨hxw pxy (by simp [pxy]), hyw pxy (by simp [pxy])⟩
      obtain ⟨i, j, hij, hi, hj⟩ := hsound pxy hta
      simp only [pxy, decide_eq_true_eq] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact False.elim (G.ne_of_adj hij rfl)
      · exact hij
      · exact hij.symm
      · exact False.elim (G.ne_of_adj hij rfl)
    have h14 : G.Adj x1 y2 := adj_cross x1 y2 hx1 hy2
    have h32 : G.Adj x2 y1 := adj_cross x2 y1 hx2 hy1
    exact hc4 x1 y1 x2 y2 h12 h32.symm h34 h14.symm
  obtain ⟨x0, y0, _, hxy0, hx0, hy0, ha_lt, hb_lt⟩ := split_owned u0 v0 hadj0 h0_inline
  by_cases hall_x0 : ∀ u v : Fin n, G.Adj u v →
      ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
        ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
          Relation.TransGen stepRel (n + t') (n + t) →
          (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) →
      u = x0 ∨ v = x0
  · exact ⟨x0, ⟨u0, v0, hadj0, h0_inline⟩, hall_x0⟩
  · push Not at hall_x0
    obtain ⟨u1, v1, hadj1, h1_inline, hu1_ne, hv1_ne⟩ := hall_x0
    obtain ⟨x1, y1, hxy1_eq, hxy1, hx1, hy1, _, _⟩ := split_owned u1 v1 hadj1 h1_inline
    have hx1_ne : x1 ≠ x0 := by
      rcases hxy1_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu1_ne
      · exact hv1_ne
    have hy1_eq : y1 = y0 := by
      rcases pair_compat x0 y0 x1 y1 hxy0 hxy1 hx0 hy0 hx1 hy1 ha_lt hb_lt with hxx | hyy
      · exact False.elim (hx1_ne hxx.symm)
      · exact hyy.symm
    subst hy1_eq
    refine ⟨y1, ⟨u0, v0, hadj0, h0_inline⟩, ?_⟩
    intro u v hadj h_inline
    obtain ⟨x, y, hxy_eq, hxy, hx, hy, _, _⟩ := split_owned u v hadj h_inline
    have hy_eq : y = y1 := by
      rcases pair_compat x0 y1 x y hxy0 hxy hx0 hy0 hx hy ha_lt hb_lt with hxx0 | hyy
      · rcases pair_compat x1 y1 x y hxy1 hxy hx1 hy1 hx hy ha_lt hb_lt with hxx1 | hyy
        · exact False.elim (hx1_ne (hxx1.trans hxx0.symm))
        · exact hyy.symm
      · exact hyy.symm
    rcases hxy_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr hy_eq
    · exact Or.inl hy_eq
