import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_547_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runGates (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

private lemma wires_eq_runGates (C : Circuit) (x : List Bool) :
    C.wires x = runGates C.gates x := rfl

private lemma runGates_nil (init : List Bool) : runGates [] init = init := rfl

private lemma runGates_append (gs₁ gs₂ : List Gate) (init : List Bool) :
    runGates (gs₁ ++ gs₂) init = runGates gs₂ (runGates gs₁ init) :=
  List.foldl_append

private lemma runGates_length (gs : List Gate) (init : List Bool) :
    (runGates gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [runGates]
  | cons g gs ih =>
    simp only [runGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [stepWire]
    omega

private lemma runGates_getD_prefix (gs₁ gs₂ : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < (runGates gs₁ init).length) :
    (runGates (gs₁ ++ gs₂) init).getD i false = (runGates gs₁ init).getD i false := by
  rw [runGates_append]
  induction gs₂ generalizing gs₁ init with
  | nil => rfl
  | cons g gs₂ ih =>
    have h1 : (runGates gs₁ init).length < (stepWire (runGates gs₁ init) g).length := by
      simp [stepWire]
    have hstep : (stepWire (runGates gs₁ init) g).getD i false = (runGates gs₁ init).getD i false := by
      rw [List.getD_eq_getElem _ _ (Nat.lt_trans hi h1), List.getD_eq_getElem _ _ hi]
      exact List.getElem_append_left hi
    have ih' := ih (gs₁ ++ [g]) init (by rw [runGates_append]; exact Nat.lt_trans hi h1)
    rw [runGates_append] at ih'
    change (runGates gs₂ (stepWire (runGates gs₁ init) g)).getD i false = (runGates gs₁ init).getD i false
    exact ih'.trans hstep

private lemma runGates_getD_step (gs : List Gate) (g : Gate) (init : List Bool) :
    (runGates (gs ++ [g]) init).getD (init.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (runGates gs init).getD i false) := by
  rw [runGates_append]
  change (stepWire (runGates gs init) g).getD (init.length + gs.length) false = _
  have hlen : (runGates gs init).length = init.length + gs.length := runGates_length gs init
  simp only [stepWire]
  rw [List.getD_eq_getElem _ _ (by simp [hlen])]
  simp [hlen]

private def legalGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def effInputs (lim : ℕ) (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => []
    | w :: _ => if w < lim then [w] else []
  | _ => g.inputs.filter (fun w => decide (w < lim))

private lemma effInputs_lt {lim : ℕ} {g : Gate} {w : ℕ} (hw : w ∈ effInputs lim g) :
    w < lim := by
  unfold effInputs at hw
  cases h : g.op with
  | not =>
    rw [h] at hw
    cases hi : g.inputs with
    | nil => simp [hi] at hw
    | cons u us =>
      rw [hi] at hw
      by_cases hu : u < lim
      · simp [hu] at hw; subst hw; exact hu
      · simp [hu] at hw
  | and | or | mod _ | maj =>
    rw [h] at hw
    exact of_decide_eq_true (List.mem_filter.mp hw).2

private lemma effInputs_mem_inputs {lim : ℕ} {g : Gate} {w : ℕ} (hw : w ∈ effInputs lim g) :
    w ∈ g.inputs := by
  unfold effInputs at hw
  cases h : g.op with
  | not =>
    rw [h] at hw
    cases hi : g.inputs with
    | nil => simp [hi] at hw
    | cons u us =>
      rw [hi] at hw
      by_cases hu : u < lim
      · simp [hu] at hw; subst hw; simp
      · simp [hu] at hw
  | and | or | mod _ | maj =>
    rw [h] at hw
    exact (List.mem_filter.mp hw).1

private lemma effInputs_not_unique {lim : ℕ} {g : Gate} (hnot : g.op = GateOp.not)
    {u v : ℕ} (hu : u ∈ effInputs lim g) (hv : v ∈ effInputs lim g) : u = v := by
  unfold effInputs at hu hv
  rw [hnot] at hu hv
  cases hi : g.inputs with
  | nil => simp [hi] at hu
  | cons w ws =>
    rw [hi] at hu hv
    by_cases hw : w < lim
    · simp [hw] at hu hv; exact hu.trans hv.symm
    · simp [hw] at hu

private lemma gate_eval_eq_of_eff (g : Gate) (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length)
    (heq : ∀ i ∈ effInputs w₁.length g, w₁.getD i false = w₂.getD i false) :
    g.op.eval (g.inputs.map fun i => w₁.getD i false) =
      g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
  cases hop : g.op with
  | not =>
    cases hi : g.inputs with
    | nil => rfl
    | cons u us =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      by_cases hu : u < w₁.length
      · have hmem : u ∈ effInputs w₁.length g := by simp [effInputs, hop, hi, hu]
        rw [heq u hmem]
      · have h1 : w₁.getD u false = false := List.getD_eq_default _ _ (Nat.le_of_not_gt hu)
        have h2 : w₂.getD u false = false := List.getD_eq_default _ _ (by omega)
        rw [h1, h2]
  | and | or | mod _ | maj =>
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hilt : i < w₁.length
    · exact heq i (by simp [effInputs, hop, hi, hilt])
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hilt),
          List.getD_eq_default _ _ (by omega)]

private def remapWire (t w : ℕ) : ℕ :=
  if w < t then w else w - 1

private def remapGate (t : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire t)⟩

private def dropDead (C : Circuit) (m j : ℕ) : Circuit :=
  ⟨(C.gates.eraseIdx j).map (remapGate (m + j)), remapWire (m + j) C.output⟩

private lemma dropDead_fanInTwo (C : Circuit) (hF : FanInTwo C) (m j : ℕ) :
    FanInTwo (dropDead C m j) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  have hmem : g' ∈ C.gates := List.mem_of_mem_eraseIdx hg'
  obtain ⟨hop, hlen⟩ := hF g' hmem
  exact ⟨hop, by simpa [remapGate] using hlen⟩

private lemma dropDead_size (C : Circuit) (m j : ℕ) (hj : j < C.gates.length) :
    (dropDead C m j).size + 1 = C.size := by
  simp only [Circuit.size, dropDead, List.length_map, List.length_eraseIdx_of_lt hj]
  omega

private lemma dropDead_eval (C : Circuit) (m j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ k : ℕ, j < k → (hk : k < C.gates.length) →
      m + j ∉ effInputs (m + k) C.gates[k])
    (hout : C.output ≠ m + j)
    (x : List Bool) (hx : x.length = m) :
    (dropDead C m j).eval x = C.eval x := by
  have hmain : ∀ k ≤ C.gates.length,
      (∀ i < m + k, i ≠ m + j →
        (runGates ((C.gates.take k).eraseIdx j |>.map (remapGate (m + j))) x).getD
          (remapWire (m + j) i) false =
        (runGates (C.gates.take k) x).getD i false) := by
    intro k hk
    induction k with
    | zero =>
      intro i hi hne
      simp only [List.take_zero, List.eraseIdx_nil, List.map_nil, runGates_nil]
      have hilt : i < m + j := by omega
      simp [remapWire, hilt]
    | succ k ih =>
      have hklt : k < C.gates.length := by omega
      have ih' := ih (Nat.le_of_lt hklt)
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
        List.take_succ_eq_append_getElem hklt
      have hlen_take : (C.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hklt)
      by_cases hkj : k = j
      · subst hkj
        have herase : (C.gates.take (k + 1)).eraseIdx k = C.gates.take k := by
          rw [htake, List.eraseIdx_append_of_length_le (by omega)]
          simp [hlen_take]
        have herase_k : (C.gates.take k).eraseIdx k = C.gates.take k :=
          List.eraseIdx_of_length_le (by omega)
        rw [herase]
        intro i hi hne
        have hilt : i < m + k := by omega
        have h1 := ih' i hilt hne
        rw [herase_k] at h1
        rw [h1, htake, runGates_getD_prefix (C.gates.take k) [C.gates[k]] x i
          (by rw [runGates_length, hx, hlen_take]; exact hilt)]
      · have herase : (C.gates.take (k + 1)).eraseIdx j =
            (C.gates.take k).eraseIdx j ++ [C.gates[k]] := by
          rw [htake]
          by_cases hjk : j < k
          · rw [List.eraseIdx_append_of_lt_length (by omega)]
          · rw [List.eraseIdx_append_of_length_le (by omega)]
            have h1 : (C.gates.take k).eraseIdx j = C.gates.take k :=
              List.eraseIdx_of_length_le (by omega)
            have h2 : [C.gates[k]].eraseIdx (j - (C.gates.take k).length) = [C.gates[k]] :=
              List.eraseIdx_of_length_le (by simp [hlen_take]; omega)
            rw [h1, h2]
        rw [herase, List.map_append, List.map_singleton, htake]
        set gs₁ := ((C.gates.take k).eraseIdx j).map (remapGate (m + j))
        have hgs₁_len : gs₁.length = if j < k then k - 1 else k := by
          simp only [gs₁, List.length_map]
          by_cases hjk : j < k
          · rw [List.length_eraseIdx_of_lt (by omega), hlen_take, ite_eq_left hjk]
          · rw [List.eraseIdx_of_length_le (by omega), hlen_take, ite_eq_right hjk]
        have hrun_gs₁ : (runGates gs₁ x).length = m + (if j < k then k - 1 else k) := by
          rw [runGates_length, hx, hgs₁_len]
        have hrun_orig : (runGates (C.gates.take k) x).length = m + k := by
          rw [runGates_length, hx, hlen_take]
        have hgate_eq :
            (remapGate (m + j) C.gates[k]).op.eval
              ((remapGate (m + j) C.gates[k]).inputs.map fun w => (runGates gs₁ x).getD w false) =
            C.gates[k].op.eval
              (C.gates[k].inputs.map fun w => (runGates (C.gates.take k) x).getD w false) := by
          have hval : ∀ w ∈ C.gates[k].inputs, w ≠ m + j →
              (runGates gs₁ x).getD (remapWire (m + j) w) false =
              (runGates (C.gates.take k) x).getD w false := by
            intro w _ hwn
            by_cases hwlt : w < m + k
            · exact ih' w hwlt hwn
            · have hge1 : (runGates gs₁ x).length ≤ remapWire (m + j) w := by
                rw [hrun_gs₁]
                unfold remapWire
                split_ifs <;> omega
              have hge2 : (runGates (C.gates.take k) x).length ≤ w := by
                rw [hrun_orig]; omega
              rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
          cases hop : C.gates[k].op with
          | not =>
            cases hin : C.gates[k].inputs with
            | nil => simp [remapGate, hop, hin, GateOp.eval]
            | cons u us =>
              simp only [remapGate, hop, hin, List.map_cons, GateOp.eval, List.headD_cons]
              by_cases hu : u = m + j
              · by_cases hjk : j < k
                · exfalso
                  apply hdead k hjk hklt
                  simp [effInputs, hop, hin, hu]
                  omega
                · have hge1 : (runGates gs₁ x).length ≤ remapWire (m + j) u := by
                    rw [hrun_gs₁, ite_eq_right hjk, hu]; unfold remapWire; split_ifs <;> omega
                  have hge2 : (runGates (C.gates.take k) x).length ≤ u := by
                    rw [hrun_orig, hu]; omega
                  rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
              · rw [hval u (by simp [hin]) hu]
          | and | or | mod _ | maj =>
            simp only [remapGate, hop, List.map_map]
            congr 1
            apply List.map_congr_left
            intro w hw
            change (runGates gs₁ x).getD (remapWire (m + j) w) false =
              (runGates (C.gates.take k) x).getD w false
            by_cases hwn : w = m + j
            · by_cases hjk : j < k
              · exfalso
                apply hdead k hjk hklt
                unfold effInputs
                rw [hop]
                exact List.mem_filter.mpr ⟨hwn ▸ hw, decide_eq_true (by omega)⟩
              · have hge1 : (runGates gs₁ x).length ≤ remapWire (m + j) w := by
                  rw [hrun_gs₁, ite_eq_right hjk, hwn]; unfold remapWire; split_ifs <;> omega
                have hge2 : (runGates (C.gates.take k) x).length ≤ w := by
                  rw [hrun_orig, hwn]; omega
                rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
            · exact hval w hw hwn
        intro i hi hne
        by_cases hik : i < m + k
        · have hri : remapWire (m + j) i < (runGates gs₁ x).length := by
            rw [hrun_gs₁]; unfold remapWire; split_ifs <;> omega
          rw [runGates_getD_prefix gs₁ [remapGate (m + j) C.gates[k]] x _ hri,
              runGates_getD_prefix (C.gates.take k) [C.gates[k]] x i (by rw [hrun_orig]; exact hik)]
          exact ih' i hik hne
        · have heq_i : i = m + k := by omega
          subst heq_i
          have hri_eq : remapWire (m + j) (m + k) = x.length + gs₁.length := by
            rw [hx, hgs₁_len]; unfold remapWire; split_ifs <;> omega
          have horig_eq : m + k = x.length + (C.gates.take k).length := by
            rw [hx, hlen_take]
          rw [hri_eq, runGates_getD_step, horig_eq, runGates_getD_step]
          exact hgate_eq
  have hfull := hmain C.gates.length le_rfl
  rw [List.take_length] at hfull
  change (runGates ((C.gates.eraseIdx j).map (remapGate (m + j))) x).getD
      (remapWire (m + j) C.output) false = (runGates C.gates x).getD C.output false
  by_cases ho : C.output < m + C.gates.length
  · exact hfull C.output ho hout
  · have hlen1 : (runGates ((C.gates.eraseIdx j).map (remapGate (m + j))) x).length =
        m + (C.gates.length - 1) := by
      rw [runGates_length, hx, List.length_map, List.length_eraseIdx_of_lt hj]
    have hlen2 : (runGates C.gates x).length = m + C.gates.length := by
      rw [runGates_length, hx]
    have hge1 : (runGates ((C.gates.eraseIdx j).map (remapGate (m + j))) x).length ≤
        remapWire (m + j) C.output := by
      rw [hlen1]; unfold remapWire; split_ifs <;> omega
    have hge2 : (runGates C.gates x).length ≤ C.output := by rw [hlen2]; omega
    rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]

private def evalSym (newWires : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => newWires.getD k false

private def lookupEnv (env : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ :=
  env.getD i (Sum.inl false)

private def simpStep (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    List Gate × List (Bool ⊕ ℕ) :=
  match g.op with
  | GateOp.and =>
    let vs := g.inputs.map (lookupEnv st.2)
    if Sum.inl false ∈ vs then
      (st.1, st.2 ++ [Sum.inl false])
    else
      let ks := vs.filterMap (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none)
      match ks with
      | [] => (st.1, st.2 ++ [Sum.inl true])
      | [k] => (st.1, st.2 ++ [Sum.inr k])
      | _ => (st.1 ++ [⟨GateOp.and, ks⟩], st.2 ++ [Sum.inr (n + st.1.length)])
  | GateOp.or =>
    let vs := g.inputs.map (lookupEnv st.2)
    if Sum.inl true ∈ vs then
      (st.1, st.2 ++ [Sum.inl true])
    else
      let ks := vs.filterMap (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none)
      match ks with
      | [] => (st.1, st.2 ++ [Sum.inl false])
      | [k] => (st.1, st.2 ++ [Sum.inr k])
      | _ => (st.1 ++ [⟨GateOp.or, ks⟩], st.2 ++ [Sum.inr (n + st.1.length)])
  | GateOp.not =>
    match g.inputs with
    | [] => (st.1, st.2 ++ [Sum.inl true])
    | i :: _ =>
      match lookupEnv st.2 i with
      | Sum.inl c => (st.1, st.2 ++ [Sum.inl (!c)])
      | Sum.inr k => (st.1 ++ [⟨GateOp.not, [k]⟩], st.2 ++ [Sum.inr (n + st.1.length)])
  | GateOp.mod _ => (st.1, st.2 ++ [Sum.inl false])
  | GateOp.maj => (st.1, st.2 ++ [Sum.inl false])

private def initEnv (n : ℕ) (cb : Bool) : List (Bool ⊕ ℕ) :=
  (List.range n).map Sum.inr ++ [Sum.inl false, Sum.inl cb]

private def simpPrefix (n : ℕ) (cb : Bool) (gs : List Gate) (k : ℕ) :
    List Gate × List (Bool ⊕ ℕ) :=
  (gs.take k).foldl (simpStep n) ([], initEnv n cb)

private lemma simpPrefix_succ (n : ℕ) (cb : Bool) (gs : List Gate) {k : ℕ} (hk : k < gs.length) :
    simpPrefix n cb gs (k + 1) = simpStep n (simpPrefix n cb gs k) gs[k] := by
  unfold simpPrefix
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

private lemma simpStep_not_nil (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.not) (hin : g.inputs = []) :
    simpStep n st g = (st.1, st.2 ++ [Sum.inl true]) := by
  cases g; simp only at hop hin; subst hop; subst hin; rfl

private lemma simpStep_not_cons (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.not) {u : ℕ} {us : List ℕ} (hin : g.inputs = u :: us) :
    simpStep n st g = match lookupEnv st.2 u with
      | Sum.inl c => (st.1, st.2 ++ [Sum.inl (!c)])
      | Sum.inr k => (st.1 ++ [⟨GateOp.not, [k]⟩], st.2 ++ [Sum.inr (n + st.1.length)]) := by
  cases g; simp only at hop hin; subst hop; subst hin; rfl

private lemma simpStep_env_length (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (simpStep n st g).2.length = st.2.length + 1 := by
  cases g with
  | mk op ins =>
    cases op with
    | and =>
      unfold simpStep; dsimp only
      split_ifs
      · simp
      · cases (ins.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
        | nil => simp
        | cons k ks => cases ks <;> simp
    | or =>
      unfold simpStep; dsimp only
      split_ifs
      · simp
      · cases (ins.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
        | nil => simp
        | cons k ks => cases ks <;> simp
    | not =>
      cases ins with
      | nil => simp [simpStep]
      | cons i is =>
        rw [simpStep_not_cons n st ⟨GateOp.not, i :: is⟩ rfl rfl]
        cases lookupEnv st.2 i <;> simp
    | mod _ => simp [simpStep]
    | maj => simp [simpStep]

private lemma simpStep_env_prefix (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (i : ℕ) (hi : i < st.2.length) :
    (simpStep n st g).2.getD i (Sum.inl false) = st.2.getD i (Sum.inl false) := by
  have hgrow : ∃ v, (simpStep n st g).2 = st.2 ++ [v] := by
    cases g with
    | mk op ins =>
      cases op with
      | and =>
        unfold simpStep; dsimp only
        split_ifs
        · exact ⟨_, rfl⟩
        · cases (ins.map (lookupEnv st.2)).filterMap
            (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
          | nil => exact ⟨_, rfl⟩
          | cons k ks => cases ks <;> exact ⟨_, rfl⟩
      | or =>
        unfold simpStep; dsimp only
        split_ifs
        · exact ⟨_, rfl⟩
        · cases (ins.map (lookupEnv st.2)).filterMap
            (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
          | nil => exact ⟨_, rfl⟩
          | cons k ks => cases ks <;> exact ⟨_, rfl⟩
      | not =>
        cases ins with
        | nil => exact ⟨_, rfl⟩
        | cons a as =>
          rw [simpStep_not_cons n st ⟨GateOp.not, a :: as⟩ rfl rfl]
          cases lookupEnv st.2 a <;> exact ⟨_, rfl⟩
      | mod _ => exact ⟨_, rfl⟩
      | maj => exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hgrow
  rw [hv, List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

private lemma simpStep_gates_le (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (simpStep n st g).1.length = st.1.length ∨ (simpStep n st g).1.length = st.1.length + 1 := by
  cases g with
  | mk op ins =>
    cases op with
    | and =>
      unfold simpStep; dsimp only
      split_ifs
      · exact Or.inl rfl
      · cases (ins.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
        | nil => exact Or.inl rfl
        | cons k ks =>
          cases ks with
          | nil => exact Or.inl rfl
          | cons k₂ ks₂ => exact Or.inr (by simp)
    | or =>
      unfold simpStep; dsimp only
      split_ifs
      · exact Or.inl rfl
      · cases (ins.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
        | nil => exact Or.inl rfl
        | cons k ks =>
          cases ks with
          | nil => exact Or.inl rfl
          | cons k₂ ks₂ => exact Or.inr (by simp)
    | not =>
      cases ins with
      | nil => exact Or.inl rfl
      | cons a as =>
        rw [simpStep_not_cons n st ⟨GateOp.not, a :: as⟩ rfl rfl]
        cases lookupEnv st.2 a with
        | inl _ => exact Or.inl rfl
        | inr _ => exact Or.inr (by simp)
    | mod _ => exact Or.inl rfl
    | maj => exact Or.inl rfl

private lemma simpPrefix_env_length (n : ℕ) (cb : Bool) (gs : List Gate) (k : ℕ)
    (hk : k ≤ gs.length) :
    (simpPrefix n cb gs k).2.length = n + 2 + k := by
  induction k with
  | zero =>
    simp [simpPrefix, initEnv]
  | succ k ih =>
    rw [simpPrefix_succ n cb gs (by omega), simpStep_env_length, ih (by omega)]
    omega

private lemma simpPrefix_env_stable (n : ℕ) (cb : Bool) (gs : List Gate)
    {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) (hk₂ : k₂ ≤ gs.length) (i : ℕ) (hi : i < n + 2 + k₁) :
    lookupEnv (simpPrefix n cb gs k₂).2 i = lookupEnv (simpPrefix n cb gs k₁).2 i := by
  induction hle with
  | refl => rfl
  | @step m hle ih =>
    have hkm : k₁ ≤ m := hle
    have hm : m < gs.length := by omega
    have hlen : (simpPrefix n cb gs m).2.length = n + 2 + m :=
      simpPrefix_env_length n cb gs m (Nat.le_of_lt hm)
    unfold lookupEnv
    rw [simpPrefix_succ n cb gs hm, simpStep_env_prefix n _ _ i (by rw [hlen]; omega)]
    exact ih (Nat.le_of_lt hm)

private lemma simpPrefix_sound (n : ℕ) (cb : Bool) (gs : List Gate)
    (hF : ∀ g ∈ gs, legalGate g) :
    ∀ k ≤ gs.length,
      (∀ g ∈ (simpPrefix n cb gs k).1, legalGate g) ∧
      (∀ s ∈ (simpPrefix n cb gs k).2, ∀ w, s = Sum.inr w →
        w < n + (simpPrefix n cb gs k).1.length) ∧
      ∀ x : Fin n → Bool,
        ∀ i : ℕ,
          (runGates (gs.take k) (List.ofFn x ++ [false, cb])).getD i false =
            evalSym (runGates (simpPrefix n cb gs k).1 (List.ofFn x))
              (lookupEnv (simpPrefix n cb gs k).2 i) := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨by intro g' hg'; exact False.elim ((List.not_mem_nil) hg'), ?_, ?_⟩
    · intro s hs w hw
      simp only [simpPrefix, List.take_zero, List.foldl_nil, initEnv, List.mem_append,
        List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨r, hr, rfl⟩ | rfl | rfl
      · cases hw; simp [simpPrefix, hr]
      · cases hw
      · cases hw
    · intro x i
      simp only [List.take_zero, runGates_nil, simpPrefix, List.foldl_nil, lookupEnv, initEnv]
      by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_append_left (by simp [hi]),
            List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_append_left (by simp [hi])]
        simp [evalSym, List.getD_eq_getElem, hi]
      · by_cases hi0 : i = n
        · subst hi0
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp),
              List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
          simp [evalSym]
        · by_cases hi1 : i = n + 1
          · subst hi1
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp),
                List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
            simp [evalSym]
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
            rfl
  | succ k ih =>
    have hklt : k < gs.length := by omega
    obtain ⟨hlegal, hbd, heval⟩ := ih (Nat.le_of_lt hklt)
    set st := simpPrefix n cb gs k
    set g := gs[k]
    have hg : legalGate g := hF g (List.getElem_mem hklt)
    have htake : gs.take (k + 1) = gs.take k ++ [g] := List.take_succ_eq_append_getElem hklt
    have hnext : simpPrefix n cb gs (k + 1) = simpStep n st g :=
      simpPrefix_succ n cb gs hklt
    have hst_len : st.2.length = n + 2 + k := simpPrefix_env_length n cb gs k (Nat.le_of_lt hklt)
    have hstep_len : (simpStep n st g).2.length = n + 2 + k + 1 := by
      rw [simpStep_env_length, hst_len]
    have hbd_lookup : ∀ w j, lookupEnv st.2 w = Sum.inr j → j < n + st.1.length := by
      intro w j hw
      unfold lookupEnv at hw
      by_cases hlt : w < st.2.length
      · rw [List.getD_eq_getElem _ _ hlt] at hw
        exact hbd _ (List.getElem_mem hlt) j hw
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hlt)] at hw
        cases hw
    have hstep_check :
        (∀ g' ∈ (simpStep n st g).1, legalGate g') ∧
        (∀ s ∈ (simpStep n st g).2, ∀ w, s = Sum.inr w → w < n + (simpStep n st g).1.length) ∧
        ∀ x : Fin n → Bool,
          (runGates (gs.take k ++ [g]) (List.ofFn x ++ [false, cb])).getD (n + 2 + k) false =
            evalSym (runGates (simpStep n st g).1 (List.ofFn x))
              (lookupEnv (simpStep n st g).2 (n + 2 + k)) ∧
          ∀ w < n + st.1.length,
            (runGates (simpStep n st g).1 (List.ofFn x)).getD w false =
              (runGates st.1 (List.ofFn x)).getD w false := by
      have hlen_orig : (List.ofFn (fun i : Fin n => i) |>.length) = n := by simp
      have horig_step : ∀ x : Fin n → Bool,
          (runGates (gs.take k ++ [g]) (List.ofFn x ++ [false, cb])).getD (n + 2 + k) false =
            g.op.eval (g.inputs.map fun i => evalSym (runGates st.1 (List.ofFn x)) (lookupEnv st.2 i)) := by
        intro x
        have hlenx : (List.ofFn x ++ [false, cb]).length + (gs.take k).length = n + 2 + k := by
          simp [List.length_take_of_le (Nat.le_of_lt hklt)]
        rw [← hlenx, runGates_getD_step]
        congr 1
        apply List.map_congr_left
        intro i _
        exact heval x i
      have hnew_unchanged : ∀ (x : Fin n → Bool) (g' : Gate) (w : ℕ), w < n + st.1.length →
          (runGates (st.1 ++ [g']) (List.ofFn x)).getD w false =
            (runGates st.1 (List.ofFn x)).getD w false := by
        intro x g' w hw
        exact runGates_getD_prefix st.1 [g'] (List.ofFn x) w (by rw [runGates_length]; simp; exact hw)
      have hlookup_last : ∀ v, (simpStep n st g).2 = st.2 ++ [v] →
          lookupEnv (simpStep n st g).2 (n + 2 + k) = v := by
        intro v hv
        unfold lookupEnv
        rw [hv, List.getD_eq_getElem _ _ (by simp [hst_len])]
        simp [hst_len]
      have hsame_gate : ∀ (v : Bool ⊕ ℕ),
          (simpStep n st g) = (st.1, st.2 ++ [v]) →
          (∀ w, v = Sum.inr w → w < n + st.1.length) →
          (∀ x : Fin n → Bool,
            g.op.eval (g.inputs.map fun i => evalSym (runGates st.1 (List.ofFn x)) (lookupEnv st.2 i)) =
              evalSym (runGates st.1 (List.ofFn x)) v) →
          (∀ g' ∈ (simpStep n st g).1, legalGate g') ∧
          (∀ s ∈ (simpStep n st g).2, ∀ w, s = Sum.inr w → w < n + (simpStep n st g).1.length) ∧
          ∀ x : Fin n → Bool,
            (runGates (gs.take k ++ [g]) (List.ofFn x ++ [false, cb])).getD (n + 2 + k) false =
              evalSym (runGates (simpStep n st g).1 (List.ofFn x))
                (lookupEnv (simpStep n st g).2 (n + 2 + k)) ∧
            ∀ w < n + st.1.length,
              (runGates (simpStep n st g).1 (List.ofFn x)).getD w false =
                (runGates st.1 (List.ofFn x)).getD w false := by
        intro v hst_eq hvbd hveq
        refine ⟨by rw [hst_eq]; exact hlegal, ?_, ?_⟩
        · rw [hst_eq]
          intro s hs w hw
          rcases List.mem_append.mp hs with hs | hs
          · exact hbd s hs w hw
          · rw [List.mem_singleton.mp hs] at hw
            exact hvbd w hw
        · intro x
          refine ⟨?_, fun w _ => by rw [hst_eq]⟩
          rw [horig_step x, hlookup_last v (congrArg Prod.snd hst_eq), hst_eq]
          exact hveq x
      have hadd_gate : ∀ (g' : Gate),
          (simpStep n st g) = (st.1 ++ [g'], st.2 ++ [Sum.inr (n + st.1.length)]) →
          legalGate g' →
          (∀ x : Fin n → Bool,
            g.op.eval (g.inputs.map fun i => evalSym (runGates st.1 (List.ofFn x)) (lookupEnv st.2 i)) =
              g'.op.eval (g'.inputs.map fun w => (runGates st.1 (List.ofFn x)).getD w false)) →
          (∀ g' ∈ (simpStep n st g).1, legalGate g') ∧
          (∀ s ∈ (simpStep n st g).2, ∀ w, s = Sum.inr w → w < n + (simpStep n st g).1.length) ∧
          ∀ x : Fin n → Bool,
            (runGates (gs.take k ++ [g]) (List.ofFn x ++ [false, cb])).getD (n + 2 + k) false =
              evalSym (runGates (simpStep n st g).1 (List.ofFn x))
                (lookupEnv (simpStep n st g).2 (n + 2 + k)) ∧
            ∀ w < n + st.1.length,
              (runGates (simpStep n st g).1 (List.ofFn x)).getD w false =
                (runGates st.1 (List.ofFn x)).getD w false := by
        intro g' hst_eq hg' hge
        refine ⟨?_, ?_, ?_⟩
        · rw [hst_eq]
          intro g'' hg''
          rcases List.mem_append.mp hg'' with hg'' | hg''
          · exact hlegal g'' hg''
          · rw [List.mem_singleton.mp hg'']; exact hg'
        · rw [hst_eq]
          intro s hs w hw
          simp only [List.length_append, List.length_singleton]
          rcases List.mem_append.mp hs with hs | hs
          · have := hbd s hs w hw; omega
          · rw [List.mem_singleton.mp hs] at hw
            cases hw; omega
        · intro x
          refine ⟨?_, fun w hw => by rw [hst_eq]; exact hnew_unchanged x g' w hw⟩
          rw [horig_step x, hlookup_last _ (congrArg Prod.snd hst_eq), hst_eq]
          simp only [evalSym]
          have hlenn : (List.ofFn x).length + st.1.length = n + st.1.length := by simp
          rw [← hlenn, runGates_getD_step]
          exact hge x
      rcases hg.1 with hop | hop | hop
      · set vs := g.inputs.map (lookupEnv st.2)
        by_cases hfalse : Sum.inl false ∈ vs
        · apply hsame_gate (Sum.inl false)
          · simp [simpStep, hop, vs, hfalse]
          · intro w hw; cases hw
          · intro x
            rw [hop, GateOp.eval, evalSym, List.all_eq_false]
            obtain ⟨i, hi, hvi⟩ := List.mem_map.mp hfalse
            exact ⟨false, List.mem_map.mpr ⟨i, hi, by rw [hvi]; rfl⟩, by decide⟩
        · set ks := vs.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
          have hall_eq : ∀ x : Fin n → Bool,
              (g.inputs.map fun i => evalSym (runGates st.1 (List.ofFn x)) (lookupEnv st.2 i)).all id =
                (ks.map fun w => (runGates st.1 (List.ofFn x)).getD w false).all id := by
            intro x
            have hmap : (g.inputs.map fun i => evalSym (runGates st.1 (List.ofFn x)) (lookupEnv st.2 i)) =
                vs.map (evalSym (runGates st.1 (List.ofFn x))) := by
              simp [vs, List.map_map, Function.comp_def]
            rw [hmap]
            have haux : ∀ l : List (Bool ⊕ ℕ), Sum.inl false ∉ l →
                (l.map (evalSym (runGates st.1 (List.ofFn x)))).all id =
                  ((l.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)).map
                    fun w => (runGates st.1 (List.ofFn x)).getD w false).all id := by
              intro l hl
              induction l with
              | nil => rfl
              | cons s ls ih =>
                have hne : s ≠ Sum.inl false := fun h => hl (by simp [h])
                have hls : Sum.inl false ∉ ls := fun h => hl (List.mem_cons_of_mem _ h)
                cases s with
                | inl b =>
                  cases b
                  · exact absurd rfl hne
                  · simp [evalSym, ih hls]
                | inr w =>
                  simp [evalSym, ih hls]
            exact haux vs hfalse
          have hks_bd : ∀ w ∈ ks, w < n + st.1.length := by
            intro w hw
            obtain ⟨s, hs, hsw⟩ := List.mem_filterMap.mp hw
            cases s with
            | inl _ => cases hsw
            | inr u =>
              cases hsw
              obtain ⟨i, _, hi⟩ := List.mem_map.mp hs
              exact hbd_lookup i w hi
          have hks_len : ks.length ≤ 2 := by
            calc ks.length ≤ vs.length := List.length_filterMap_le _ _
              _ = g.inputs.length := List.length_map _
              _ ≤ 2 := hg.2
          cases hks : ks with
          | nil =>
            apply hsame_gate (Sum.inl true)
            · simp [simpStep, hop, vs, hfalse, ks, hks]
            · intro w hw; cases hw
            · intro x; rw [hop, GateOp.eval, hall_eq x, hks]; rfl
          | cons w₁ ws =>
            cases ws with
            | nil =>
              apply hsame_gate (Sum.inr w₁)
              · simp [simpStep, hop, vs, hfalse, ks, hks]
              · intro w hw; cases hw; exact hks_bd w₁ (by simp [hks])
              · intro x; rw [hop, GateOp.eval, hall_eq x, hks]; simp [evalSym]
            | cons w₂ ws₂ =>
              apply hadd_gate ⟨GateOp.and, w₁ :: w₂ :: ws₂⟩
              · simp [simpStep, hop, vs, hfalse, ks, hks]
              · exact ⟨Or.inl rfl, hks ▸ hks_len⟩
              · intro x; rw [hop, GateOp.eval, hall_eq x, hks]; rfl
      · set vs := g.inputs.map (lookupEnv st.2)
        by_cases htrue : Sum.inl true ∈ vs
        · apply hsame_gate (Sum.inl true)
          · simp [simpStep, hop, vs, htrue]
          · intro w hw; cases hw
          · intro x
            rw [hop, GateOp.eval, evalSym, List.any_eq_true]
            obtain ⟨i, hi, hvi⟩ := List.mem_map.mp htrue
            exact ⟨true, List.mem_map.mpr ⟨i, hi, by rw [hvi]; rfl⟩, rfl⟩
        · set ks := vs.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
          have hany_eq : ∀ x : Fin n → Bool,
              (g.inputs.map fun i => evalSym (runGates st.1 (List.ofFn x)) (lookupEnv st.2 i)).any id =
                (ks.map fun w => (runGates st.1 (List.ofFn x)).getD w false).any id := by
            intro x
            have hmap : (g.inputs.map fun i => evalSym (runGates st.1 (List.ofFn x)) (lookupEnv st.2 i)) =
                vs.map (evalSym (runGates st.1 (List.ofFn x))) := by
              simp [vs, List.map_map, Function.comp_def]
            rw [hmap]
            have haux : ∀ l : List (Bool ⊕ ℕ), Sum.inl true ∉ l →
                (l.map (evalSym (runGates st.1 (List.ofFn x)))).any id =
                  ((l.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)).map
                    fun w => (runGates st.1 (List.ofFn x)).getD w false).any id := by
              intro l hl
              induction l with
              | nil => rfl
              | cons s ls ih =>
                have hne : s ≠ Sum.inl true := fun h => hl (by simp [h])
                have hls : Sum.inl true ∉ ls := fun h => hl (List.mem_cons_of_mem _ h)
                cases s with
                | inl b =>
                  cases b
                  · simp [evalSym, ih hls]
                  · exact absurd rfl hne
                | inr w =>
                  simp [evalSym, ih hls]
            exact haux vs htrue
          have hks_bd : ∀ w ∈ ks, w < n + st.1.length := by
            intro w hw
            obtain ⟨s, hs, hsw⟩ := List.mem_filterMap.mp hw
            cases s with
            | inl _ => cases hsw
            | inr u =>
              cases hsw
              obtain ⟨i, _, hi⟩ := List.mem_map.mp hs
              exact hbd_lookup i w hi
          have hks_len : ks.length ≤ 2 := by
            calc ks.length ≤ vs.length := List.length_filterMap_le _ _
              _ = g.inputs.length := List.length_map _
              _ ≤ 2 := hg.2
          cases hks : ks with
          | nil =>
            apply hsame_gate (Sum.inl false)
            · simp [simpStep, hop, vs, htrue, ks, hks]
            · intro w hw; cases hw
            · intro x; rw [hop, GateOp.eval, hany_eq x, hks]; rfl
          | cons w₁ ws =>
            cases ws with
            | nil =>
              apply hsame_gate (Sum.inr w₁)
              · simp [simpStep, hop, vs, htrue, ks, hks]
              · intro w hw; cases hw; exact hks_bd w₁ (by simp [hks])
              · intro x; rw [hop, GateOp.eval, hany_eq x, hks]; simp [evalSym]
            | cons w₂ ws₂ =>
              apply hadd_gate ⟨GateOp.or, w₁ :: w₂ :: ws₂⟩
              · simp [simpStep, hop, vs, htrue, ks, hks]
              · exact ⟨Or.inr (Or.inl rfl), hks ▸ hks_len⟩
              · intro x; rw [hop, GateOp.eval, hany_eq x, hks]; rfl
      · cases hin : g.inputs with
        | nil =>
          apply hsame_gate (Sum.inl true)
          · exact simpStep_not_nil n st g hop hin
          · intro w hw; cases hw
          · intro x; rw [hop, hin]; rfl
        | cons u us =>
          cases hlu : lookupEnv st.2 u with
          | inl c =>
            apply hsame_gate (Sum.inl (!c))
            · rw [simpStep_not_cons n st g hop hin, hlu]
            · intro w hw; cases hw
            · intro x; rw [hop, hin, GateOp.eval, List.map_cons, List.headD_cons, hlu]; rfl
          | inr w =>
            apply hadd_gate ⟨GateOp.not, [w]⟩
            · rw [simpStep_not_cons n st g hop hin, hlu]
            · exact ⟨Or.inr (Or.inr rfl), by simp⟩
            · intro x; rw [hop, hin, GateOp.eval, List.map_cons, List.headD_cons, hlu]; rfl
    rw [hnext]
    refine ⟨hstep_check.1, hstep_check.2.1, fun x i => ?_⟩
    rw [htake]
    by_cases hi : i < n + 2 + k
    · have hlen_orig : (runGates (gs.take k) (List.ofFn x ++ [false, cb])).length = n + 2 + k := by
        rw [runGates_length]; simp [List.length_take_of_le (Nat.le_of_lt hklt)]
      rw [runGates_getD_prefix (gs.take k) [g] _ i (by rw [hlen_orig]; exact hi)]
      have hlu_eq : lookupEnv (simpStep n st g).2 i = lookupEnv st.2 i :=
        simpStep_env_prefix n st g i (by rw [hst_len]; exact hi)
      rw [hlu_eq, heval x i]
      cases hval : lookupEnv st.2 i with
      | inl c => rfl
      | inr w =>
        simp only [evalSym]
        exact ((hstep_check.2.2 x).2 w (hbd_lookup i w hval)).symm
    · by_cases heq : i = n + 2 + k
      · subst heq
        exact (hstep_check.2.2 x).1
      · have hge1 : (runGates (gs.take k ++ [g]) (List.ofFn x ++ [false, cb])).length ≤ i := by
          rw [runGates_length]; simp [List.length_take_of_le (Nat.le_of_lt hklt)]; omega
        have hge2 : (simpStep n st g).2.length ≤ i := by rw [hstep_len]; omega
        rw [List.getD_eq_default _ _ hge1]
        unfold lookupEnv
        rw [List.getD_eq_default _ _ hge2]
        rfl

private def isElim (n : ℕ) (cb : Bool) (gs : List Gate) (j : ℕ) : Bool :=
  decide ((simpPrefix n cb gs (j + 1)).1.length = (simpPrefix n cb gs j).1.length)

private lemma simpPrefix_count (n : ℕ) (cb : Bool) (gs : List Gate) (k : ℕ)
    (hk : k ≤ gs.length) :
    (simpPrefix n cb gs k).1.length +
      ((Finset.range k).filter (fun j => isElim n cb gs j = true)).card = k := by
  induction k with
  | zero => simp [simpPrefix]
  | succ k ih =>
    have hklt : k < gs.length := by omega
    have ih' := ih (Nat.le_of_lt hklt)
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnext : simpPrefix n cb gs (k + 1) = simpStep n (simpPrefix n cb gs k) gs[k] :=
      simpPrefix_succ n cb gs hklt
    have hle := simpStep_gates_le n (simpPrefix n cb gs k) gs[k]
    rw [← hnext] at hle
    have hnotmem : k ∉ (Finset.range k).filter (fun j => isElim n cb gs j = true) := by
      simp
    by_cases he : (simpPrefix n cb gs (k + 1)).1.length = (simpPrefix n cb gs k).1.length
    · have his : isElim n cb gs k = true := by simp [isElim, he]
      rw [ite_eq_left his, Finset.card_insert_of_notMem hnotmem]
      omega
    · have his : ¬ (isElim n cb gs k = true) := by simp [isElim, he]
      have hsucc : (simpPrefix n cb gs (k + 1)).1.length = (simpPrefix n cb gs k).1.length + 1 :=
        hle.resolve_left he
      rw [ite_eq_right his]
      omega

private lemma elim_of_const_input (n : ℕ) (cb : Bool) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hlg : legalGate gs[j])
    (w : ℕ) (hw : w ∈ effInputs (n + 2 + j) gs[j])
    (c : Bool) (hc : lookupEnv (simpPrefix n cb gs gs.length).2 w = Sum.inl c) :
    isElim n cb gs j = true := by
  have hwlt : w < n + 2 + j := effInputs_lt hw
  have hcw : lookupEnv (simpPrefix n cb gs j).2 w = Sum.inl c := by
    rw [← simpPrefix_env_stable n cb gs (Nat.le_of_lt hj) le_rfl w hwlt]
    exact hc
  have hnext : simpPrefix n cb gs (j + 1) = simpStep n (simpPrefix n cb gs j) gs[j] :=
    simpPrefix_succ n cb gs hj
  unfold isElim
  rw [decide_eq_true_eq, hnext]
  set st := simpPrefix n cb gs j
  rcases hlg.1 with hop | hop | hop
  · have hmem_in : w ∈ gs[j].inputs := effInputs_mem_inputs hw
    simp only [simpStep, hop]
    split_ifs with hf
    · rfl
    · have hlen_ks : ((gs[j].inputs.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none)).length ≤ 1 := by
        have hlen2 : gs[j].inputs.length ≤ 2 := hlg.2
        cases hin : gs[j].inputs with
        | nil => simp [hin] at hmem_in
        | cons u₁ us =>
          cases us with
          | nil =>
            simp [hin] at hmem_in
            subst hmem_in
            simp [hcw]
          | cons u₂ us₂ =>
            cases us₂ with
            | nil =>
              simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hmem_in
              rcases hmem_in with rfl | rfl
              · simp [hcw]; cases lookupEnv st.2 u₂ <;> simp
              · simp [hcw]; cases lookupEnv st.2 u₁ <;> simp
            | cons _ _ => simp [hin] at hlen2
      cases hks : (gs[j].inputs.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
      | nil => rfl
      | cons k₁ ks =>
        cases ks with
        | nil => rfl
        | cons k₂ ks₂ => rw [hks] at hlen_ks; simp at hlen_ks
  · have hmem_in : w ∈ gs[j].inputs := effInputs_mem_inputs hw
    simp only [simpStep, hop]
    split_ifs with ht
    · rfl
    · have hlen_ks : ((gs[j].inputs.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none)).length ≤ 1 := by
        have hlen2 : gs[j].inputs.length ≤ 2 := hlg.2
        cases hin : gs[j].inputs with
        | nil => simp [hin] at hmem_in
        | cons u₁ us =>
          cases us with
          | nil =>
            simp [hin] at hmem_in
            subst hmem_in
            simp [hcw]
          | cons u₂ us₂ =>
            cases us₂ with
            | nil =>
              simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hmem_in
              rcases hmem_in with rfl | rfl
              · simp [hcw]; cases lookupEnv st.2 u₂ <;> simp
              · simp [hcw]; cases lookupEnv st.2 u₁ <;> simp
            | cons _ _ => simp [hin] at hlen2
      cases hks : (gs[j].inputs.map (lookupEnv st.2)).filterMap
          (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) with
      | nil => rfl
      | cons k₁ ks =>
        cases ks with
        | nil => rfl
        | cons k₂ ks₂ => rw [hks] at hlen_ks; simp at hlen_ks
  · unfold effInputs at hw
    rw [hop] at hw
    cases hin : gs[j].inputs with
    | nil => simp [hin] at hw
    | cons u us =>
      rw [hin] at hw
      by_cases hu : u < n + 2 + j
      · simp [hu] at hw
        subst hw
        change lookupEnv st.2 w = Sum.inl c at hcw
        rw [simpStep_not_cons n st gs[j] hop hin, hcw]
      · simp [hu] at hw

private lemma const_of_all_const_inputs (n : ℕ) (cb : Bool) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hlg : legalGate gs[j])
    (hall : ∀ w ∈ effInputs (n + 2 + j) gs[j],
      ∃ c : Bool, lookupEnv (simpPrefix n cb gs gs.length).2 w = Sum.inl c) :
    ∃ c : Bool, lookupEnv (simpPrefix n cb gs gs.length).2 (n + 2 + j) = Sum.inl c := by
  have hnext : simpPrefix n cb gs (j + 1) = simpStep n (simpPrefix n cb gs j) gs[j] :=
    simpPrefix_succ n cb gs hj
  have hst_len : (simpPrefix n cb gs j).2.length = n + 2 + j :=
    simpPrefix_env_length n cb gs j (Nat.le_of_lt hj)
  rw [simpPrefix_env_stable n cb gs (Nat.succ_le_of_lt hj) le_rfl (n + 2 + j) (by omega), hnext]
  set st := simpPrefix n cb gs j
  have hlast : ∀ v, (simpStep n st gs[j]).2 = st.2 ++ [v] →
      lookupEnv (simpStep n st gs[j]).2 (n + 2 + j) = v := by
    intro v hv
    unfold lookupEnv
    rw [hv, List.getD_eq_getElem _ _ (by simp [hst_len])]
    simp [hst_len]
  rcases hlg.1 with hop | hop | hop
  · have hall_and : ∀ w ∈ gs[j].inputs, ∃ c : Bool, lookupEnv st.2 w = Sum.inl c := by
      intro w hw
      by_cases hwlt : w < n + 2 + j
      · obtain ⟨c, hc⟩ := hall w (by simp [effInputs, hop, hw, hwlt])
        rw [simpPrefix_env_stable n cb gs (Nat.le_of_lt hj) le_rfl w hwlt] at hc
        exact ⟨c, hc⟩
      · exact ⟨false, List.getD_eq_default _ _ (by rw [hst_len]; omega)⟩
    have hks_nil : (gs[j].inputs.map (lookupEnv st.2)).filterMap
        (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro k hk
      obtain ⟨s, hs, hsk⟩ := List.mem_filterMap.mp hk
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
      obtain ⟨c, hc⟩ := hall_and w hw
      rw [hc] at hsk; cases hsk
    by_cases hf : Sum.inl false ∈ gs[j].inputs.map (lookupEnv st.2)
    · refine ⟨false, hlast _ ?_⟩; simp [simpStep, hop, hf]
    · refine ⟨true, hlast _ ?_⟩; simp [simpStep, hop, hf, hks_nil]
  · have hall_or : ∀ w ∈ gs[j].inputs, ∃ c : Bool, lookupEnv st.2 w = Sum.inl c := by
      intro w hw
      by_cases hwlt : w < n + 2 + j
      · obtain ⟨c, hc⟩ := hall w (by simp [effInputs, hop, hw, hwlt])
        rw [simpPrefix_env_stable n cb gs (Nat.le_of_lt hj) le_rfl w hwlt] at hc
        exact ⟨c, hc⟩
      · exact ⟨false, List.getD_eq_default _ _ (by rw [hst_len]; omega)⟩
    have hks_nil : (gs[j].inputs.map (lookupEnv st.2)).filterMap
        (fun s => match s with | Sum.inr k => some k | Sum.inl _ => none) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro k hk
      obtain ⟨s, hs, hsk⟩ := List.mem_filterMap.mp hk
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
      obtain ⟨c, hc⟩ := hall_or w hw
      rw [hc] at hsk; cases hsk
    by_cases ht : Sum.inl true ∈ gs[j].inputs.map (lookupEnv st.2)
    · refine ⟨true, hlast _ ?_⟩; simp [simpStep, hop, ht]
    · refine ⟨false, hlast _ ?_⟩; simp [simpStep, hop, ht, hks_nil]
  · cases hin : gs[j].inputs with
    | nil =>
      refine ⟨true, hlast _ ?_⟩
      rw [simpStep_not_nil n st gs[j] hop hin]
    | cons u us =>
      by_cases hu : u < n + 2 + j
      · obtain ⟨c, hc⟩ := hall u (by unfold effInputs; rw [hop, hin]; simp [hu])
        rw [simpPrefix_env_stable n cb gs (Nat.le_of_lt hj) le_rfl u hu] at hc
        change lookupEnv st.2 u = Sum.inl c at hc
        refine ⟨!c, hlast _ ?_⟩
        rw [simpStep_not_cons n st gs[j] hop hin, hc]
      · have hlu : lookupEnv st.2 u = Sum.inl false :=
          List.getD_eq_default _ _ (by rw [hst_len]; omega)
        refine ⟨true, hlast _ ?_⟩
        rw [simpStep_not_cons n st gs[j] hop hin, hlu]; rfl

private lemma const_of_kill_input (n : ℕ) (cb : Bool) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (_hlg : legalGate gs[j])
    (w : ℕ) (hw : w ∈ effInputs (n + 2 + j) gs[j])
    (hkill : (gs[j].op = GateOp.and ∧ lookupEnv (simpPrefix n cb gs gs.length).2 w = Sum.inl false) ∨
             (gs[j].op = GateOp.or ∧ lookupEnv (simpPrefix n cb gs gs.length).2 w = Sum.inl true) ∨
             (gs[j].op = GateOp.not ∧ ∃ c, lookupEnv (simpPrefix n cb gs gs.length).2 w = Sum.inl c)) :
    ∃ c : Bool, lookupEnv (simpPrefix n cb gs gs.length).2 (n + 2 + j) = Sum.inl c := by
  have hwlt : w < n + 2 + j := effInputs_lt hw
  have hnext : simpPrefix n cb gs (j + 1) = simpStep n (simpPrefix n cb gs j) gs[j] :=
    simpPrefix_succ n cb gs hj
  have hst_len : (simpPrefix n cb gs j).2.length = n + 2 + j :=
    simpPrefix_env_length n cb gs j (Nat.le_of_lt hj)
  rw [simpPrefix_env_stable n cb gs (Nat.succ_le_of_lt hj) le_rfl (n + 2 + j) (by omega), hnext]
  set st := simpPrefix n cb gs j
  have hlast : ∀ v, (simpStep n st gs[j]).2 = st.2 ++ [v] →
      lookupEnv (simpStep n st gs[j]).2 (n + 2 + j) = v := by
    intro v hv
    unfold lookupEnv
    rw [hv, List.getD_eq_getElem _ _ (by simp [hst_len])]
    simp [hst_len]
  rcases hkill with ⟨hop, hc⟩ | ⟨hop, hc⟩ | ⟨hop, c, hc⟩
  · rw [simpPrefix_env_stable n cb gs (Nat.le_of_lt hj) le_rfl w hwlt] at hc
    have hmem : Sum.inl false ∈ gs[j].inputs.map (lookupEnv st.2) :=
      List.mem_map.mpr ⟨w, effInputs_mem_inputs hw, hc⟩
    refine ⟨false, hlast _ ?_⟩; simp [simpStep, hop, hmem]
  · rw [simpPrefix_env_stable n cb gs (Nat.le_of_lt hj) le_rfl w hwlt] at hc
    have hmem : Sum.inl true ∈ gs[j].inputs.map (lookupEnv st.2) :=
      List.mem_map.mpr ⟨w, effInputs_mem_inputs hw, hc⟩
    refine ⟨true, hlast _ ?_⟩; simp [simpStep, hop, hmem]
  · rw [simpPrefix_env_stable n cb gs (Nat.le_of_lt hj) le_rfl w hwlt] at hc
    unfold effInputs at hw; rw [hop] at hw
    cases hin : gs[j].inputs with
    | nil => simp [hin] at hw
    | cons u us =>
      rw [hin] at hw
      by_cases hu : u < n + 2 + j
      · simp [hu] at hw; subst hw
        change lookupEnv st.2 w = Sum.inl c at hc
        refine ⟨!c, hlast _ ?_⟩
        rw [simpStep_not_cons n st gs[j] hop hin, hc]
      · simp [hu] at hw

private lemma initEnv_a (n : ℕ) (cb : Bool) (gs : List Gate) :
    lookupEnv (simpPrefix n cb gs gs.length).2 n = Sum.inl false := by
  rw [simpPrefix_env_stable n cb gs (Nat.zero_le _) le_rfl n (by omega)]
  simp [simpPrefix, initEnv, lookupEnv, List.getD_eq_getElem]

private lemma initEnv_b (n : ℕ) (cb : Bool) (gs : List Gate) :
    lookupEnv (simpPrefix n cb gs gs.length).2 (n + 1) = Sum.inl cb := by
  rw [simpPrefix_env_stable n cb gs (Nat.zero_le _) le_rfl (n + 1) (by omega)]
  simp [simpPrefix, initEnv, lookupEnv, List.getD_eq_getElem]

private def extInput {n : ℕ} (x : Fin n → Bool) (a b : Bool) : Fin (n + 2) → Bool :=
  fun i =>
    if h : i.val < n then x ⟨i.val, h⟩
    else if i.val = n then a
    else b

private lemma ofFn_extInput {n : ℕ} (x : Fin n → Bool) (a b : Bool) :
    List.ofFn (extInput x a b) = List.ofFn x ++ [a, b] := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.getElem_ofFn, extInput]
    by_cases h1 : i < n
    · rw [dite_eq_left h1, List.getElem_append_left (by simp [h1])]
      simp
    · rw [dite_eq_right h1, List.getElem_append_right (by simp; omega)]
      by_cases h2 : i = n
      · subst h2; simp
      · rw [ite_eq_right h2]
        have h3 : i - (List.ofFn x).length = 1 := by simp at hi1 ⊢; omega
        simp only [List.getElem_cons, h3]; rfl

private lemma extInput_castAdd {n : ℕ} (x : Fin n → Bool) (a b : Bool) (i : Fin n) :
    extInput x a b (Fin.castAdd 2 i) = x i := by
  simp [extInput, i.isLt]

private lemma extInput_natAdd0 {n : ℕ} (x : Fin n → Bool) (a b : Bool) :
    extInput x a b (Fin.natAdd n 0) = a := by
  simp [extInput]

private lemma extInput_natAdd1 {n : ℕ} (x : Fin n → Bool) (a b : Bool) :
    extInput x a b (Fin.natAdd n 1) = b := by
  simp [extInput]

private lemma simplify_gives_circuit (n : ℕ) (g : (Fin n → Bool) → Bool)
    (h1 : ∃ x : Fin n → Bool, g x = true) (h2 : ∃ x : Fin n → Bool, g x = false)
    (C : Circuit) (hF : FanInTwo C) (cb : Bool)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x ++ [false, cb]) = g x)
    (elimSet : Finset ℕ) (hsub : ∀ j ∈ elimSet, j < C.gates.length ∧ isElim n cb C.gates j = true) :
    ∃ s' : ℕ, s' + elimSet.card ≤ C.size ∧ HasCircuitSize n g s' := by
  have hsound := simpPrefix_sound n cb C.gates hF C.gates.length le_rfl
  set st := simpPrefix n cb C.gates C.gates.length with hst_def
  cases hout : lookupEnv st.2 C.output with
  | inl c =>
    exfalso
    obtain ⟨x₁, hx₁⟩ := h1
    obtain ⟨x₂, hx₂⟩ := h2
    have e1 : g x₁ = c := by
      have h := hsound.2.2 x₁ C.output
      rw [List.take_length, hout] at h
      exact (he x₁).symm.trans h
    have e2 : g x₂ = c := by
      have h := hsound.2.2 x₂ C.output
      rw [List.take_length, hout] at h
      exact (he x₂).symm.trans h
    rw [hx₁] at e1; rw [hx₂] at e2; rw [← e1] at e2; cases e2
  | inr out =>
    refine ⟨st.1.length, ?_, ⟨⟨st.1, out⟩, hsound.1, le_rfl, ?_⟩⟩
    · have hcnt := simpPrefix_count n cb C.gates C.gates.length le_rfl
      rw [← hst_def] at hcnt
      have hcard_le : elimSet.card ≤
          ((Finset.range C.gates.length).filter (fun j => isElim n cb C.gates j = true)).card := by
        apply Finset.card_le_card
        intro j hj
        obtain ⟨hlt, hel⟩ := hsub j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hel⟩
      change st.1.length + elimSet.card ≤ C.gates.length
      omega
    · intro x
      have h := hsound.2.2 x C.output
      rw [List.take_length, hout] at h
      exact h.symm.trans (he x)

private lemma wire_not_const_output (n : ℕ) (g : (Fin n → Bool) → Bool)
    (h1 : ∃ x : Fin n → Bool, g x = true) (h2 : ∃ x : Fin n → Bool, g x = false)
    (C : Circuit) (hF : FanInTwo C) (cb : Bool)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x ++ [false, cb]) = g x)
    (c : Bool) (hc : lookupEnv (simpPrefix n cb C.gates C.gates.length).2 C.output = Sum.inl c) :
    False := by
  have hsound := simpPrefix_sound n cb C.gates hF C.gates.length le_rfl
  obtain ⟨x₁, hx₁⟩ := h1
  obtain ⟨x₂, hx₂⟩ := h2
  have e1 : g x₁ = c := by
    have h := hsound.2.2 x₁ C.output
    rw [List.take_length, hc] at h
    exact (he x₁).symm.trans h
  have e2 : g x₂ = c := by
    have h := hsound.2.2 x₂ C.output
    rw [List.take_length, hc] at h
    exact (he x₂).symm.trans h
  rw [hx₁] at e1; rw [hx₂] at e2; rw [← e1] at e2; cases e2

private lemma depend_implies_reader (C : Circuit) (m w : ℕ)
    (x y : List Bool) (hx : x.length = m) (hy : y.length = m)
    (hagree : ∀ i < m, i ≠ w → x.getD i false = y.getD i false)
    (hdiff : C.eval x ≠ C.eval y) (hout : C.output ≠ w) :
    ∃ j : ℕ, ∃ hj : j < C.gates.length, w ∈ effInputs (m + j) C.gates[j] := by
  by_contra hno
  push Not at hno
  have hall : ∀ k ≤ C.gates.length, ∀ i < m + k, i ≠ w →
      (runGates (C.gates.take k) x).getD i false = (runGates (C.gates.take k) y).getD i false := by
    intro k hk
    induction k with
    | zero =>
      intro i hi hne; exact hagree i hi hne
    | succ k ih =>
      have hklt : k < C.gates.length := by omega
      have ih' := ih (Nat.le_of_lt hklt)
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
        List.take_succ_eq_append_getElem hklt
      have hlen_x : (runGates (C.gates.take k) x).length = m + k := by
        rw [runGates_length, hx, List.length_take_of_le (Nat.le_of_lt hklt)]
      have hlen_y : (runGates (C.gates.take k) y).length = m + k := by
        rw [runGates_length, hy, List.length_take_of_le (Nat.le_of_lt hklt)]
      intro i hi hne
      rw [htake]
      by_cases hik : i < m + k
      · rw [runGates_getD_prefix _ _ _ i (by rw [hlen_x]; exact hik),
            runGates_getD_prefix _ _ _ i (by rw [hlen_y]; exact hik)]
        exact ih' i hik hne
      · have heq : i = m + k := by omega
        subst heq
        have hx' : x.length + (C.gates.take k).length = m + k := by
          rw [hx, List.length_take_of_le (Nat.le_of_lt hklt)]
        have hy' : y.length + (C.gates.take k).length = m + k := by
          rw [hy, List.length_take_of_le (Nat.le_of_lt hklt)]
        rw [← hx', runGates_getD_step, hx', ← hy', runGates_getD_step]
        apply gate_eval_eq_of_eff C.gates[k] _ _ (by rw [hlen_x, hlen_y])
        intro u hu
        rw [hlen_x] at hu
        have hult : u < m + k := effInputs_lt hu
        have huw : u ≠ w := fun h => hno k hklt (h ▸ hu)
        exact ih' u hult huw
  apply hdiff
  change (runGates C.gates x).getD C.output false = (runGates C.gates y).getD C.output false
  by_cases ho : C.output < m + C.gates.length
  · simpa [List.take_length] using hall C.gates.length le_rfl C.output ho hout
  · rw [List.getD_eq_default _ _ (by rw [runGates_length, hx]; omega),
        List.getD_eq_default _ _ (by rw [runGates_length, hy]; omega)]

private lemma bool_pigeonhole (a b c : Bool) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> decide

private lemma no_single_exit (n : ℕ) (C : Circuit)
    (B : Finset ℕ) (u : ℕ)
    (huB : u = n ∨ u = n + 1 ∨ ∃ j ∈ B, u = n + 2 + j)
    (hB_closed : ∀ j ∈ B, ∀ hj : j < C.gates.length,
      ∀ w ∈ effInputs (n + 2 + j) C.gates[j], w = n ∨ w = n + 1 ∨ ∃ i ∈ B, w = n + 2 + i)
    (hB_exit : ∀ j : ℕ, ∀ hj : j < C.gates.length, j ∉ B →
      ∀ w ∈ effInputs (n + 2 + j) C.gates[j],
        (w = n ∨ w = n + 1 ∨ ∃ i ∈ B, w = n + 2 + i) → w = u)
    (hout_exit : (C.output = n ∨ C.output = n + 1 ∨ ∃ i ∈ B, C.output = n + 2 + i) → C.output = u)
    (x₂ x₃ : Fin n → Bool)
    (h00_2 : C.eval (List.ofFn x₂ ++ [false, false]) = false)
    (h10_2 : C.eval (List.ofFn x₂ ++ [true, false]) = true)
    (h11_2 : C.eval (List.ofFn x₂ ++ [true, true]) = true)
    (h10_3 : C.eval (List.ofFn x₃ ++ [true, false]) = false)
    (h11_3 : C.eval (List.ofFn x₃ ++ [true, true]) = true) :
    False := by
  have hB_indep : ∀ (a b : Bool) (x y : Fin n → Bool) (k : ℕ), k ≤ C.gates.length →
      ∀ i < n + 2 + k, (i = n ∨ i = n + 1 ∨ ∃ j ∈ B, i = n + 2 + j) →
        (runGates (C.gates.take k) (List.ofFn x ++ [a, b])).getD i false =
          (runGates (C.gates.take k) (List.ofFn y ++ [a, b])).getD i false := by
    intro a b x y k hk
    induction k with
    | zero =>
      intro i hi hmem
      simp only [List.take_zero, runGates_nil]
      rcases hmem with rfl | rfl | ⟨j, _, hj⟩
      · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp),
            List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
        simp
      · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp),
            List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
        simp
      · omega
    | succ k ih =>
      have hklt : k < C.gates.length := by omega
      have ih' := ih (Nat.le_of_lt hklt)
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
        List.take_succ_eq_append_getElem hklt
      have hlen_x : (runGates (C.gates.take k) (List.ofFn x ++ [a, b])).length = n + 2 + k := by
        rw [runGates_length]; simp [List.length_take_of_le (Nat.le_of_lt hklt)]
      have hlen_y : (runGates (C.gates.take k) (List.ofFn y ++ [a, b])).length = n + 2 + k := by
        rw [runGates_length]; simp [List.length_take_of_le (Nat.le_of_lt hklt)]
      intro i hi hmem
      rw [htake]
      by_cases hik : i < n + 2 + k
      · rw [runGates_getD_prefix _ _ _ i (by rw [hlen_x]; exact hik),
            runGates_getD_prefix _ _ _ i (by rw [hlen_y]; exact hik)]
        exact ih' i hik hmem
      · have heq : i = n + 2 + k := by omega
        subst heq
        have hkB : k ∈ B := by
          rcases hmem with h | h | ⟨j, hjB, hj⟩
          · omega
          · omega
          · have : j = k := by omega
            subst this; exact hjB
        have hx' : (List.ofFn x ++ [a, b]).length + (C.gates.take k).length = n + 2 + k := by
          simp [List.length_take_of_le (Nat.le_of_lt hklt)]
        have hy' : (List.ofFn y ++ [a, b]).length + (C.gates.take k).length = n + 2 + k := by
          simp [List.length_take_of_le (Nat.le_of_lt hklt)]
        rw [← hx', runGates_getD_step, hx', ← hy', runGates_getD_step]
        apply gate_eval_eq_of_eff C.gates[k] _ _ (by rw [hlen_x, hlen_y])
        intro w hw
        rw [hlen_x] at hw
        exact ih' w (effInputs_lt hw) (hB_closed k hkB hklt w hw)
  have hagree_of_u : ∀ (a₁ b₁ a₂ b₂ : Bool) (x : Fin n → Bool),
      ((runGates C.gates (List.ofFn x ++ [a₁, b₁])).getD u false =
        (runGates C.gates (List.ofFn x ++ [a₂, b₂])).getD u false) →
      C.eval (List.ofFn x ++ [a₁, b₁]) = C.eval (List.ofFn x ++ [a₂, b₂]) := by
    intro a₁ b₁ a₂ b₂ x hu_eq
    have hstep : ∀ k ≤ C.gates.length, ∀ i < n + 2 + k,
        (¬ (i = n ∨ i = n + 1 ∨ ∃ j ∈ B, i = n + 2 + j) ∨ i = u) →
        (runGates (C.gates.take k) (List.ofFn x ++ [a₁, b₁])).getD i false =
          (runGates (C.gates.take k) (List.ofFn x ++ [a₂, b₂])).getD i false := by
      intro k hk
      induction k with
      | zero =>
        intro i hi hcond
        rcases hcond with houtB | hiu
        · have hilt : i < n := by omega
          simp only [List.take_zero, runGates_nil]
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp [hilt]),
              List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp [hilt])]
        · rw [hiu] at hi ⊢
          simp only [List.take_zero]
          have h1 := runGates_getD_prefix [] C.gates (List.ofFn x ++ [a₁, b₁]) u
            (by rw [runGates_nil]; simp; omega)
          have h2 := runGates_getD_prefix [] C.gates (List.ofFn x ++ [a₂, b₂]) u
            (by rw [runGates_nil]; simp; omega)
          simp only [List.nil_append] at h1 h2
          rw [← h1, ← h2, hu_eq]
      | succ k ih =>
        have hklt : k < C.gates.length := by omega
        have ih' := ih (Nat.le_of_lt hklt)
        have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
          List.take_succ_eq_append_getElem hklt
        have hlen1 : (runGates (C.gates.take k) (List.ofFn x ++ [a₁, b₁])).length = n + 2 + k := by
          rw [runGates_length]; simp [List.length_take_of_le (Nat.le_of_lt hklt)]
        have hlen2 : (runGates (C.gates.take k) (List.ofFn x ++ [a₂, b₂])).length = n + 2 + k := by
          rw [runGates_length]; simp [List.length_take_of_le (Nat.le_of_lt hklt)]
        intro i hi hcond
        by_cases hiu : i = u
        · rw [hiu] at hi ⊢
          have hsplit : C.gates = C.gates.take (k + 1) ++ C.gates.drop (k + 1) :=
            (List.take_append_drop (k + 1) C.gates).symm
          have h1 := runGates_getD_prefix (C.gates.take (k + 1)) (C.gates.drop (k + 1))
            (List.ofFn x ++ [a₁, b₁]) u (by rw [runGates_length]; simp [List.length_take_of_le hk]; exact hi)
          have h2 := runGates_getD_prefix (C.gates.take (k + 1)) (C.gates.drop (k + 1))
            (List.ofFn x ++ [a₂, b₂]) u (by rw [runGates_length]; simp [List.length_take_of_le hk]; exact hi)
          rw [← hsplit] at h1 h2
          rw [← h1, ← h2, hu_eq]
        · have houtB : ¬ (i = n ∨ i = n + 1 ∨ ∃ j ∈ B, i = n + 2 + j) := hcond.resolve_right hiu
          rw [htake]
          by_cases hik : i < n + 2 + k
          · rw [runGates_getD_prefix _ _ _ i (by rw [hlen1]; exact hik),
                runGates_getD_prefix _ _ _ i (by rw [hlen2]; exact hik)]
            exact ih' i hik (Or.inl houtB)
          · have heq : i = n + 2 + k := by omega
            subst heq
            have hk_notB : k ∉ B := fun h => houtB (Or.inr (Or.inr ⟨k, h, rfl⟩))
            have hx1 : (List.ofFn x ++ [a₁, b₁]).length + (C.gates.take k).length = n + 2 + k := by
              simp [List.length_take_of_le (Nat.le_of_lt hklt)]
            have hx2 : (List.ofFn x ++ [a₂, b₂]).length + (C.gates.take k).length = n + 2 + k := by
              simp [List.length_take_of_le (Nat.le_of_lt hklt)]
            rw [← hx1, runGates_getD_step, hx1, ← hx2, runGates_getD_step]
            apply gate_eval_eq_of_eff C.gates[k] _ _ (by rw [hlen1, hlen2])
            intro w hw
            rw [hlen1] at hw
            have hult : w < n + 2 + k := effInputs_lt hw
            by_cases hwB : w = n ∨ w = n + 1 ∨ ∃ j ∈ B, w = n + 2 + j
            · exact ih' w hult (Or.inr (hB_exit k hklt hk_notB w hw hwB))
            · exact ih' w hult (Or.inl hwB)
    change (runGates C.gates (List.ofFn x ++ [a₁, b₁])).getD C.output false =
      (runGates C.gates (List.ofFn x ++ [a₂, b₂])).getD C.output false
    by_cases ho : C.output < n + 2 + C.gates.length
    · have hcond : ¬ (C.output = n ∨ C.output = n + 1 ∨ ∃ j ∈ B, C.output = n + 2 + j) ∨ C.output = u := by
        by_cases h : C.output = n ∨ C.output = n + 1 ∨ ∃ j ∈ B, C.output = n + 2 + j
        · exact Or.inr (hout_exit h)
        · exact Or.inl h
      simpa [List.take_length] using hstep C.gates.length le_rfl C.output ho hcond
    · rw [List.getD_eq_default _ _ (by rw [runGates_length]; simp; omega),
          List.getD_eq_default _ _ (by rw [runGates_length]; simp; omega)]
  have hu_in_B : ∀ a b, (runGates C.gates (List.ofFn x₂ ++ [a, b])).getD u false =
      (runGates C.gates (List.ofFn x₃ ++ [a, b])).getD u false := by
    intro a b
    by_cases hult : u < n + 2 + C.gates.length
    · simpa [List.take_length] using hB_indep a b x₂ x₃ C.gates.length le_rfl u hult huB
    · rw [List.getD_eq_default _ _ (by rw [runGates_length]; simp; omega),
          List.getD_eq_default _ _ (by rw [runGates_length]; simp; omega)]
  rcases bool_pigeonhole
      ((runGates C.gates (List.ofFn x₂ ++ [false, false])).getD u false)
      ((runGates C.gates (List.ofFn x₂ ++ [true, false])).getD u false)
      ((runGates C.gates (List.ofFn x₂ ++ [true, true])).getD u false) with h1 | h2 | h3
  · have := hagree_of_u false false true false x₂ h1
    rw [h00_2, h10_2] at this; cases this
  · have := hagree_of_u false false true true x₂ h2
    rw [h00_2, h11_2] at this; cases this
  · have h3' : (runGates C.gates (List.ofFn x₃ ++ [true, false])).getD u false =
        (runGates C.gates (List.ofFn x₃ ++ [true, true])).getD u false := by
      rw [← hu_in_B true false, ← hu_in_B true true]; exact h3
    have := hagree_of_u true false true true x₃ h3'
    rw [h10_3, h11_3] at this; cases this

end PEqualNP.Outside.L_meta_547_aux

theorem PEqualNP.Outside.L_meta_547 : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool) (v : Fin n), (∃ x : Fin n → Bool, g x = true) → (∃ x : Fin n → Bool, x v = true ∧ g x = false) → (∃ x : Fin n → Bool, x v = false ∧ g x = false) → PEqualNP.MetaComplexity.HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => g (fun i : Fin n => x (Fin.castAdd 2 i)) || (x (Fin.natAdd n 0) && (x (Fin.castAdd 2 v) || x (Fin.natAdd n 1)))) s → ∃ s' : ℕ, s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n g s' := by
  classical
  intro n s g v h1 h2 h3 hhas
  set F : (Fin (n + 2) → Bool) → Bool := fun x =>
    g (fun i : Fin n => x (Fin.castAdd 2 i)) ||
      (x (Fin.natAdd n 0) && (x (Fin.castAdd 2 v) || x (Fin.natAdd n 1)))
  have hex : ∃ s₀ : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (n + 2) F s₀ := ⟨s, hhas⟩
  let s₀ := Nat.find hex
  have hs₀_le : s₀ ≤ s := Nat.find_min' hex hhas
  obtain ⟨C, hF, hCsize, hCeval⟩ := Nat.find_spec hex
  have hCmin : ∀ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C' →
      (∀ x : Fin (n + 2) → Bool, C'.eval (List.ofFn x) = F x) →
      C.size ≤ C'.size := by
    intro C' hF' hE'
    have hge : s₀ ≤ C'.size := Nat.find_min' hex ⟨C', hF', le_rfl, hE'⟩
    exact le_trans hCsize hge
  suffices hgoal : ∃ s' : ℕ, s' + 3 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n g s' by
    obtain ⟨s', hs', hg'⟩ := hgoal
    exact ⟨s', by omega, hg'⟩
  have hlive : ∀ j : ℕ, j < C.gates.length →
      C.output = n + 2 + j ∨
        ∃ k : ℕ, j < k ∧ ∃ hk : k < C.gates.length,
          n + 2 + j ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + k) C.gates[k] := by
    intro j hj
    by_contra hdead
    push Not at hdead
    obtain ⟨hout, hno⟩ := hdead
    let C' := PEqualNP.Outside.L_meta_547_aux.dropDead C (n + 2) j
    have hF' := PEqualNP.Outside.L_meta_547_aux.dropDead_fanInTwo C hF (n + 2) j
    have hE' : ∀ x : Fin (n + 2) → Bool, C'.eval (List.ofFn x) = F x := by
      intro x
      rw [PEqualNP.Outside.L_meta_547_aux.dropDead_eval C (n + 2) j hj hno hout (List.ofFn x) (by simp)]
      exact hCeval x
    have hle := hCmin C' hF' hE'
    have hsz := PEqualNP.Outside.L_meta_547_aux.dropDead_size C (n + 2) j hj
    dsimp only [C'] at hle
    omega
  have hCeval_ext : ∀ (x : Fin n → Bool) (a b : Bool),
      C.eval (List.ofFn x ++ [a, b]) = (g x || (a && (x v || b))) := by
    intro x a b
    rw [← PEqualNP.Outside.L_meta_547_aux.ofFn_extInput x a b, hCeval]
    simp only [F, PEqualNP.Outside.L_meta_547_aux.extInput_castAdd,
      PEqualNP.Outside.L_meta_547_aux.extInput_natAdd0,
      PEqualNP.Outside.L_meta_547_aux.extInput_natAdd1]
  have hCeval_false : ∀ (cb : Bool) (x : Fin n → Bool),
      C.eval (List.ofFn x ++ [false, cb]) = g x := by
    intro cb x
    simp [hCeval_ext]
  obtain ⟨x₁, hx₁⟩ := h1
  obtain ⟨x₂, hx₂v, hx₂g⟩ := h2
  obtain ⟨x₃, hx₃v, hx₃g⟩ := h3
  have hg_false : ∃ x : Fin n → Bool, g x = false := ⟨x₂, hx₂g⟩
  have h00_2 : C.eval (List.ofFn x₂ ++ [false, false]) = false := by simp [hCeval_ext, hx₂g]
  have h10_2 : C.eval (List.ofFn x₂ ++ [true, false]) = true := by simp [hCeval_ext, hx₂v, hx₂g]
  have h11_2 : C.eval (List.ofFn x₂ ++ [true, true]) = true := by simp [hCeval_ext, hx₂v, hx₂g]
  have h10_3 : C.eval (List.ofFn x₃ ++ [true, false]) = false := by simp [hCeval_ext, hx₃v, hx₃g]
  have h11_3 : C.eval (List.ofFn x₃ ++ [true, true]) = true := by simp [hCeval_ext, hx₃v, hx₃g]
  have hout_ne_a : C.output ≠ n := by
    intro heq
    have h := hCeval_ext x₁ false false
    rw [hx₁] at h
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.Outside.L_meta_547_aux.wires_eq_runGates, heq] at h
    have hpref := PEqualNP.Outside.L_meta_547_aux.runGates_getD_prefix [] C.gates
      (List.ofFn x₁ ++ [false, false]) n (by rw [PEqualNP.Outside.L_meta_547_aux.runGates_nil]; simp)
    simp only [List.nil_append, PEqualNP.Outside.L_meta_547_aux.runGates_nil] at hpref
    rw [hpref, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)] at h
    simp at h
  have hout_ne_b : C.output ≠ n + 1 := by
    intro heq
    have h := hCeval_ext x₁ false false
    rw [hx₁] at h
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.Outside.L_meta_547_aux.wires_eq_runGates, heq] at h
    have hpref := PEqualNP.Outside.L_meta_547_aux.runGates_getD_prefix [] C.gates
      (List.ofFn x₁ ++ [false, false]) (n + 1) (by rw [PEqualNP.Outside.L_meta_547_aux.runGates_nil]; simp)
    simp only [List.nil_append, PEqualNP.Outside.L_meta_547_aux.runGates_nil] at hpref
    rw [hpref, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)] at h
    simp at h
  let Sa : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    if h : j < C.gates.length then
      decide (n ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + j) C.gates[j])
    else false
  let Sb : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    if h : j < C.gates.length then
      decide (n + 1 ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + j) C.gates[j])
    else false
  let S : Finset ℕ := Sa ∪ Sb
  have mem_Sa : ∀ j : ℕ, j ∈ Sa ↔ ∃ hj : j < C.gates.length,
      n ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + j) C.gates[j] := by
    intro j
    simp only [Sa, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, h⟩; rw [dite_eq_left hj, decide_eq_true_eq] at h; exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩; exact ⟨hj, by rw [dite_eq_left hj, decide_eq_true_eq]; exact h⟩
  have mem_Sb : ∀ j : ℕ, j ∈ Sb ↔ ∃ hj : j < C.gates.length,
      n + 1 ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + j) C.gates[j] := by
    intro j
    simp only [Sb, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, h⟩; rw [dite_eq_left hj, decide_eq_true_eq] at h; exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩; exact ⟨hj, by rw [dite_eq_left hj, decide_eq_true_eq]; exact h⟩
  have hSa_ne : Sa.Nonempty := by
    obtain ⟨j, hj, hmem⟩ := PEqualNP.Outside.L_meta_547_aux.depend_implies_reader C (n + 2) n
      (List.ofFn x₂ ++ [false, false]) (List.ofFn x₂ ++ [true, false]) (by simp) (by simp)
      (by
        intro i hi hne
        by_cases hlt : i < n
        · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp [hlt]),
              List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp [hlt])]
        · have hi1 : i = n + 1 := by omega
          subst hi1
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp),
              List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
          simp)
      (by rw [h00_2, h10_2]; decide) hout_ne_a
    exact ⟨j, (mem_Sa j).mpr ⟨hj, hmem⟩⟩
  have hSb_ne : Sb.Nonempty := by
    obtain ⟨j, hj, hmem⟩ := PEqualNP.Outside.L_meta_547_aux.depend_implies_reader C (n + 2) (n + 1)
      (List.ofFn x₃ ++ [true, false]) (List.ofFn x₃ ++ [true, true]) (by simp) (by simp)
      (by
        intro i hi hne
        by_cases hlt : i < n
        · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp [hlt]),
              List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp [hlt])]
        · have hi0 : i = n := by omega
          subst hi0
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp),
              List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
          simp)
      (by rw [h10_3, h11_3]; decide) hout_ne_b
    exact ⟨j, (mem_Sb j).mpr ⟨hj, hmem⟩⟩
  have eff_two_subset : ∀ (j : ℕ) (hj : j < C.gates.length) (u₁ u₂ : ℕ), u₁ ≠ u₂ →
      u₁ ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + j) C.gates[j] →
      u₂ ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + j) C.gates[j] →
      ∀ w ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + j) C.gates[j], w = u₁ ∨ w = u₂ := by
    intro j hj u₁ u₂ hne hu₁ hu₂ w hw
    have hlen : C.gates[j].inputs.length ≤ 2 := (hF C.gates[j] (List.getElem_mem hj)).2
    have hm1 := PEqualNP.Outside.L_meta_547_aux.effInputs_mem_inputs hu₁
    have hm2 := PEqualNP.Outside.L_meta_547_aux.effInputs_mem_inputs hu₂
    have hmw := PEqualNP.Outside.L_meta_547_aux.effInputs_mem_inputs hw
    cases hin : C.gates[j].inputs with
    | nil => simp [hin] at hm1
    | cons p ps =>
      cases ps with
      | nil =>
        simp [hin] at hm1 hm2
        exact absurd (hm1.trans hm2.symm) hne
      | cons q qs =>
        cases qs with
        | nil =>
          simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hm1 hm2 hmw
          rcases hm1 with rfl | rfl <;> rcases hm2 with rfl | rfl
          · exact absurd rfl hne
          · exact hmw
          · exact hmw.symm
          · exact absurd rfl hne
        | cons _ _ => simp [hin] at hlen
  by_cases hS3 : 3 ≤ S.card
  · obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_547_aux.simplify_gives_circuit n g
      ⟨x₁, hx₁⟩ hg_false C hF false (hCeval_false false) S (by
        intro j hj
        rcases Finset.mem_union.mp hj with hja | hjb
        · obtain ⟨hlt, hmem⟩ := (mem_Sa j).mp hja
          exact ⟨hlt, PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n false C.gates j hlt
            (hF _ (List.getElem_mem hlt)) n hmem false
            (PEqualNP.Outside.L_meta_547_aux.initEnv_a n false C.gates)⟩
        · obtain ⟨hlt, hmem⟩ := (mem_Sb j).mp hjb
          exact ⟨hlt, PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n false C.gates j hlt
            (hF _ (List.getElem_mem hlt)) (n + 1) hmem false
            (PEqualNP.Outside.L_meta_547_aux.initEnv_b n false C.gates)⟩)
    exact ⟨s', by omega, hg'⟩
  · have hS_pos : 1 ≤ S.card := by
      obtain ⟨j, hj⟩ := hSa_ne
      exact Finset.card_pos.mpr ⟨j, Finset.mem_union_left _ hj⟩
    by_cases hS1 : S.card = 1
    · exfalso
      obtain ⟨j₀, hj₀eq⟩ := Finset.card_eq_one.mp hS1
      have hj₀a : j₀ ∈ Sa := by
        obtain ⟨j, hj⟩ := hSa_ne
        have hjeq : j = j₀ := Finset.mem_singleton.mp (hj₀eq ▸ Finset.mem_union_left _ hj)
        exact hjeq ▸ hj
      have hj₀b : j₀ ∈ Sb := by
        obtain ⟨j, hj⟩ := hSb_ne
        have hjeq : j = j₀ := Finset.mem_singleton.mp (hj₀eq ▸ Finset.mem_union_right _ hj)
        exact hjeq ▸ hj
      obtain ⟨hlt, ha0⟩ := (mem_Sa j₀).mp hj₀a
      obtain ⟨_, hb0⟩ := (mem_Sb j₀).mp hj₀b
      exact PEqualNP.Outside.L_meta_547_aux.no_single_exit n C {j₀} (n + 2 + j₀)
        (Or.inr (Or.inr ⟨j₀, by simp, rfl⟩))
        (by
          intro j hjB hjlt w hw
          have hjj : j = j₀ := Finset.mem_singleton.mp hjB
          subst j
          rcases eff_two_subset j₀ hlt n (n + 1) (by omega) ha0 hb0 w hw with hwn | hwn
          · exact Or.inl hwn
          · exact Or.inr (Or.inl hwn))
        (by
          intro j hjlt hnotB w hw hmem
          rcases hmem with hwn | hwn | ⟨i, hiB, hwi⟩
          · exfalso
            have : j ∈ S := Finset.mem_union_left _ ((mem_Sa j).mpr ⟨hjlt, hwn ▸ hw⟩)
            rw [hj₀eq] at this; exact hnotB this
          · exfalso
            have : j ∈ S := Finset.mem_union_right _ ((mem_Sb j).mpr ⟨hjlt, hwn ▸ hw⟩)
            rw [hj₀eq] at this; exact hnotB this
          · rw [hwi, Finset.mem_singleton.mp hiB])
        (by
          intro hmem
          rcases hmem with h | h | ⟨i, hiB, h⟩
          · exact absurd h hout_ne_a
          · exact absurd h hout_ne_b
          · rw [h, Finset.mem_singleton.mp hiB])
        x₂ x₃ h00_2 h10_2 h11_2 h10_3 h11_3
    · have hS2 : S.card = 2 := by omega
      obtain ⟨j₁, j₂, hjne, hSeq⟩ := Finset.card_eq_two.mp hS2
      by_cases hboth : j₁ ∈ Sa ∧ j₁ ∈ Sb ∨ j₂ ∈ Sa ∧ j₂ ∈ Sb
      · have h2bi : ∀ p q : ℕ, p ≠ q → S = {p, q} → p ∈ Sa → p ∈ Sb →
            ∃ s' : ℕ, s' + 3 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n g s' := by
          intro p q hpq hSpq hpa hpb
          obtain ⟨hplt, hpa'⟩ := (mem_Sa p).mp hpa
          obtain ⟨_, hpb'⟩ := (mem_Sb p).mp hpb
          have hp_const : ∃ c : Bool,
              PEqualNP.Outside.L_meta_547_aux.lookupEnv
                (PEqualNP.Outside.L_meta_547_aux.simpPrefix n false C.gates C.gates.length).2
                (n + 2 + p) = Sum.inl c := by
            apply PEqualNP.Outside.L_meta_547_aux.const_of_all_const_inputs n false C.gates p hplt
              (hF _ (List.getElem_mem hplt))
            intro w hw
            rcases eff_two_subset p hplt n (n + 1) (by omega) hpa' hpb' w hw with hwn | hwn
            · rw [hwn]; exact ⟨false, PEqualNP.Outside.L_meta_547_aux.initEnv_a n false C.gates⟩
            · rw [hwn]; exact ⟨false, PEqualNP.Outside.L_meta_547_aux.initEnv_b n false C.gates⟩
          obtain ⟨cp, hcp⟩ := hp_const
          have hout_ne_p : C.output ≠ n + 2 + p := by
            intro heq
            exact PEqualNP.Outside.L_meta_547_aux.wire_not_const_output n g ⟨x₁, hx₁⟩ hg_false C hF
              false (hCeval_false false) cp (heq ▸ hcp)
          by_cases hother : ∃ r : ℕ, ∃ hr : r < C.gates.length, r ≠ p ∧ r ≠ q ∧
              n + 2 + p ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + r) C.gates[r]
          · obtain ⟨r, hrlt, hrp, hrq, hr_mem⟩ := hother
            have hqS : q ∈ S := by rw [hSpq]; simp
            have hq_elim : ∃ hqlt : q < C.gates.length,
                PEqualNP.Outside.L_meta_547_aux.isElim n false C.gates q = true := by
              rcases Finset.mem_union.mp hqS with hqa | hqb
              · obtain ⟨hlt, hm⟩ := (mem_Sa q).mp hqa
                exact ⟨hlt, PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n false C.gates q hlt
                  (hF _ (List.getElem_mem hlt)) n hm false
                  (PEqualNP.Outside.L_meta_547_aux.initEnv_a n false C.gates)⟩
              · obtain ⟨hlt, hm⟩ := (mem_Sb q).mp hqb
                exact ⟨hlt, PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n false C.gates q hlt
                  (hF _ (List.getElem_mem hlt)) (n + 1) hm false
                  (PEqualNP.Outside.L_meta_547_aux.initEnv_b n false C.gates)⟩
            obtain ⟨hqlt, hqel⟩ := hq_elim
            have hpel := PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n false C.gates p hplt
              (hF _ (List.getElem_mem hplt)) n hpa' false
              (PEqualNP.Outside.L_meta_547_aux.initEnv_a n false C.gates)
            have hrel := PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n false C.gates r hrlt
              (hF _ (List.getElem_mem hrlt)) (n + 2 + p) hr_mem cp hcp
            have hcard3 : ({p, q, r} : Finset ℕ).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hpq, Ne.symm hrp]),
                  Finset.card_insert_of_notMem (by simp [Ne.symm hrq]),
                  Finset.card_singleton]
            obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_547_aux.simplify_gives_circuit n g
              ⟨x₁, hx₁⟩ hg_false C hF false (hCeval_false false) {p, q, r} (by
                intro j hj
                simp only [Finset.mem_insert, Finset.mem_singleton] at hj
                rcases hj with rfl | rfl | rfl
                · exact ⟨hplt, hpel⟩
                · exact ⟨hqlt, hqel⟩
                · exact ⟨hrlt, hrel⟩)
            exact ⟨s', by omega, hg'⟩
          · exfalso
            push Not at hother
            obtain ⟨k, hpk, hklt, hk_mem⟩ := (hlive p hplt).resolve_left hout_ne_p
            have hkq : k = q := by
              by_contra hne
              exact hother k hklt (by omega) hne hk_mem
            subst k
            have hqS : q ∈ S := by rw [hSpq]; simp
            have hq_in_ab : n ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + q) C.gates[q] ∨
                n + 1 ∈ PEqualNP.Outside.L_meta_547_aux.effInputs (n + 2 + q) C.gates[q] := by
              rcases Finset.mem_union.mp hqS with hqa | hqb
              · exact Or.inl ((mem_Sa q).mp hqa).2
              · exact Or.inr ((mem_Sb q).mp hqb).2
            exact PEqualNP.Outside.L_meta_547_aux.no_single_exit n C {p, q} (n + 2 + q)
              (Or.inr (Or.inr ⟨q, by simp, rfl⟩))
              (by
                intro j hjB hjlt w hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hjB
                rcases hjB with hjp | hjq
                · subst j
                  rcases eff_two_subset p hplt n (n + 1) (by omega) hpa' hpb' w hw with hwn | hwn
                  · exact Or.inl hwn
                  · exact Or.inr (Or.inl hwn)
                · subst j
                  rcases hq_in_ab with ha_k | hb_k
                  · rcases eff_two_subset q hklt n (n + 2 + p) (by omega) ha_k hk_mem w hw with hwn | hwn
                    · exact Or.inl hwn
                    · exact Or.inr (Or.inr ⟨p, by simp, hwn⟩)
                  · rcases eff_two_subset q hklt (n + 1) (n + 2 + p) (by omega) hb_k hk_mem w hw with hwn | hwn
                    · exact Or.inr (Or.inl hwn)
                    · exact Or.inr (Or.inr ⟨p, by simp, hwn⟩))
              (by
                intro j hjlt hnotB w hw hmem
                have hjp : j ≠ p := fun h => hnotB (by simp [h])
                have hjq : j ≠ q := fun h => hnotB (by simp [h])
                rcases hmem with hwn | hwn | ⟨i, hiB, hwi⟩
                · exfalso
                  have : j ∈ S := Finset.mem_union_left _ ((mem_Sa j).mpr ⟨hjlt, hwn ▸ hw⟩)
                  rw [hSpq] at this; exact hnotB this
                · exfalso
                  have : j ∈ S := Finset.mem_union_right _ ((mem_Sb j).mpr ⟨hjlt, hwn ▸ hw⟩)
                  rw [hSpq] at this; exact hnotB this
                · simp only [Finset.mem_insert, Finset.mem_singleton] at hiB
                  rcases hiB with hip | hiq
                  · subst i; exact absurd (hwi ▸ hw) (hother j hjlt hjp hjq)
                  · rw [hwi, hiq])
              (by
                intro hmem
                rcases hmem with h | h | ⟨i, hiB, h⟩
                · exact absurd h hout_ne_a
                · exact absurd h hout_ne_b
                · simp only [Finset.mem_insert, Finset.mem_singleton] at hiB
                  rcases hiB with hip | hiq
                  · subst i; exact absurd h hout_ne_p
                  · rw [h, hiq])
              x₂ x₃ h00_2 h10_2 h11_2 h10_3 h11_3
        rcases hboth with ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩
        · exact h2bi j₁ j₂ hjne hSeq h1a h1b
        · exact h2bi j₂ j₁ (Ne.symm hjne) (by rw [hSeq, Finset.pair_comm]) h2a h2b
      · push Not at hboth
        obtain ⟨ja, hja⟩ := hSa_ne
        obtain ⟨jb, hjb⟩ := hSb_ne
        have hjab : ja ≠ jb := by
          intro heq; subst heq
          have hmem : ja ∈ S := Finset.mem_union_left _ hja
          rw [hSeq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact hboth.1 hja hjb
          · exact hboth.2 hja hjb
        obtain ⟨hjalt, hja_mem⟩ := (mem_Sa ja).mp hja
        obtain ⟨hjblt, hjb_mem⟩ := (mem_Sb jb).mp hjb
        have hgb_legal := hF C.gates[jb] (List.getElem_mem hjblt)
        let cb : Bool := if C.gates[jb].op = PEqualNP.CircuitLowerBounds.GateOp.or then true else false
        have hjb_const : ∃ cb_out : Bool,
            PEqualNP.Outside.L_meta_547_aux.lookupEnv
              (PEqualNP.Outside.L_meta_547_aux.simpPrefix n cb C.gates C.gates.length).2
              (n + 2 + jb) = Sum.inl cb_out := by
          apply PEqualNP.Outside.L_meta_547_aux.const_of_kill_input n cb C.gates jb hjblt
            hgb_legal (n + 1) hjb_mem
          rcases hgb_legal.1 with hop | hop | hop
          · left; exact ⟨hop, by simpa [cb, hop] using PEqualNP.Outside.L_meta_547_aux.initEnv_b n cb C.gates⟩
          · right; left; exact ⟨hop, by simpa [cb, hop] using PEqualNP.Outside.L_meta_547_aux.initEnv_b n cb C.gates⟩
          · right; right; exact ⟨hop, cb, PEqualNP.Outside.L_meta_547_aux.initEnv_b n cb C.gates⟩
        obtain ⟨db, hdb⟩ := hjb_const
        have hout_ne_jb : C.output ≠ n + 2 + jb := by
          intro heq
          exact PEqualNP.Outside.L_meta_547_aux.wire_not_const_output n g ⟨x₁, hx₁⟩ hg_false C hF
            cb (hCeval_false cb) db (heq ▸ hdb)
        obtain ⟨hb, hjbhb, hhblt, hhb_mem⟩ := (hlive jb hjblt).resolve_left hout_ne_jb
        have hja_el := PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n cb C.gates ja hjalt
          (hF _ (List.getElem_mem hjalt)) n hja_mem false
          (PEqualNP.Outside.L_meta_547_aux.initEnv_a n cb C.gates)
        have hjb_el := PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n cb C.gates jb hjblt
          hgb_legal (n + 1) hjb_mem cb
          (PEqualNP.Outside.L_meta_547_aux.initEnv_b n cb C.gates)
        by_cases hhb_ne : hb ≠ ja
        · have hhb_el := PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n cb C.gates hb hhblt
            (hF _ (List.getElem_mem hhblt)) (n + 2 + jb) hhb_mem db hdb
          have hcard3 : ({ja, jb, hb} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hjab, Ne.symm hhb_ne]),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_singleton]
          obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_547_aux.simplify_gives_circuit n g
            ⟨x₁, hx₁⟩ hg_false C hF cb (hCeval_false cb) {ja, jb, hb} (by
              intro j hj
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl | rfl
              · exact ⟨hjalt, hja_el⟩
              · exact ⟨hjblt, hjb_el⟩
              · exact ⟨hhblt, hhb_el⟩)
          exact ⟨s', by omega, hg'⟩
        · push Not at hhb_ne
          subst hb
          have hja_const : ∃ da : Bool,
              PEqualNP.Outside.L_meta_547_aux.lookupEnv
                (PEqualNP.Outside.L_meta_547_aux.simpPrefix n cb C.gates C.gates.length).2
                (n + 2 + ja) = Sum.inl da := by
            apply PEqualNP.Outside.L_meta_547_aux.const_of_all_const_inputs n cb C.gates ja hjalt
              (hF _ (List.getElem_mem hjalt))
            intro w hw
            rcases eff_two_subset ja hjalt n (n + 2 + jb) (by omega) hja_mem hhb_mem w hw with hwn | hwn
            · rw [hwn]; exact ⟨false, PEqualNP.Outside.L_meta_547_aux.initEnv_a n cb C.gates⟩
            · rw [hwn]; exact ⟨db, hdb⟩
          obtain ⟨da, hda⟩ := hja_const
          have hout_ne_ja : C.output ≠ n + 2 + ja := by
            intro heq
            exact PEqualNP.Outside.L_meta_547_aux.wire_not_const_output n g ⟨x₁, hx₁⟩ hg_false C hF
              cb (hCeval_false cb) da (heq ▸ hda)
          obtain ⟨ha, hhbha, hhalt, hha_mem⟩ := (hlive ja hjalt).resolve_left hout_ne_ja
          have hha_el := PEqualNP.Outside.L_meta_547_aux.elim_of_const_input n cb C.gates ha hhalt
            (hF _ (List.getElem_mem hhalt)) (n + 2 + ja) hha_mem da hda
          have hcard3 : ({jb, ja, ha} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_singleton]
          obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_547_aux.simplify_gives_circuit n g
            ⟨x₁, hx₁⟩ hg_false C hF cb (hCeval_false cb) {jb, ja, ha} (by
              intro j hj
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl | rfl
              · exact ⟨hjblt, hjb_el⟩
              · exact ⟨hjalt, hja_el⟩
              · exact ⟨hhalt, hha_el⟩)
          exact ⟨s', by omega, hg'⟩
