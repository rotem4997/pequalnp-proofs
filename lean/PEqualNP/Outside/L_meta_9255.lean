import Mathlib.Tactic
import Mathlib.Data.Tree.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9255
-- The graph is a triangle with three paths of two edges hung on one after another. The namespace Path and the
-- theorem Path.pathExtension (such a path costs at least three gates) are taken from PEqualNP.Outside.L_meta_8505
-- (by Brian, same repository, Apache-2.0). New here: the bound for the triangle, the renaming of inputs and the
-- last theorem.

namespace Path

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

end Path

theorem Path.pathExtension : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool) (v : Fin n), (∃ x : Fin n → Bool, g x = true) → (∃ x : Fin n → Bool, x v = true ∧ g x = false) → (∃ x : Fin n → Bool, x v = false ∧ g x = false) → PEqualNP.MetaComplexity.HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => g (fun i : Fin n => x (Fin.castAdd 2 i)) || (x (Fin.natAdd n 0) && (x (Fin.castAdd 2 v) || x (Fin.natAdd n 1)))) s → ∃ s' : ℕ, s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n g s' := by
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
          n + 2 + j ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + k) C.gates[k] := by
    intro j hj
    by_contra hdead
    push Not at hdead
    obtain ⟨hout, hno⟩ := hdead
    let C' := PEqualNP.Outside.L_meta_9255.Path.dropDead C (n + 2) j
    have hF' := PEqualNP.Outside.L_meta_9255.Path.dropDead_fanInTwo C hF (n + 2) j
    have hE' : ∀ x : Fin (n + 2) → Bool, C'.eval (List.ofFn x) = F x := by
      intro x
      rw [PEqualNP.Outside.L_meta_9255.Path.dropDead_eval C (n + 2) j hj hno hout (List.ofFn x) (by simp)]
      exact hCeval x
    have hle := hCmin C' hF' hE'
    have hsz := PEqualNP.Outside.L_meta_9255.Path.dropDead_size C (n + 2) j hj
    dsimp only [C'] at hle
    omega
  have hCeval_ext : ∀ (x : Fin n → Bool) (a b : Bool),
      C.eval (List.ofFn x ++ [a, b]) = (g x || (a && (x v || b))) := by
    intro x a b
    rw [← PEqualNP.Outside.L_meta_9255.Path.ofFn_extInput x a b, hCeval]
    simp only [F, PEqualNP.Outside.L_meta_9255.Path.extInput_castAdd,
      PEqualNP.Outside.L_meta_9255.Path.extInput_natAdd0,
      PEqualNP.Outside.L_meta_9255.Path.extInput_natAdd1]
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
      PEqualNP.Outside.L_meta_9255.Path.wires_eq_runGates, heq] at h
    have hpref := PEqualNP.Outside.L_meta_9255.Path.runGates_getD_prefix [] C.gates
      (List.ofFn x₁ ++ [false, false]) n (by rw [PEqualNP.Outside.L_meta_9255.Path.runGates_nil]; simp)
    simp only [List.nil_append, PEqualNP.Outside.L_meta_9255.Path.runGates_nil] at hpref
    rw [hpref, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)] at h
    simp at h
  have hout_ne_b : C.output ≠ n + 1 := by
    intro heq
    have h := hCeval_ext x₁ false false
    rw [hx₁] at h
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.Outside.L_meta_9255.Path.wires_eq_runGates, heq] at h
    have hpref := PEqualNP.Outside.L_meta_9255.Path.runGates_getD_prefix [] C.gates
      (List.ofFn x₁ ++ [false, false]) (n + 1) (by rw [PEqualNP.Outside.L_meta_9255.Path.runGates_nil]; simp)
    simp only [List.nil_append, PEqualNP.Outside.L_meta_9255.Path.runGates_nil] at hpref
    rw [hpref, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)] at h
    simp at h
  let Sa : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    if h : j < C.gates.length then
      decide (n ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + j) C.gates[j])
    else false
  let Sb : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    if h : j < C.gates.length then
      decide (n + 1 ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + j) C.gates[j])
    else false
  let S : Finset ℕ := Sa ∪ Sb
  have mem_Sa : ∀ j : ℕ, j ∈ Sa ↔ ∃ hj : j < C.gates.length,
      n ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + j) C.gates[j] := by
    intro j
    simp only [Sa, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, h⟩; rw [dite_eq_left hj, decide_eq_true_eq] at h; exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩; exact ⟨hj, by rw [dite_eq_left hj, decide_eq_true_eq]; exact h⟩
  have mem_Sb : ∀ j : ℕ, j ∈ Sb ↔ ∃ hj : j < C.gates.length,
      n + 1 ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + j) C.gates[j] := by
    intro j
    simp only [Sb, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, h⟩; rw [dite_eq_left hj, decide_eq_true_eq] at h; exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩; exact ⟨hj, by rw [dite_eq_left hj, decide_eq_true_eq]; exact h⟩
  have hSa_ne : Sa.Nonempty := by
    obtain ⟨j, hj, hmem⟩ := PEqualNP.Outside.L_meta_9255.Path.depend_implies_reader C (n + 2) n
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
    obtain ⟨j, hj, hmem⟩ := PEqualNP.Outside.L_meta_9255.Path.depend_implies_reader C (n + 2) (n + 1)
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
      u₁ ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + j) C.gates[j] →
      u₂ ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + j) C.gates[j] →
      ∀ w ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + j) C.gates[j], w = u₁ ∨ w = u₂ := by
    intro j hj u₁ u₂ hne hu₁ hu₂ w hw
    have hlen : C.gates[j].inputs.length ≤ 2 := (hF C.gates[j] (List.getElem_mem hj)).2
    have hm1 := PEqualNP.Outside.L_meta_9255.Path.effInputs_mem_inputs hu₁
    have hm2 := PEqualNP.Outside.L_meta_9255.Path.effInputs_mem_inputs hu₂
    have hmw := PEqualNP.Outside.L_meta_9255.Path.effInputs_mem_inputs hw
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
  · obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_9255.Path.simplify_gives_circuit n g
      ⟨x₁, hx₁⟩ hg_false C hF false (hCeval_false false) S (by
        intro j hj
        rcases Finset.mem_union.mp hj with hja | hjb
        · obtain ⟨hlt, hmem⟩ := (mem_Sa j).mp hja
          exact ⟨hlt, PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n false C.gates j hlt
            (hF _ (List.getElem_mem hlt)) n hmem false
            (PEqualNP.Outside.L_meta_9255.Path.initEnv_a n false C.gates)⟩
        · obtain ⟨hlt, hmem⟩ := (mem_Sb j).mp hjb
          exact ⟨hlt, PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n false C.gates j hlt
            (hF _ (List.getElem_mem hlt)) (n + 1) hmem false
            (PEqualNP.Outside.L_meta_9255.Path.initEnv_b n false C.gates)⟩)
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
      exact PEqualNP.Outside.L_meta_9255.Path.no_single_exit n C {j₀} (n + 2 + j₀)
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
              PEqualNP.Outside.L_meta_9255.Path.lookupEnv
                (PEqualNP.Outside.L_meta_9255.Path.simpPrefix n false C.gates C.gates.length).2
                (n + 2 + p) = Sum.inl c := by
            apply PEqualNP.Outside.L_meta_9255.Path.const_of_all_const_inputs n false C.gates p hplt
              (hF _ (List.getElem_mem hplt))
            intro w hw
            rcases eff_two_subset p hplt n (n + 1) (by omega) hpa' hpb' w hw with hwn | hwn
            · rw [hwn]; exact ⟨false, PEqualNP.Outside.L_meta_9255.Path.initEnv_a n false C.gates⟩
            · rw [hwn]; exact ⟨false, PEqualNP.Outside.L_meta_9255.Path.initEnv_b n false C.gates⟩
          obtain ⟨cp, hcp⟩ := hp_const
          have hout_ne_p : C.output ≠ n + 2 + p := by
            intro heq
            exact PEqualNP.Outside.L_meta_9255.Path.wire_not_const_output n g ⟨x₁, hx₁⟩ hg_false C hF
              false (hCeval_false false) cp (heq ▸ hcp)
          by_cases hother : ∃ r : ℕ, ∃ hr : r < C.gates.length, r ≠ p ∧ r ≠ q ∧
              n + 2 + p ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + r) C.gates[r]
          · obtain ⟨r, hrlt, hrp, hrq, hr_mem⟩ := hother
            have hqS : q ∈ S := by rw [hSpq]; simp
            have hq_elim : ∃ hqlt : q < C.gates.length,
                PEqualNP.Outside.L_meta_9255.Path.isElim n false C.gates q = true := by
              rcases Finset.mem_union.mp hqS with hqa | hqb
              · obtain ⟨hlt, hm⟩ := (mem_Sa q).mp hqa
                exact ⟨hlt, PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n false C.gates q hlt
                  (hF _ (List.getElem_mem hlt)) n hm false
                  (PEqualNP.Outside.L_meta_9255.Path.initEnv_a n false C.gates)⟩
              · obtain ⟨hlt, hm⟩ := (mem_Sb q).mp hqb
                exact ⟨hlt, PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n false C.gates q hlt
                  (hF _ (List.getElem_mem hlt)) (n + 1) hm false
                  (PEqualNP.Outside.L_meta_9255.Path.initEnv_b n false C.gates)⟩
            obtain ⟨hqlt, hqel⟩ := hq_elim
            have hpel := PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n false C.gates p hplt
              (hF _ (List.getElem_mem hplt)) n hpa' false
              (PEqualNP.Outside.L_meta_9255.Path.initEnv_a n false C.gates)
            have hrel := PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n false C.gates r hrlt
              (hF _ (List.getElem_mem hrlt)) (n + 2 + p) hr_mem cp hcp
            have hcard3 : ({p, q, r} : Finset ℕ).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hpq, Ne.symm hrp]),
                  Finset.card_insert_of_notMem (by simp [Ne.symm hrq]),
                  Finset.card_singleton]
            obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_9255.Path.simplify_gives_circuit n g
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
            have hq_in_ab : n ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + q) C.gates[q] ∨
                n + 1 ∈ PEqualNP.Outside.L_meta_9255.Path.effInputs (n + 2 + q) C.gates[q] := by
              rcases Finset.mem_union.mp hqS with hqa | hqb
              · exact Or.inl ((mem_Sa q).mp hqa).2
              · exact Or.inr ((mem_Sb q).mp hqb).2
            exact PEqualNP.Outside.L_meta_9255.Path.no_single_exit n C {p, q} (n + 2 + q)
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
            PEqualNP.Outside.L_meta_9255.Path.lookupEnv
              (PEqualNP.Outside.L_meta_9255.Path.simpPrefix n cb C.gates C.gates.length).2
              (n + 2 + jb) = Sum.inl cb_out := by
          apply PEqualNP.Outside.L_meta_9255.Path.const_of_kill_input n cb C.gates jb hjblt
            hgb_legal (n + 1) hjb_mem
          rcases hgb_legal.1 with hop | hop | hop
          · left; exact ⟨hop, by simpa [cb, hop] using PEqualNP.Outside.L_meta_9255.Path.initEnv_b n cb C.gates⟩
          · right; left; exact ⟨hop, by simpa [cb, hop] using PEqualNP.Outside.L_meta_9255.Path.initEnv_b n cb C.gates⟩
          · right; right; exact ⟨hop, cb, PEqualNP.Outside.L_meta_9255.Path.initEnv_b n cb C.gates⟩
        obtain ⟨db, hdb⟩ := hjb_const
        have hout_ne_jb : C.output ≠ n + 2 + jb := by
          intro heq
          exact PEqualNP.Outside.L_meta_9255.Path.wire_not_const_output n g ⟨x₁, hx₁⟩ hg_false C hF
            cb (hCeval_false cb) db (heq ▸ hdb)
        obtain ⟨hb, hjbhb, hhblt, hhb_mem⟩ := (hlive jb hjblt).resolve_left hout_ne_jb
        have hja_el := PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n cb C.gates ja hjalt
          (hF _ (List.getElem_mem hjalt)) n hja_mem false
          (PEqualNP.Outside.L_meta_9255.Path.initEnv_a n cb C.gates)
        have hjb_el := PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n cb C.gates jb hjblt
          hgb_legal (n + 1) hjb_mem cb
          (PEqualNP.Outside.L_meta_9255.Path.initEnv_b n cb C.gates)
        by_cases hhb_ne : hb ≠ ja
        · have hhb_el := PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n cb C.gates hb hhblt
            (hF _ (List.getElem_mem hhblt)) (n + 2 + jb) hhb_mem db hdb
          have hcard3 : ({ja, jb, hb} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hjab, Ne.symm hhb_ne]),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_singleton]
          obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_9255.Path.simplify_gives_circuit n g
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
              PEqualNP.Outside.L_meta_9255.Path.lookupEnv
                (PEqualNP.Outside.L_meta_9255.Path.simpPrefix n cb C.gates C.gates.length).2
                (n + 2 + ja) = Sum.inl da := by
            apply PEqualNP.Outside.L_meta_9255.Path.const_of_all_const_inputs n cb C.gates ja hjalt
              (hF _ (List.getElem_mem hjalt))
            intro w hw
            rcases eff_two_subset ja hjalt n (n + 2 + jb) (by omega) hja_mem hhb_mem w hw with hwn | hwn
            · rw [hwn]; exact ⟨false, PEqualNP.Outside.L_meta_9255.Path.initEnv_a n cb C.gates⟩
            · rw [hwn]; exact ⟨db, hdb⟩
          obtain ⟨da, hda⟩ := hja_const
          have hout_ne_ja : C.output ≠ n + 2 + ja := by
            intro heq
            exact PEqualNP.Outside.L_meta_9255.Path.wire_not_const_output n g ⟨x₁, hx₁⟩ hg_false C hF
              cb (hCeval_false cb) da (heq ▸ hda)
          obtain ⟨ha, hhbha, hhalt, hha_mem⟩ := (hlive ja hjalt).resolve_left hout_ne_ja
          have hha_el := PEqualNP.Outside.L_meta_9255.Path.elim_of_const_input n cb C.gates ha hhalt
            (hF _ (List.getElem_mem hhalt)) (n + 2 + ja) hha_mem da hda
          have hcard3 : ({jb, ja, ha} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_singleton]
          obtain ⟨s', hs', hg'⟩ := PEqualNP.Outside.L_meta_9255.Path.simplify_gives_circuit n g
            ⟨x₁, hx₁⟩ hg_false C hF cb (hCeval_false cb) {jb, ja, ha} (by
              intro j hj
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl | rfl
              · exact ⟨hjblt, hjb_el⟩
              · exact ⟨hjalt, hja_el⟩
              · exact ⟨hhalt, hha_el⟩)
          exact ⟨s', by omega, hg'⟩


namespace Ren
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stp (W gs x) g := by simp [W]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc, stp]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]


-- Inputs that do not matter are read as false: a wire past the end of the list.

def rhs (n k : ℕ) (τ : ℕ → ℕ) (i : ℕ) : ℕ := if i < n then τ i else i - n + k

def rens (n k : ℕ) (τ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rhs n k τ)⟩

theorem sub_wires (n k B : ℕ) (τ : ℕ → ℕ) (hτ : ∀ i < n, τ i < k ∨ B ≤ τ i) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = k) (hxy : ∀ i < n, x.getD i false = y.getD (τ i) false) (gs : List Gate) :
    k + gs.length ≤ B → ∀ i, (W (gs.map (rens n k τ)) y).getD (rhs n k τ i) false = (W gs x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i
    by_cases hi : i < n
    · simp only [rhs, hi, ↓reduceIte, W, List.map_nil, List.foldl_nil]
      exact (hxy i hi).symm
    · simp only [rhs, hi, ↓reduceIte, W, List.map_nil, List.foldl_nil]
      rw [getD_big _ _ (by omega), getD_big _ _ (by omega)]
  | append_singleton gs g ih =>
    intro hB i
    simp only [List.length_append, List.length_singleton] at hB
    have IH := ih (by omega)
    have lx : (W gs x).length = n + gs.length := by rw [W_len, hx]
    have ly : (W (gs.map (rens n k τ)) y).length = k + gs.length := by rw [W_len, hy, List.length_map]
    rw [List.map_append, List.map_singleton, W_snoc, W_snoc, stp, stp]
    by_cases hi : i < n
    · have e : rhs n k τ i = τ i := by simp [rhs, hi]
      rw [getD_lt _ _ _ (by omega : i < (W gs x).length), ← IH i, e]
      rcases hτ i hi with h | h
      · rw [getD_lt _ _ _ (by omega)]
      · rw [getD_big _ _ (by simp; omega), getD_big _ _ (by omega)]
    · have e : rhs n k τ i = i - n + k := by simp [rhs, hi]
      rcases lt_trichotomy i (n + gs.length) with h | h | h
      · rw [getD_lt _ _ _ (by omega : i < (W gs x).length), ← IH i, e, getD_lt _ _ _ (by omega)]
      · have e1 := getD_len (W gs x) (g.op.eval (g.inputs.map fun i => (W gs x).getD i false))
        have e2 := getD_len (W (gs.map (rens n k τ)) y)
          ((rens n k τ g).op.eval ((rens n k τ g).inputs.map fun i => (W (gs.map (rens n k τ)) y).getD i false))
        rw [lx] at e1
        rw [ly] at e2
        rw [e, h, e1, show n + gs.length - n + k = k + gs.length by omega, e2]
        simp only [rens, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact IH j
      · rw [e, getD_big _ _ (by simp; omega), getD_big _ _ (by simp; omega)]

theorem sub (n k B : ℕ) (τ : ℕ → ℕ) (hτ : ∀ i < n, τ i < k ∨ B ≤ τ i) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hs : k + s ≤ B) (h : HasCircuitSize n f s) :
    HasCircuitSize k (fun y => f (fun i => (List.ofFn y).getD (τ i) false)) s := by
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨⟨C.gates.map (rens n k τ), rhs n k τ C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    simpa [rens] using h1 g' hg'
  · have : C.gates.length ≤ s := h2
    simpa [Circuit.size] using this
  · intro y
    have hl : C.gates.length ≤ s := h2
    change _ = f (fun i : Fin n => (List.ofFn y).getD (τ i) false)
    rw [← h3]
    refine sub_wires n k B τ hτ (List.ofFn fun i : Fin n => (List.ofFn y).getD (τ i) false) (List.ofFn y) (by simp)
      (by simp) ?_ C.gates (by omega) C.output
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

end Ren

namespace K3
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuits of AND, OR and NOT gates for a function on 3 inputs, looked at on a few chosen inputs. A
-- smallest circuit has no gate that equals an earlier wire, or is constantly false, on them. Counting
-- the wires still needed, from the last gate back, shows that a circuit with few gates is a read-once
-- formula after a few steps, each of which uses a value twice or complements it. The steps are
-- followed on multisets of leaf values, and a recursion on the pairs of inputs that each side of the
-- top gate must separate excludes every case.

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

def Good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stp (W gs x) g := by simp [W]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc, stp]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

-- the chosen inputs: first those where the function is true, then those where it is false
def PT : List ℕ := [3, 5, 6, 0, 1, 2, 4]

def X (p : ℕ) : List Bool := List.ofFn (fun i : Fin 3 => Nat.testBit (PT.getD p 0) i)

theorem X_len (p : ℕ) : (X p).length = 3 := by simp [X]

-- the values of input i on the chosen inputs
def lf (i : ℕ) : ℕ := [19, 37, 70].getD i 0

theorem lf_X : ∀ i < 3, ∀ p < 7, (lf i).testBit p = (X p).getD i false := by decide +kernel

def ev (gs : List Gate) (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (W gs x).getD i false)

def Irr (gs : List Gate) : Prop := ∀ pre g post, gs = pre ++ g :: post →
  (∀ a < 3 + pre.length, ¬ ∀ p < 7, ev pre g (X p) = (W pre (X p)).getD a false) ∧
  ¬ ∀ p < 7, ev pre g (X p) = false

theorem Irr_prefix (gs : List Gate) (g : Gate) (h : Irr (gs ++ [g])) : Irr gs := by
  intro pre g' post e
  exact h pre g' (post ++ [g]) (by rw [e]; simp)

def rho (k a i : ℕ) : ℕ := if i < k then i else if i = k then a else i - 1

def ren (k a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho k a)⟩

theorem ren_wires (pre : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 3) (a L : ℕ)
    (ha : (a < 3 + pre.length ∧ ev pre g x = (W pre x).getD a false) ∨
      (a = 3 + pre.length + L ∧ ev pre g x = false)) (post : List Gate) : post.length ≤ L →
    ∀ i, (W (pre ++ post.map (ren (3 + pre.length) a)) x).getD (rho (3 + pre.length) a i) false =
      (W (pre ++ g :: post) x).getD i false := by
  set k := 3 + pre.length with hk
  induction post using List.reverseRecOn with
  | nil =>
    intro _ i
    have h1 : W (pre ++ [g]) x = W pre x ++ [ev pre g x] := by rw [W_snoc]; rfl
    have hl : (W pre x).length = k := by rw [W_len, hx]
    simp only [List.map_nil, List.append_nil]
    rw [h1]
    rcases lt_trichotomy i k with h | h | h
    · rw [rho, ite_eq_left h, getD_lt _ _ _ (by omega)]
    · rw [rho, ite_eq_right (by omega), ite_eq_left h]
      have h2 := getD_len (W pre x) (ev pre g x)
      rw [hl] at h2
      rw [h, h2]
      rcases ha with ⟨_, h3⟩ | ⟨h3, h4⟩
      · exact h3.symm
      · rw [h4, getD_big _ _ (by omega)]
    · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_big _ _ (by omega),
        getD_big _ _ (by simp; omega)]
  | append_singleton post h ih =>
    intro hL i
    simp only [List.length_append, List.length_singleton] at hL
    have IH := ih (by omega)
    set w0 := W (pre ++ g :: post) x with hw0
    set w1 := W (pre ++ post.map (ren k a)) x with hw1
    have l0 : w0.length = k + 1 + post.length := by rw [hw0, W_len, hx]; simp; omega
    have l1 : w1.length = k + post.length := by rw [hw1, W_len, hx]; simp; omega
    have e0 : W (pre ++ g :: (post ++ [h])) x = w0 ++ [ev (pre ++ g :: post) h x] := by
      rw [show pre ++ g :: (post ++ [h]) = (pre ++ g :: post) ++ [h] by simp, W_snoc]; rfl
    have e1 : W (pre ++ (post ++ [h]).map (ren k a)) x =
        w1 ++ [ev (pre ++ post.map (ren k a)) (ren k a h) x] := by
      rw [show pre ++ (post ++ [h]).map (ren k a) =
        (pre ++ post.map (ren k a)) ++ [ren k a h] by simp, W_snoc]; rfl
    have ee : ev (pre ++ post.map (ren k a)) (ren k a h) x = ev (pre ++ g :: post) h x := by
      unfold ev ren
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact IH j
    rw [e0, e1, ee]
    rcases lt_trichotomy i w0.length with hi | hi | hi
    · rw [getD_lt _ _ _ hi, ← IH i]
      rcases lt_trichotomy i k with h' | h' | h'
      · rw [rho, ite_eq_left h', getD_lt _ _ _ (by omega)]
      · rw [rho, ite_eq_right (by omega), ite_eq_left h']
        rcases ha with ⟨h3, _⟩ | ⟨h3, _⟩
        · rw [getD_lt _ _ _ (by omega)]
        · rw [getD_big _ _ (by simp; omega), getD_big _ _ (by omega)]
      · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_lt _ _ _ (by omega)]
    · have h2 := getD_len w0 (ev (pre ++ g :: post) h x)
      rw [hi, h2, rho, ite_eq_right (by omega), ite_eq_right (by omega)]
      have h3 := getD_len w1 (ev (pre ++ g :: post) h x)
      rw [show w0.length - 1 = w1.length by omega, h3]
    · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_big _ _ (by simp; omega),
        getD_big _ _ (by simp; omega)]

-- the values of the function on the chosen inputs
def MM : ℕ := 2 ^ 3 - 1

theorem min_circ (f : (Fin 3 → Bool) → Bool)
    (hf : ∀ p < 7, f (fun i => Nat.testBit (PT.getD p 0) i) = MM.testBit p) (s : ℕ)
    (h : HasCircuitSize 3 f s) :
    ∃ C : Circuit, (∀ g ∈ C.gates, Good g) ∧ C.gates.length ≤ s ∧
      (∀ p < 7, C.eval (X p) = MM.testBit p) ∧ Irr C.gates := by
  classical
  have hgood : ∀ C : Circuit, FanInTwo C → ∀ g ∈ C.gates, Good g := by
    intro C hC g hg
    have := hC g hg
    simpa [Good] using this
  have hall : ∀ C : Circuit, (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = f x) →
      ∀ p < 7, C.eval (X p) = MM.testBit p := by
    intro C hC p hp
    rw [← hf p hp]
    exact hC _
  have hex : ∃ t, ∃ C : Circuit, (∀ g ∈ C.gates, Good g) ∧ C.gates.length = t ∧
      (∀ p < 7, C.eval (X p) = MM.testBit p) := by
    obtain ⟨C, hC, _, hr⟩ := h
    exact ⟨_, C, hgood C hC, rfl, hall C hr⟩
  obtain ⟨C, hC, hlen, hrep⟩ := Nat.find_spec hex
  have hle : C.gates.length ≤ s := by
    obtain ⟨C', hC', hs, hr⟩ := h
    rw [hlen]
    exact (Nat.find_min' hex ⟨C', hgood C' hC', rfl, hall C' hr⟩).trans hs
  refine ⟨C, hC, hle, hrep, ?_⟩
  -- a removable gate would give a smaller circuit
  have key : ∀ pre g post, C.gates = pre ++ g :: post → ∀ a,
      (∀ p < 7, (a < 3 + pre.length ∧ ev pre g (X p) = (W pre (X p)).getD a false) ∨
        (a = 3 + pre.length + post.length ∧ ev pre g (X p) = false)) → False := by
    intro pre g post e a ha
    have hnew : ∃ C' : Circuit, (∀ g ∈ C'.gates, Good g) ∧
        C'.gates.length = C.gates.length - 1 ∧ (∀ p < 7, C'.eval (X p) = MM.testBit p) := by
      refine ⟨⟨pre ++ post.map (ren (3 + pre.length) a), rho (3 + pre.length) a C.output⟩,
        ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h1 | h1
        · exact hC g' (by rw [e]; simp [h1])
        · obtain ⟨h2, h3, rfl⟩ := List.mem_map.mp h1
          have := hC h2 (by rw [e]; simp [h3])
          exact ⟨this.1, by simpa [ren] using this.2⟩
      · rw [e]; simp
      · intro p hp
        have h1 := ren_wires pre g (X p) (X_len _) a post.length (ha _ hp) post le_rfl C.output
        rw [← e] at h1
        exact h1.trans (hrep p hp)
    have := Nat.find_min' hex hnew
    have hpos : 0 < C.gates.length := by rw [e]; simp
    omega
  intro pre g post e
  refine ⟨fun a ha hall => key pre g post e a (fun p hp => Or.inl ⟨ha, hall p hp⟩),
    fun hall => key pre g post e _ (fun p hp => Or.inr ⟨rfl, hall p hp⟩)⟩

-- Read-once formulas over multisets of leaf values, families of wires, and chains of steps.

def FULL : ℕ := 2 ^ 7 - 1

theorem FULL_bit (p : ℕ) (hp : p < 7) (m : ℕ) : (FULL ^^^ m).testBit p = !m.testBit p := by
  rw [Nat.testBit_xor]
  have : FULL.testBit p = true := by
    unfold FULL; rw [Nat.testBit_two_pow_sub_one]; simpa using hp
  rw [this]; simp

def RM (S : Multiset ℕ) (m : ℕ) : Prop := ∀ Q : Multiset ℕ → ℕ → Prop, (∀ x, Q {x} x) →
  (∀ S T a b, Q S a → Q T b → Q (S + T) (a &&& b) ∧ Q (S + T) (a ||| b)) → Q S m

theorem RM_leaf (x : ℕ) : RM {x} x := fun _ h1 _ => h1 x

theorem RM_and {S T : Multiset ℕ} {a b : ℕ} (ha : RM S a) (hb : RM T b) : RM (S + T) (a &&& b) :=
  fun Q h1 h2 => (h2 S T a b (ha Q h1 h2) (hb Q h1 h2)).1

theorem RM_or {S T : Multiset ℕ} {a b : ℕ} (ha : RM S a) (hb : RM T b) : RM (S + T) (a ||| b) :=
  fun Q h1 h2 => (h2 S T a b (ha Q h1 h2) (hb Q h1 h2)).2

def Fam (L : Multiset ℕ) (I : Finset ℕ) (val : ℕ → ℕ → Bool) : Prop :=
  ∃ (S : ℕ → Multiset ℕ) (m : ℕ → ℕ), (∀ w ∈ I, RM (S w) (m w)) ∧
    (∀ w ∈ I, ∀ p < 7, (m w).testBit p = val w p) ∧ ∑ w ∈ I, S w = L

def Ch : ℕ → Multiset ℕ → Finset ℕ → (ℕ → ℕ → Bool) → Prop
  | 0, L, I, val => Fam L I val
  | b + 1, L, I, val => ∃ (Sc rest : Multiset ℕ) (mc : ℕ), L = Sc + rest ∧ RM Sc mc ∧
      (Ch b (mc ::ₘ mc ::ₘ rest) I val ∨ Ch b ((FULL ^^^ mc) ::ₘ rest) I val)

theorem Ch_map (I I' : Finset ℕ) (val val' : ℕ → ℕ → Bool)
    (h : ∀ L, Fam L I val → Fam L I' val') : ∀ b L, Ch b L I val → Ch b L I' val' := by
  intro b
  induction b with
  | zero => exact h
  | succ b ih =>
    rintro L ⟨Sc, rest, mc, h1, h2, h3⟩
    exact ⟨Sc, rest, mc, h1, h2, h3.imp (ih _) (ih _)⟩

theorem Fam_congr (I : Finset ℕ) (val val' : ℕ → ℕ → Bool)
    (h : ∀ w ∈ I, ∀ p < 7, val w p = val' w p) (L : Multiset ℕ)
    (hF : Fam L I val) : Fam L I val' := by
  obtain ⟨S, m, h1, h2, h3⟩ := hF
  exact ⟨S, m, h1, fun w hw p hp => by rw [h2 w hw p hp, h w hw p hp], h3⟩

-- two members of the family are merged into a new one
theorem Fam_bin (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a b e : ℕ) (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) (he : e ∉ (I.erase a).erase b)
    (hv : (∀ p < 7, val e p = (val a p && val b p)) ∨ (∀ p < 7, val e p = (val a p || val b p)))
    (L : Multiset ℕ) (hF : Fam L I val) : Fam L (insert e ((I.erase a).erase b)) val := by
  obtain ⟨S, m, hRM, hval, hsum⟩ := hF
  obtain ⟨mk, hmk1, hmk2⟩ : ∃ mk, RM (S a + S b) mk ∧ ∀ p < 7, mk.testBit p = val e p := by
    rcases hv with hv | hv
    · exact ⟨_, RM_and (hRM a ha) (hRM b hb), fun p hp => by
        rw [hv p hp, Nat.testBit_and, hval a ha p hp, hval b hb p hp]⟩
    · exact ⟨_, RM_or (hRM a ha) (hRM b hb), fun p hp => by
        rw [hv p hp, Nat.testBit_or, hval a ha p hp, hval b hb p hp]⟩
  have hR : ∀ w ∈ (I.erase a).erase b, w ≠ e ∧ w ∈ I := by
    intro w hw
    have h1 := Finset.mem_erase.mp hw
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨fun h => he (h ▸ hw), h2.2⟩
  refine ⟨fun w => if w = e then S a + S b else S w, fun w => if w = e then mk else m w, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact hmk1
    · simp only [(hR w h).1, ↓reduceIte]; exact hRM w (hR w h).2
  · intro w hw p hp
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact hmk2 p hp
    · simp only [(hR w h).1, ↓reduceIte]; exact hval w (hR w h).2 p hp
  · rw [Finset.sum_insert he]
    simp only [↓reduceIte]
    rw [Finset.sum_congr rfl (fun w hw => by simp only [(hR w hw).1, ↓reduceIte] :
      ∀ w ∈ (I.erase a).erase b, (if w = e then S a + S b else S w) = S w)]
    have hb' : b ∈ I.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    rw [add_assoc, Finset.add_sum_erase _ S hb', Finset.add_sum_erase _ S ha]
    exact hsum

-- a member of the family is used a second time
theorem Fam_dup (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I)
    (hv : ∀ p < 7, val e p = val a p) (L : Multiset ℕ) (hF : Fam L I val) :
    Ch 1 L (insert e I) val := by
  obtain ⟨S, m, hRM, hval, hsum⟩ := hF
  have hea : e ≠ a := fun h => he (h ▸ ha)
  refine ⟨S a, ∑ w ∈ I.erase a, S w, m a, ?_, hRM a ha, Or.inl ?_⟩
  · rw [Finset.add_sum_erase _ S ha]; exact hsum.symm
  · refine ⟨fun w => if w = e ∨ w = a then {m a} else S w, fun w => if w = e then m a else m w,
      ?_, ?_, ?_⟩
    · intro w hw
      by_cases h1 : w = e
      · simp only [h1, true_or, ↓reduceIte]; exact RM_leaf _
      · by_cases h2 : w = a
        · simp only [h2, or_true, hea.symm, ↓reduceIte]; exact RM_leaf _
        · simp only [h1, h2, or_self, ↓reduceIte]
          exact hRM w ((Finset.mem_insert.mp hw).resolve_left h1)
    · intro w hw p hp
      by_cases h1 : w = e
      · simp only [h1, ↓reduceIte]; rw [hv p hp]; exact hval a ha p hp
      · simp only [h1, ↓reduceIte]
        exact hval w ((Finset.mem_insert.mp hw).resolve_left h1) p hp
    · rw [Finset.sum_insert he, ← Finset.add_sum_erase _ _ ha]
      simp only [true_or, or_true, ↓reduceIte]
      rw [Finset.sum_congr rfl (fun w hw => by
        have h1 := Finset.mem_erase.mp hw
        have h2 : w ≠ e := fun h => he (h ▸ h1.2)
        simp only [h2, h1.1, or_self, ↓reduceIte] :
        ∀ w ∈ I.erase a, (if w = e ∨ w = a then {m a} else S w) = S w)]
      rw [Multiset.singleton_add, Multiset.singleton_add]

-- a member of the family is complemented
theorem Fam_neg (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I.erase a)
    (hv : ∀ p < 7, val e p = !val a p) (L : Multiset ℕ) (hF : Fam L I val) :
    Ch 1 L (insert e (I.erase a)) val := by
  obtain ⟨S, m, hRM, hval, hsum⟩ := hF
  have hR : ∀ w ∈ I.erase a, w ≠ e := fun w hw h => he (h ▸ hw)
  refine ⟨S a, ∑ w ∈ I.erase a, S w, m a, ?_, hRM a ha, Or.inr ?_⟩
  · rw [Finset.add_sum_erase _ S ha]; exact hsum.symm
  · refine ⟨fun w => if w = e then {FULL ^^^ m a} else S w,
      fun w => if w = e then FULL ^^^ m a else m w, ?_, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with h | h
      · simp only [h, ↓reduceIte]; exact RM_leaf _
      · simp only [hR w h, ↓reduceIte]; exact hRM w (Finset.mem_of_mem_erase h)
    · intro w hw p hp
      rcases Finset.mem_insert.mp hw with h | h
      · simp only [h, ↓reduceIte]
        rw [FULL_bit p hp, hval a ha p hp, hv p hp]
      · simp only [hR w h, ↓reduceIte]; exact hval w (Finset.mem_of_mem_erase h) p hp
    · rw [Finset.sum_insert he]
      simp only [↓reduceIte]
      rw [Finset.sum_congr rfl (fun w hw => by simp only [hR w hw, ↓reduceIte] :
        ∀ w ∈ I.erase a, (if w = e then {FULL ^^^ m a} else S w) = S w), Multiset.singleton_add]

theorem Ch_dup (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I)
    (hv : ∀ p < 7, val e p = val a p) : ∀ b L, Ch b L I val → Ch (b + 1) L (insert e I) val := by
  intro b
  induction b with
  | zero => exact fun L h => Fam_dup I val a e ha he hv L h
  | succ b ih =>
    rintro L ⟨Sc, rest, mc, h1, h2, h3⟩
    exact ⟨Sc, rest, mc, h1, h2, h3.imp (ih _) (ih _)⟩

theorem Ch_neg (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I.erase a)
    (hv : ∀ p < 7, val e p = !val a p) :
    ∀ b L, Ch b L I val → Ch (b + 1) L (insert e (I.erase a)) val := by
  intro b
  induction b with
  | zero => exact fun L h => Fam_neg I val a e ha he hv L h
  | succ b ih =>
    rintro L ⟨Sc, rest, mc, h1, h2, h3⟩
    exact ⟨Sc, rest, mc, h1, h2, h3.imp (ih _) (ih _)⟩

-- Counting back from the last gate.

def Det (gs : List Gate) (pend D : Finset ℕ) : Prop :=
  ∀ x y : List Bool, x.length = 3 → y.length = 3 →
    (∀ i ∈ D, x.getD i false = y.getD i false) →
    ∀ w ∈ pend, (W gs x).getD w false = (W gs y).getD w false

def vl (gs : List Gate) (w p : ℕ) : Bool := (W gs (X p)).getD w false

theorem main (gs : List Gate) : (∀ g ∈ gs, Good g) → Irr gs → ∀ pend : Finset ℕ,
    (∀ w ∈ pend, w < 3 + gs.length) → (∀ w ∈ pend, ∃ p < 7, vl gs w p = false) →
    ∃ D : Finset ℕ, D ⊆ Finset.range 3 ∧ Det gs pend D ∧
      ∃ j, D.card + j ≤ pend.card + gs.length ∧
        Ch j (D.val.map lf) pend (vl gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ pend hp _
    refine ⟨pend, fun w hw => by simpa using hp w hw, fun x y _ _ h w hw => by
      simpa [W] using h w hw, 0, by simp, fun w => {lf w}, lf,
      fun w hw => RM_leaf _,
      fun w hw p hpp => by simpa [W, vl] using lf_X w (by simpa using hp w hw) p hpp, ?_⟩
    have h := Multiset.sum_map_singleton (pend.val.map lf)
    rw [Multiset.map_map] at h
    exact h
  | append_singleton gs g ih =>
    intro hg hirr pend hp hnt
    have hg' : ∀ g ∈ gs, Good g := fun g' h => hg g' (by simp [h])
    have hgg : Good g := hg g (by simp)
    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
    have IH := ih hg' (Irr_prefix gs g hirr)
    have hI := hirr gs g [] rfl
    set k := 3 + gs.length with hk
    have hlo : ∀ x : List Bool, x.length = 3 → ∀ w, w < k →
        (W (gs ++ [g]) x).getD w false = (W gs x).getD w false := by
      intro x hx w hw
      rw [W_snoc, stp, getD_lt _ _ _ (by rw [W_len, hx]; exact hw)]
    have hto : ∀ x : List Bool, x.length = 3 →
        (W (gs ++ [g]) x).getD k false = ev gs g x := by
      intro x hx
      have h := getD_len (W gs x) (ev gs g x)
      rw [W_len, hx] at h
      rw [W_snoc]; exact h
    have hvlo : ∀ w, w < k → ∀ p, vl (gs ++ [g]) w p = vl gs w p := fun w hw p =>
      hlo _ (X_len p) w hw
    have hvto : ∀ p, vl (gs ++ [g]) k p = ev gs g (X p) := fun p => hto _ (X_len p)
    have hpk : ∀ w ∈ pend, w ≠ k → w < k := by
      intro w hw hwk
      have h1 := hp w hw
      rw [hlen] at h1; omega
    have hbig : ∀ x : List Bool, x.length = 3 → ∀ i, k ≤ i → (W gs x).getD i false = false := by
      intro x hx i hi
      exact getD_big _ _ (by rw [W_len, hx]; omega)
    by_cases hkp : k ∈ pend
    swap
    · have hp' : ∀ w ∈ pend, w < k := fun w hw => hpk w hw (fun h => hkp (h ▸ hw))
      obtain ⟨D, h1, h2, j, h3, h4⟩ := IH pend hp' (fun w hw => by
        obtain ⟨p, hpp, h⟩ := hnt w hw
        exact ⟨p, hpp, by rw [← hvlo w (hp' w hw) p]; exact h⟩)
      refine ⟨D, h1, ?_, j, by rw [hlen]; omega, ?_⟩
      · intro x y hx hy hxy w hw
        rw [hlo x hx w (hp' w hw), hlo y hy w (hp' w hw)]
        exact h2 x y hx hy hxy w hw
      · exact Ch_map _ _ _ _ (Fam_congr pend _ _ fun w hw p _ => (hvlo w (hp' w hw) p).symm)
          _ _ h4
    · set E := pend.erase k with hE
      have hEc : E.card + 1 = pend.card := Finset.card_erase_add_one hkp
      have hElt : ∀ w ∈ E, w < k := fun w hw =>
        hpk w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)
      have hEnt : ∀ w ∈ E, ∃ p < 7, vl gs w p = false := by
        intro w hw
        obtain ⟨p, hpp, h⟩ := hnt w (Finset.mem_of_mem_erase hw)
        exact ⟨p, hpp, by rw [← hvlo w (hElt w hw) p]; exact h⟩
      have hpE : pend = insert k E := (Finset.insert_erase hkp).symm
      have hk1E : k + 1 ∉ E := fun h => by have := hElt _ h; omega
      have hk2E : k + 2 ∉ E := fun h => by have := hElt _ h; omega
      obtain ⟨p0, hp0, hk0⟩ := hnt k hkp
      rw [hvto p0] at hk0
      -- the gate reads two different earlier wires, or complements one
      have hcases : (∃ a b, a < k ∧ b < k ∧ a ≠ b ∧
          ((∀ x : List Bool, x.length = 3 → ev gs g x = ((W gs x).getD a false && (W gs x).getD b false)) ∨
           (∀ x : List Bool, x.length = 3 → ev gs g x = ((W gs x).getD a false || (W gs x).getD b false)))) ∨
          (∃ a, a < k ∧ ∀ x : List Bool, x.length = 3 → ev gs g x = !(W gs x).getD a false) := by
        have hcopy : ∀ a < k, (∀ x : List Bool, x.length = 3 → ev gs g x = (W gs x).getD a false) →
            False := fun a ha h => hI.1 a ha (fun p _ => h _ (X_len p))
        have hfalse : (∀ x : List Bool, x.length = 3 → ev gs g x = false) → False :=
          fun h => hI.2 (fun p _ => h _ (X_len p))
        have htrue : (∀ x : List Bool, x.length = 3 → ev gs g x = true) → False := by
          intro h
          rw [h _ (X_len p0)] at hk0; exact absurd hk0 (by simp)
        have hl2 := hgg.2
        rcases hgg.1 with ho | ho | ho
        · -- AND
          left
          rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨t, l⟩⟩⟩
          · exact (htrue fun x _ => by simp [ev, hins, ho, GateOp.eval]).elim
          · exfalso
            have he : ∀ x, ev gs g x = (W gs x).getD a false := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · exact hcopy a hak (fun x _ => he x)
            · exact hfalse (fun x hx => by rw [he x, hbig x hx a (by omega)])
          · have he : ∀ x, ev gs g x = ((W gs x).getD a false && (W gs x).getD b false) := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · by_cases hbk : b < k
              · by_cases hab : a = b
                · exact (hcopy b hbk fun x _ => by rw [he x, hab, Bool.and_self]).elim
                · exact ⟨a, b, hak, hbk, hab, Or.inl fun x _ => he x⟩
              · exact (hfalse fun x hx => by
                  rw [he x, hbig x hx b (by omega), Bool.and_false]).elim
            · exact (hfalse fun x hx => by
                rw [he x, hbig x hx a (by omega), Bool.false_and]).elim
          · rw [hins] at hl2; simp at hl2
        · -- OR
          left
          rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨t, l⟩⟩⟩
          · exact (hfalse fun x _ => by simp [ev, hins, ho, GateOp.eval]).elim
          · exfalso
            have he : ∀ x, ev gs g x = (W gs x).getD a false := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · exact hcopy a hak (fun x _ => he x)
            · exact hfalse (fun x hx => by rw [he x, hbig x hx a (by omega)])
          · have he : ∀ x, ev gs g x = ((W gs x).getD a false || (W gs x).getD b false) := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · by_cases hbk : b < k
              · by_cases hab : a = b
                · exact (hcopy b hbk fun x _ => by rw [he x, hab, Bool.or_self]).elim
                · exact ⟨a, b, hak, hbk, hab, Or.inr fun x _ => he x⟩
              · exact (hcopy a hak fun x hx => by
                  rw [he x, hbig x hx b (by omega), Bool.or_false]).elim
            · by_cases hbk : b < k
              · exact (hcopy b hbk fun x hx => by
                  rw [he x, hbig x hx a (by omega), Bool.false_or]).elim
              · exact (hfalse fun x hx => by
                  rw [he x, hbig x hx a (by omega), hbig x hx b (by omega)]; rfl).elim
          · rw [hins] at hl2; simp at hl2
        · -- NOT
          right
          rcases hins : g.inputs with _ | ⟨a, l⟩
          · exact (htrue fun x _ => by simp [ev, hins, ho, GateOp.eval]).elim
          · have he : ∀ x, ev gs g x = !(W gs x).getD a false := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · exact ⟨a, hak, fun x _ => he x⟩
            · exact (htrue fun x hx => by rw [he x, hbig x hx a (by omega)]; rfl).elim
      rcases hcases with ⟨a, b, hak, hbk, hab, hev⟩ | ⟨a, hak, hev⟩
      swap
      · -- a complement
        have hant : ∃ p < 7, vl gs a p = false := by
          by_contra hne
          push Not at hne
          exact hI.2 fun p hpp => by
            have h1 := hne p hpp
            rw [hev _ (X_len p)]
            have h2 : (W gs (X p)).getD a false = true := by simpa [vl] using h1
            rw [h2]; rfl
        have hdet : ∀ (P : Finset ℕ) D, (∀ w ∈ E, w ∈ P) → a ∈ P → Det gs P D →
            Det (gs ++ [g]) pend D := by
          intro P D hEP haP hD x y hx hy hxy w hw
          by_cases hwk : w = k
          · rw [hwk, hto x hx, hto y hy, hev x hx, hev y hy, hD x y hx hy hxy a haP]
          · have hwe : w ∈ E := Finset.mem_erase.mpr ⟨hwk, hw⟩
            rw [hlo x hx w (hElt w hwe), hlo y hy w (hElt w hwe)]
            exact hD x y hx hy hxy w (hEP w hwe)
        set v' : ℕ → ℕ → Bool := fun w p => if w = k + 1 then vl gs a p else vl (gs ++ [g]) w p with hv'
        have v'1 : ∀ p, v' (k + 1) p = vl gs a p := fun p => by simp [hv']
        have v'k : ∀ p, v' k p = ev gs g (X p) := fun p => by
          simp only [hv']
          rw [ite_eq_right (by omega), hvto p]
        have v'l : ∀ w, w < k → ∀ p, v' w p = vl gs w p := fun w hw p => by
          simp only [hv']
          rw [ite_eq_right (by omega), hvlo w hw p]
        have hstart : ∀ (P : Finset ℕ) L j, (∀ w ∈ P, w < k) → Ch j L P (vl gs) →
            Ch j L P v' := fun P L j hP h =>
          Ch_map _ _ _ _ (Fam_congr P _ _ fun w hw p _ => (v'l w (hP w hw) p).symm) _ _ h
        have hend : ∀ L j, Ch j L (insert k E) v' → Ch j L pend (vl (gs ++ [g])) := by
          intro L j h
          rw [hpE]
          refine Ch_map _ _ _ _ (Fam_congr _ _ _ fun w hw p _ => ?_) _ _ h
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rw [v'k, hvto]
          · rw [v'l w (hElt w hw), hvlo w (hElt w hw)]
        have hcomb : ∀ (P : Finset ℕ) L j c, c ∈ P → P.erase c = E →
            (∀ p, v' c p = vl gs a p) → Ch j L P v' →
            Ch (j + 1) L pend (vl (gs ++ [g])) := by
          intro P L j c hc hPE hvc h
          apply hend
          rw [← hPE]
          refine Ch_neg P v' c k hc ?_ ?_ _ _ h
          · rw [hPE]; exact Finset.notMem_erase _ _
          · intro p _
            rw [v'k, hvc, hev _ (X_len p)]; rfl
        by_cases haE : a ∈ E
        · obtain ⟨D, h1, h2, j, h3, h4⟩ := IH E hElt hEnt
          refine ⟨D, h1, hdet E D (fun w hw => hw) haE h2, j + 2, by rw [hlen]; omega, ?_⟩
          have s1 := hstart E _ j hElt h4
          have s2 := Ch_dup E v' a (k + 1) haE hk1E (fun p _ => by rw [v'1, v'l a hak]) j _ s1
          refine hcomb (insert (k + 1) E) _ _ (k + 1) (by simp) ?_ v'1 s2
          exact Finset.erase_insert hk1E
        · have hP : ∀ w ∈ insert a E, w < k := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hak
            · exact hElt w hw
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert a E) hP (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant
            · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem haE] at h3
          refine ⟨D, h1, hdet (insert a E) D (fun w hw => Finset.mem_insert_of_mem hw)
            (Finset.mem_insert_self _ _) h2, j + 1, by rw [hlen]; omega, ?_⟩
          have s1 := hstart (insert a E) _ j hP h4
          refine hcomb (insert a E) _ _ a (by simp) ?_ (v'l a hak) s1
          exact Finset.erase_insert haE
      -- neither of the two is constantly true
      have hant : (∃ p < 7, vl gs a p = false) ∧ (∃ p < 7, vl gs b p = false) := by
        rcases hev with hev | hev
        · constructor
          · by_contra hne
            push Not at hne
            exact hI.1 b hbk fun p hpp => by
              have h1 := hne p hpp
              rw [hev _ (X_len p)]
              have h2 : (W gs (X p)).getD a false = true := by simpa [vl] using h1
              rw [h2, Bool.true_and]
          · by_contra hne
            push Not at hne
            exact hI.1 a hak fun p hpp => by
              have h1 := hne p hpp
              rw [hev _ (X_len p)]
              have h2 : (W gs (X p)).getD b false = true := by simpa [vl] using h1
              rw [h2, Bool.and_true]
        · rw [hev _ (X_len p0), Bool.or_eq_false_iff] at hk0
          exact ⟨⟨p0, hp0, hk0.1⟩, ⟨p0, hp0, hk0.2⟩⟩
      -- the new family from the old one
      have hdet : ∀ (P : Finset ℕ) D, (∀ w ∈ E, w ∈ P) → a ∈ P → b ∈ P → Det gs P D →
          Det (gs ++ [g]) pend D := by
        intro P D hEP haP hbP hD x y hx hy hxy w hw
        by_cases hwk : w = k
        · rw [hwk, hto x hx, hto y hy]
          have h1 := hD x y hx hy hxy a haP
          have h2 := hD x y hx hy hxy b hbP
          rcases hev with hev | hev <;> rw [hev x hx, hev y hy, h1, h2]
        · have hwe : w ∈ E := Finset.mem_erase.mpr ⟨hwk, hw⟩
          rw [hlo x hx w (hElt w hwe), hlo y hy w (hElt w hwe)]
          exact hD x y hx hy hxy w (hEP w hwe)
      set v' : ℕ → ℕ → Bool := fun w p => if w = k + 1 then vl gs a p else
        if w = k + 2 then vl gs b p else vl (gs ++ [g]) w p with hv'
      have v'1 : ∀ p, v' (k + 1) p = vl gs a p := fun p => by simp [hv']
      have v'2 : ∀ p, v' (k + 2) p = vl gs b p := fun p => by simp [hv']
      have v'k : ∀ p, v' k p = ev gs g (X p) := fun p => by
        simp only [hv']
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hvto p]
      have v'l : ∀ w, w < k → ∀ p, v' w p = vl gs w p := fun w hw p => by
        simp only [hv']
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hvlo w hw p]
      have hstart : ∀ (P : Finset ℕ) L j, (∀ w ∈ P, w < k) → Ch j L P (vl gs) →
          Ch j L P v' := fun P L j hP h =>
        Ch_map _ _ _ _ (Fam_congr P _ _ fun w hw p _ => (v'l w (hP w hw) p).symm) _ _ h
      have hend : ∀ L j, Ch j L (insert k E) v' → Ch j L pend (vl (gs ++ [g])) := by
        intro L j h
        rw [hpE]
        refine Ch_map _ _ _ _ (Fam_congr _ _ _ fun w hw p _ => ?_) _ _ h
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rw [v'k, hvto]
        · rw [v'l w (hElt w hw), hvlo w (hElt w hw)]
      have hcomb : ∀ (P : Finset ℕ) L j c d, c ∈ P → d ∈ P → c ≠ d → (P.erase c).erase d = E →
          (∀ p, v' c p = vl gs a p) → (∀ p, v' d p = vl gs b p) → Ch j L P v' →
          Ch j L pend (vl (gs ++ [g])) := by
        intro P L j c d hc hd hcd hPE hvc hvd h
        apply hend
        rw [← hPE]
        refine Ch_map _ _ _ _ (Fam_bin P v' c d k hc hd hcd ?_ ?_) _ _ h
        · rw [hPE]; exact Finset.notMem_erase _ _
        · rcases hev with hev | hev
          · left; intro p _
            rw [v'k, hvc, hvd, hev _ (X_len p)]; rfl
          · right; intro p _
            rw [v'k, hvc, hvd, hev _ (X_len p)]; rfl
      by_cases haE : a ∈ E
      · by_cases hbE : b ∈ E
        · -- both are needed elsewhere too
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH E hElt hEnt
          refine ⟨D, h1, hdet E D (fun w hw => hw) haE hbE h2, j + 2, by rw [hlen]; omega, ?_⟩
          have s1 := hstart E _ j hElt h4
          have s2 := Ch_dup E v' a (k + 1) haE hk1E (fun p _ => by rw [v'1, v'l a hak]) j _ s1
          have s3 := Ch_dup (insert (k + 1) E) v' b (k + 2) (Finset.mem_insert_of_mem hbE)
            (by simp [hk2E]) (fun p _ => by rw [v'2, v'l b hbk]) (j + 1) _ s2
          refine hcomb (insert (k + 2) (insert (k + 1) E)) _ _ (k + 1) (k + 2) (by simp) (by simp)
            (by omega) ?_ v'1 v'2 s3
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            have := hElt w h
            exact ⟨by omega, by omega, Or.inr (Or.inr h)⟩
        · -- a is needed elsewhere, b is new
          have hP : ∀ w ∈ insert b E, w < k := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hbk
            · exact hElt w hw
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert b E) hP (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.2
            · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem hbE] at h3
          refine ⟨D, h1, hdet (insert b E) D (fun w hw => Finset.mem_insert_of_mem hw)
            (Finset.mem_insert_of_mem haE) (Finset.mem_insert_self _ _) h2, j + 1,
            by rw [hlen]; omega, ?_⟩
          have s1 := hstart (insert b E) _ j hP h4
          have s2 := Ch_dup (insert b E) v' a (k + 1) (Finset.mem_insert_of_mem haE)
            (by rw [Finset.mem_insert, not_or]; exact ⟨by omega, hk1E⟩)
            (fun p _ => by rw [v'1, v'l a hak]) j _ s1
          refine hcomb (insert (k + 1) (insert b E)) _ _ (k + 1) b (by simp) (by simp)
            (by omega) ?_ v'1 (v'l b hbk) s2
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n1
            · exact absurd h n2
            · exact h
          · intro h
            have := hElt w h
            exact ⟨fun h' => hbE (h' ▸ h), by omega, Or.inr (Or.inr h)⟩
      · have hP : ∀ w ∈ insert a E, w < k := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hak
          · exact hElt w hw
        by_cases hbE : b ∈ E
        · -- b is needed elsewhere, a is new
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert a E) hP (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.1
            · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem haE] at h3
          refine ⟨D, h1, hdet (insert a E) D (fun w hw => Finset.mem_insert_of_mem hw)
            (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hbE) h2, j + 1,
            by rw [hlen]; omega, ?_⟩
          have s1 := hstart (insert a E) _ j hP h4
          have s2 := Ch_dup (insert a E) v' b (k + 2) (Finset.mem_insert_of_mem hbE)
            (by rw [Finset.mem_insert, not_or]; exact ⟨by omega, hk2E⟩)
            (fun p _ => by rw [v'2, v'l b hbk]) j _ s1
          refine hcomb (insert (k + 2) (insert a E)) _ _ a (k + 2) (by simp) (by simp)
            (by omega) ?_ (v'l a hak) v'2 s2
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            have := hElt w h
            exact ⟨by omega, fun h' => haE (h' ▸ h), Or.inr (Or.inr h)⟩
        · -- both are new
          have hbaE : b ∉ insert a E := by
            rw [Finset.mem_insert, not_or]; exact ⟨fun h => hab h.symm, hbE⟩
          have hP2 : ∀ w ∈ insert b (insert a E), w < k := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hbk
            · exact hP w hw
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert b (insert a E)) hP2 (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.2
            · rcases Finset.mem_insert.mp hw with rfl | hw
              · exact hant.1
              · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem hbaE, Finset.card_insert_of_notMem haE] at h3
          refine ⟨D, h1, hdet _ D (fun w hw => Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem hw)) (by simp) (by simp) h2, j, by rw [hlen]; omega, ?_⟩
          have s1 := hstart _ _ j hP2 h4
          refine hcomb (insert b (insert a E)) _ _ a b (by simp) (by simp) hab ?_ (v'l a hak)
            (v'l b hbk) s1
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            exact ⟨fun h' => hbE (h' ▸ h), fun h' => haE (h' ▸ h), Or.inr (Or.inr h)⟩

-- Pairs (an input where the function is true, one where it is false): bit 8 p + t of a matrix is the
-- pair of the p-th and the t-th of them. A value is a number whose low 3 bits are its values on the
-- first kind and whose next bits are its values on the second kind.

def po (i : ℕ) : ℕ := i / 8
def zo (i : ℕ) : ℕ := 3 + i % 8
def V (i : ℕ) : Prop := i / 8 < 3 ∧ i % 8 < 4

def dn (j x : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x j)
def up (j x : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x j)
def ONE : ℕ := 65793
def FZ : ℕ := 15
def rc (x : ℕ) : ℕ := Nat.land (dn 4 (dn 2 (dn 1 x))) ONE
def cc (x : ℕ) : ℕ := Nat.land (dn 64 (dn 32 (dn 16 (dn 8 x)))) FZ
def fill (x : ℕ) : ℕ := up 4 (up 2 (up 1 x))
def rep (x : ℕ) : ℕ := up 64 (up 32 (up 16 (up 8 x)))
def mat (L n : ℕ) : ℕ := Nat.land (fill (Nat.land L ONE)) (rep (Nat.land n FZ))

theorem dn_bit (j x i : ℕ) (h : (dn j x).testBit i = true) :
    x.testBit i = true ∨ x.testBit (i + j) = true := by
  have h : (x ||| x >>> j).testBit i = true := h
  rw [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true, Nat.add_comm] at h
  exact h

theorem up_bit (j x i : ℕ) (h : (up j x).testBit i = true) :
    x.testBit i = true ∨ (j ≤ i ∧ x.testBit (i - j) = true) := by
  have h : (x ||| x <<< j).testBit i = true := h
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h

theorem land_bit (x y i : ℕ) (h : (Nat.land x y).testBit i = true) :
    x.testBit i = true ∧ y.testBit i = true := by
  have h : (x &&& y).testBit i = true := h
  rwa [Nat.testBit_and, Bool.and_eq_true] at h

theorem land_bit' (x y i : ℕ) (hx : x.testBit i = true) (hy : y.testBit i = true) :
    (Nat.land x y).testBit i = true := by
  change (x &&& y).testBit i = true
  rw [Nat.testBit_and, hx, hy]; rfl

theorem ONE_bit (i : ℕ) (h : ONE.testBit i = true) : i % 8 = 0 ∧ i / 8 < 3 := by
  by_cases hi : i < 128
  · have : ∀ i < 128, ONE.testBit i = true → i % 8 = 0 ∧ i / 8 < 3 := by decide +kernel
    exact this i hi h
  · have h1 : ONE.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc ONE < 2 ^ 128 := by decide +kernel
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h1] at h; exact absurd h (by simp)

theorem FZ_bit (t : ℕ) (h : FZ.testBit t = true) : t < 4 := by
  have e : FZ = 2 ^ 4 - 1 := by decide +kernel
  rw [e, Nat.testBit_two_pow_sub_one] at h
  simpa using h

theorem rc_bit (x j : ℕ) (h : (rc x).testBit j = true) :
    j % 8 = 0 ∧ j / 8 < 3 ∧ ∃ i, x.testBit i = true ∧ i / 8 = j / 8 := by
  have h := land_bit _ _ _ h
  have h1 := ONE_bit _ h.2
  have d : ∀ j y c : ℕ, (∀ i, y.testBit i = true → ∃ a, a ≤ c ∧ x.testBit (i + a) = true) →
      ∀ i, (dn j y).testBit i = true → ∃ a, a ≤ c + j ∧ x.testBit (i + a) = true := by
    intro j y c hy i hi
    rcases dn_bit _ _ _ hi with hi | hi
    · obtain ⟨a, h1, h2⟩ := hy i hi
      exact ⟨a, by omega, h2⟩
    · obtain ⟨a, h1, h2⟩ := hy _ hi
      exact ⟨j + a, by omega, by rw [← Nat.add_assoc]; exact h2⟩
  obtain ⟨a, h2, h3⟩ := d 4 _ _ (d 2 _ _ (d 1 x 0 (fun i hi => ⟨0, le_refl _, hi⟩))) _ h.1
  exact ⟨h1.1, h1.2, j + a, h3, by omega⟩

theorem cc_bit (x t : ℕ) (h : (cc x).testBit t = true) :
    t < 4 ∧ ∃ i, x.testBit i = true ∧ i % 8 = t := by
  have h := land_bit _ _ _ h
  have h1 := FZ_bit _ h.2
  have hd : ∀ j y : ℕ, j % 8 = 0 →
      (∀ n, y.testBit n = true → ∃ t, x.testBit t = true ∧ t % 8 = n % 8) →
      ∀ n, (dn j y).testBit n = true → ∃ t, x.testBit t = true ∧ t % 8 = n % 8 := by
    intro j y hj hy n hn
    rcases dn_bit _ _ _ hn with hn | hn
    · exact hy n hn
    · obtain ⟨t, h1, h2⟩ := hy _ hn
      exact ⟨t, h1, by omega⟩
  obtain ⟨i, h2, h3⟩ := hd 64 _ rfl (hd 32 _ rfl (hd 16 _ rfl (hd 8 x rfl (fun n hn => ⟨n, hn, rfl⟩)))) _ h.1
  exact ⟨h1, i, h2, by omega⟩

theorem fill_bit (x i : ℕ) (hx : ∀ j, x.testBit j = true → j % 8 = 0)
    (h : (fill x).testBit i = true) : x.testBit (8 * (i / 8)) = true := by
  have u : ∀ j y c : ℕ, (∀ i, y.testBit i = true → ∃ a, a ≤ c ∧ a ≤ i ∧ x.testBit (i - a) = true) →
      ∀ i, (up j y).testBit i = true → ∃ a, a ≤ c + j ∧ a ≤ i ∧ x.testBit (i - a) = true := by
    intro j y c hy i hi
    rcases up_bit _ _ _ hi with hi | ⟨hl, hi⟩
    · obtain ⟨a, h1, h2, h3⟩ := hy i hi
      exact ⟨a, by omega, h2, h3⟩
    · obtain ⟨a, h1, h2, h3⟩ := hy _ hi
      exact ⟨a + j, by omega, by omega, by rw [show i - (a + j) = i - j - a by omega]; exact h3⟩
  obtain ⟨a, h1, h2, h3⟩ := u 4 _ _ (u 2 _ _ (u 1 x 0 (fun i hi => ⟨0, le_refl _, Nat.zero_le _, hi⟩))) i h
  have h4 := hx _ h3
  rw [show 8 * (i / 8) = i - a by omega]
  exact h3

theorem rep_bit (x i : ℕ) (hx : ∀ j, x.testBit j = true → j < 8)
    (h : (rep x).testBit i = true) : x.testBit (i % 8) = true := by
  have u : ∀ j y : ℕ, j % 8 = 0 → (∀ n, y.testBit n = true → x.testBit (n % 8) = true) →
      ∀ n, (up j y).testBit n = true → x.testBit (n % 8) = true := by
    intro j y hj hy n hn
    rcases up_bit _ _ _ hn with hn | ⟨hl, hn⟩
    · exact hy n hn
    · have := hy _ hn
      rw [show n % 8 = (n - j) % 8 by omega]
      exact this
  exact u 64 _ rfl (u 32 _ rfl (u 16 _ rfl (u 8 x rfl (fun n hn => by rw [Nat.mod_eq_of_lt (hx n hn)]; exact hn)))) i h

theorem mat_bit (L n i : ℕ) (h : (mat L n).testBit i = true) :
    L.testBit (8 * (i / 8)) = true ∧ n.testBit (i % 8) = true ∧ V i := by
  have h := land_bit _ _ _ h
  have h1 := fill_bit _ i (fun j hj => (ONE_bit j (land_bit _ _ _ hj).2).1) h.1
  have h2 := rep_bit _ i (fun j hj => by
    have := FZ_bit j (land_bit _ _ _ hj).2; omega) h.2
  have h1 := land_bit _ _ _ h1
  have h2 := land_bit _ _ _ h2
  have h3 := (ONE_bit _ h1.2).2
  exact ⟨h1.1, h2.1, by omega, FZ_bit _ h2.2⟩

def matL : List ℕ → ℕ
  | [] => 0
  | r :: l => Nat.lor r (Nat.shiftLeft (matL l) 8)

theorem matL_bit : ∀ (l : List ℕ), (∀ r ∈ l, ∀ t, r.testBit t = true → t < 8) → ∀ i,
    (matL l).testBit i = true → i / 8 < l.length ∧ (l.getD (i / 8) 0).testBit (i % 8) = true := by
  intro l
  induction l with
  | nil => intro _ i h; simp [matL] at h
  | cons r l ih =>
    intro hl i h
    have h : (r ||| (matL l) <<< 8).testBit i = true := h
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have hi := hl r List.mem_cons_self i h
      rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      exact ⟨by simp, by simpa using h⟩
    · have := ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)) _ h2
      have e1 : i / 8 = (i - 8) / 8 + 1 := by omega
      have e2 : i % 8 = (i - 8) % 8 := by omega
      rw [e1, e2]
      exact ⟨by simpa using this.1, by simpa using this.2⟩

def RW : List ℕ := List.range 3

-- the pairs that x does not separate
def ns (x : ℕ) : ℕ := matL (RW.map fun r => bif Nat.testBit x r then Nat.land (Nat.shiftRight x 3) FZ else FZ)

theorem row_bit (x t : ℕ) (h : (Nat.land (Nat.shiftRight x 3) FZ).testBit t = true) :
    t < 4 ∧ x.testBit (3 + t) = true := by
  have h := land_bit _ _ _ h
  have h1 : (x >>> 3).testBit t = true := h.1
  rw [Nat.testBit_shiftRight] at h1
  exact ⟨FZ_bit t h.2, h1⟩

theorem ns_bit (x i : ℕ) (h : (ns x).testBit i = true) : V i ∧
    ¬ (x.testBit (po i) = true ∧ x.testBit (zo i) = false) := by
  have hr : ∀ r ∈ RW.map (fun r => bif Nat.testBit x r then Nat.land (Nat.shiftRight x 3) FZ else FZ), ∀ t,
      r.testBit t = true → t < 4 := by
    intro r hr t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    cases hp : Nat.testBit x p
    · rw [hp] at ht; exact FZ_bit t ht
    · rw [hp] at ht; exact (row_bit x t ht).1
  obtain ⟨h1, h2⟩ := matL_bit _ (fun r hr' t ht => by
    have := hr r hr' t ht; omega) i h
  have hlen : i / 8 < RW.length := by simpa using h1
  have hlo : i / 8 < 3 := by simpa [RW] using hlen
  have e : (RW.map (fun r => bif Nat.testBit x r then Nat.land (Nat.shiftRight x 3) FZ else FZ)).getD (i / 8) 0 =
      (bif Nat.testBit x (po i) then Nat.land (Nat.shiftRight x 3) FZ else FZ) := by
    unfold po
    rw [List.getD_eq_getElem _ _ h1, List.getElem_map]
    simp [RW]
  have hlt : i % 8 < 4 := by
    apply hr _ _ _ h2
    rw [List.getD_eq_getElem _ _ h1]
    exact List.getElem_mem _
  refine ⟨⟨hlo, hlt⟩, ?_⟩
  rintro ⟨h3, h4⟩
  rw [e, h3] at h2
  have := (row_bit x _ h2).2
  unfold zo at h4
  rw [h4] at this; exact absurd this (by simp)

theorem po_ok (i : ℕ) (h : V i) : po i < 7 ∧ MM.testBit (po i) = true := by
  have h1 : po i < 3 := h.1
  refine ⟨by omega, ?_⟩
  unfold MM; rw [Nat.testBit_two_pow_sub_one]; simpa using h1

theorem zo_ok (i : ℕ) (h : V i) : zo i < 7 ∧ MM.testBit (zo i) = false := by
  have h1 := h.2
  refine ⟨by unfold zo; omega, ?_⟩
  unfold MM zo; rw [Nat.testBit_two_pow_sub_one]; simp

def AL : ℕ := 2 ^ 128 - 1

def nsl (l : List ℕ) : ℕ := l.foldr (fun x acc => Nat.land x acc) AL

theorem nsl_bit (l : List ℕ) (i : ℕ) (h : (nsl l).testBit i = true) :
    ∀ x ∈ l, x.testBit i = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h' := land_bit x (nsl l) i h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h'.1
    · exact ih h'.2 y hy

-- force a number to its literal before going on
def frc {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  match x with
  | 0 => k 0
  | n + 1 => k (Nat.succ n)

theorem frc_eq {α : Type} (x : ℕ) (k : ℕ → α) : frc x k = k x := by cases x <;> rfl

theorem bit_of_ne (x : ℕ) (h : Nat.beq x 0 = false) : ∃ i, x.testBit i = true := by
  by_contra hno
  push Not at hno
  have : x = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.zero_testBit]
    simpa using hno i
  rw [this] at h; exact absurd h (by decide)

def splits {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: l => (splits l).flatMap fun s => [(x :: s.1, s.2), (s.1, x :: s.2)]

theorem mem_splits {α : Type} (f : α → ℕ) : ∀ (l : List α) (A B : Multiset ℕ), (↑(l.map f) : Multiset ℕ) = A + B →
    ∃ s ∈ splits l, (↑(s.1.map f) : Multiset ℕ) = A ∧ (↑(s.2.map f) : Multiset ℕ) = B ∧
      (∀ x ∈ s.1, x ∈ l) ∧ (∀ x ∈ s.2, x ∈ l) ∧ s.1.length + s.2.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro A B h
    have h0 : A + B = 0 := by rw [← h]; rfl
    obtain ⟨h1, h2⟩ := add_eq_zero.mp h0
    exact ⟨([], []), by simp [splits], by rw [h1]; rfl, by rw [h2]; rfl, by simp, by simp, rfl⟩
  | cons x l ih =>
    intro A B h
    have hx : f x ∈ A + B := by rw [← h]; simp
    rcases Multiset.mem_add.mp hx with hx | hx
    · obtain ⟨A', rfl⟩ := Multiset.exists_cons_of_mem hx
      have h' : (↑(l.map f) : Multiset ℕ) = A' + B := by
        rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add] at h
        exact (Multiset.cons_inj_right _).mp h
      obtain ⟨s, hs, e1, e2, e3, e4, e5⟩ := ih A' B h'
      refine ⟨(x :: s.1, s.2), ?_, ?_, e2, ?_, ?_, ?_⟩
      · simp only [splits, List.mem_flatMap]
        exact ⟨s, hs, by simp⟩
      · rw [List.map_cons, ← Multiset.cons_coe, e1]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · simp [e3 y hy]
      · intro y hy; simp [e4 y hy]
      · simp only [List.length_cons]; omega
    · obtain ⟨B', rfl⟩ := Multiset.exists_cons_of_mem hx
      have h' : (↑(l.map f) : Multiset ℕ) = A + B' := by
        rw [List.map_cons, ← Multiset.cons_coe, Multiset.add_cons] at h
        exact (Multiset.cons_inj_right _).mp h
      obtain ⟨s, hs, e1, e2, e3, e4, e5⟩ := ih A B' h'
      refine ⟨(s.1, x :: s.2), ?_, e1, ?_, ?_, ?_, ?_⟩
      · simp only [splits, List.mem_flatMap]
        exact ⟨s, hs, by simp⟩
      · rw [List.map_cons, ← Multiset.cons_coe, e2]
      · intro y hy; simp [e3 y hy]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · simp [e4 y hy]
      · simp only [List.length_cons]; omega

-- m is true on the rows of L and false on the columns of n (when both are there)
def Sep (L n m : ℕ) : Prop := ∀ p t, p < 3 → t < 4 → L.testBit (8 * p) = true →
  n.testBit t = true → m.testBit p = true ∧ m.testBit (3 + t) = false

theorem RM_inv (S : Multiset ℕ) (m : ℕ) (h : RM S m) : S = {m} ∨
    ∃ A B a b, S = A + B ∧ A ≠ 0 ∧ B ≠ 0 ∧ RM A a ∧ RM B b ∧ (m = a &&& b ∨ m = a ||| b) := by
  have key := h (fun S m => RM S m ∧ S ≠ 0 ∧ (S = {m} ∨
    ∃ A B a b, S = A + B ∧ A ≠ 0 ∧ B ≠ 0 ∧ RM A a ∧ RM B b ∧ (m = a &&& b ∨ m = a ||| b)))
    (fun x => ⟨RM_leaf x, by simp, Or.inl rfl⟩)
    (fun S T a b hS hT => ⟨⟨RM_and hS.1 hT.1, fun h => hS.2.1 (add_eq_zero.mp h).1,
        Or.inr ⟨S, T, a, b, rfl, hS.2.1, hT.2.1, hS.1, hT.1, Or.inl rfl⟩⟩,
      ⟨RM_or hS.1 hT.1, fun h => hS.2.1 (add_eq_zero.mp h).1,
        Or.inr ⟨S, T, a, b, rfl, hS.2.1, hT.2.1, hS.1, hT.1, Or.inr rfl⟩⟩⟩)
  exact key.2.2

-- a formula over leaves that do not separate a pair does not separate it
theorem RM_un (p t : ℕ) (S : Multiset ℕ) (m : ℕ) (h : RM S m) :
    (∀ v ∈ S, ¬ (v.testBit p = true ∧ v.testBit t = false)) →
      ¬ (m.testBit p = true ∧ m.testBit t = false) := by
  refine h (fun S m => (∀ v ∈ S, ¬ (v.testBit p = true ∧ v.testBit t = false)) →
      ¬ (m.testBit p = true ∧ m.testBit t = false)) (fun x hx => hx x (by simp)) ?_
  intro S T a b hS hT
  constructor
  · intro hv
    have h1 := hS (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inl hv')))
    have h2 := hT (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inr hv')))
    rw [Nat.testBit_and, Nat.testBit_and]
    cases hap : a.testBit p <;> cases hat : a.testBit t <;> cases hbp : b.testBit p <;>
      cases hbt : b.testBit t <;> simp_all
  · intro hv
    have h1 := hS (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inl hv')))
    have h2 := hT (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inr hv')))
    rw [Nat.testBit_or, Nat.testBit_or]
    cases hap : a.testBit p <;> cases hat : a.testBit t <;> cases hbp : b.testBit p <;>
      cases hbt : b.testBit t <;> simp_all

-- same, when every leaf takes the same value on both
theorem RM_eq (p t : ℕ) (S : Multiset ℕ) (m : ℕ) (h : RM S m) :
    (∀ v ∈ S, v.testBit p = v.testBit t) → m.testBit p = m.testBit t := by
  refine h (fun S m => (∀ v ∈ S, v.testBit p = v.testBit t) → m.testBit p = m.testBit t)
    (fun x hx => hx x (by simp)) ?_
  intro S T a b hS hT
  constructor
  · intro hv
    rw [Nat.testBit_and, Nat.testBit_and, hS (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inl hv'))),
      hT (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inr hv')))]
  · intro hv
    rw [Nat.testBit_or, Nat.testBit_or, hS (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inl hv'))),
      hT (fun v hv' => hv v (Multiset.mem_add.mpr (Or.inr hv')))]

theorem or_cond (L n m a b x y : ℕ) (A B : Multiset ℕ) (hm : Sep L n m) (e : m = a ||| b)
    (hA : RM A a) (hB : RM B b) (hx : ∀ i, x.testBit i = true → (mat L n).testBit i = true ∧
      ∀ v ∈ A, (ns v).testBit i = true)
    (hy : ∀ i, y.testBit i = true → (mat L n).testBit i = true ∧ ∀ v ∈ B, (ns v).testBit i = true) :
    Nat.beq (Nat.land (rc x) (rc y)) 0 = true ∧ Sep (rc y) n a ∧ Sep (rc x) n b := by
  have key : ∀ (z c : ℕ) (C : Multiset ℕ), RM C c → (∀ q, m.testBit q = false → c.testBit q = false) →
      (∀ i, z.testBit i = true → (mat L n).testBit i = true ∧ ∀ v ∈ C, (ns v).testBit i = true) →
      ∀ j, (rc z).testBit j = true → j % 8 = 0 ∧ c.testBit (j / 8) = false ∧
        L.testBit (8 * (j / 8)) = true ∧ m.testBit (j / 8) = true := by
    intro z c C hC hc hz j hj
    obtain ⟨h1, h2, i, h3, h4⟩ := rc_bit z j hj
    obtain ⟨h5, h6⟩ := hz i h3
    obtain ⟨h7, h8, h9⟩ := mat_bit _ _ _ h5
    have h10 := hm (i / 8) (i % 8) h9.1 h9.2 h7 h8
    have h11 := RM_un (po i) (zo i) C c hC (fun v hv => (ns_bit v i (h6 v hv)).2)
    have h12 : c.testBit (po i) = false := by
      by_contra h
      exact h11 ⟨by simpa using h, hc _ h10.2⟩
    rw [h4] at h7 h10
    unfold po at h12
    rw [h4] at h12
    exact ⟨h1, h12, h7, h10.1⟩
  have ha : ∀ q, m.testBit q = false → a.testBit q = false := by
    intro q hq
    rw [e, Nat.testBit_or, Bool.or_eq_false_iff] at hq
    exact hq.1
  have hb : ∀ q, m.testBit q = false → b.testBit q = false := by
    intro q hq
    rw [e, Nat.testBit_or, Bool.or_eq_false_iff] at hq
    exact hq.2
  have kx := key x a A hA ha hx
  have ky := key y b B hB hb hy
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    obtain ⟨j, hj⟩ := bit_of_ne _ (Bool.eq_false_iff.mpr h)
    have hj := land_bit _ _ _ hj
    have h1 := (kx j hj.1)
    have h2 := (ky j hj.2)
    have h3 := h1.2.2.2
    rw [e, Nat.testBit_or, h1.2.1, h2.2.1] at h3
    exact absurd h3 (by simp)
  · intro p t hp ht hL hn
    have h1 := ky _ hL
    rw [Nat.mul_div_cancel_left p (by norm_num)] at h1
    have h2 := hm p t hp ht h1.2.2.1 hn
    refine ⟨?_, ha _ h2.2⟩
    have h3 := h2.1
    rw [e, Nat.testBit_or, h1.2.1] at h3
    simpa using h3
  · intro p t hp ht hL hn
    have h1 := kx _ hL
    rw [Nat.mul_div_cancel_left p (by norm_num)] at h1
    have h2 := hm p t hp ht h1.2.2.1 hn
    refine ⟨?_, hb _ h2.2⟩
    have h3 := h2.1
    rw [e, Nat.testBit_or, h1.2.1] at h3
    simpa using h3

theorem and_cond (L n m a b x y : ℕ) (A B : Multiset ℕ) (hm : Sep L n m) (e : m = a &&& b)
    (hA : RM A a) (hB : RM B b) (hx : ∀ i, x.testBit i = true → (mat L n).testBit i = true ∧
      ∀ v ∈ A, (ns v).testBit i = true)
    (hy : ∀ i, y.testBit i = true → (mat L n).testBit i = true ∧ ∀ v ∈ B, (ns v).testBit i = true) :
    Nat.beq (Nat.land (cc x) (cc y)) 0 = true ∧ Sep L (cc y) a ∧ Sep L (cc x) b := by
  have key : ∀ (z c : ℕ) (C : Multiset ℕ), RM C c → (∀ q, m.testBit q = true → c.testBit q = true) →
      (∀ i, z.testBit i = true → (mat L n).testBit i = true ∧ ∀ v ∈ C, (ns v).testBit i = true) →
      ∀ t, (cc z).testBit t = true → c.testBit (3 + t) = true ∧
        n.testBit t = true ∧ m.testBit (3 + t) = false := by
    intro z c C hC hc hz t ht
    obtain ⟨h1, i, h3, h4⟩ := cc_bit z t ht
    obtain ⟨h5, h6⟩ := hz i h3
    obtain ⟨h7, h8, h9⟩ := mat_bit _ _ _ h5
    have h10 := hm (i / 8) (i % 8) h9.1 h9.2 h7 h8
    have h11 := RM_un (po i) (zo i) C c hC (fun v hv => (ns_bit v i (h6 v hv)).2)
    have h12 : c.testBit (zo i) = true := by
      by_contra h
      exact h11 ⟨hc _ h10.1, by simpa using h⟩
    unfold zo at h12
    rw [h4] at h8 h10 h12
    exact ⟨h12, h8, h10.2⟩
  have ha : ∀ q, m.testBit q = true → a.testBit q = true := by
    intro q hq
    rw [e, Nat.testBit_and, Bool.and_eq_true] at hq
    exact hq.1
  have hb : ∀ q, m.testBit q = true → b.testBit q = true := by
    intro q hq
    rw [e, Nat.testBit_and, Bool.and_eq_true] at hq
    exact hq.2
  have kx := key x a A hA ha hx
  have ky := key y b B hB hb hy
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    obtain ⟨j, hj⟩ := bit_of_ne _ (Bool.eq_false_iff.mpr h)
    have hj := land_bit _ _ _ hj
    have h1 := (kx j hj.1)
    have h2 := (ky j hj.2)
    have h3 := h1.2.2
    rw [e, Nat.testBit_and, h1.1, h2.1] at h3
    exact absurd h3 (by simp)
  · intro p t hp ht hL hn
    have h1 := ky _ hn
    have h2 := hm p t hp ht hL h1.2.1
    refine ⟨ha _ h2.1, ?_⟩
    have h3 := h2.2
    rw [e, Nat.testBit_and, h1.1] at h3
    simpa using h3
  · intro p t hp ht hL hn
    have h1 := kx _ hn
    have h2 := hm p t hp ht hL h1.2.1
    refine ⟨hb _ h2.1, ?_⟩
    have h3 := h2.2
    rw [e, Nat.testBit_and, h1.1] at h3
    simpa using h3

def VALS : ℕ := 0x731ad25d84c000

def NV : ℕ := 8

def GS : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6], [0, 2, 1, 3, 5, 4, 6], [1, 2, 0, 3, 6, 4, 5]]

def ID : List ℕ := List.range 7

-- The table of refuted relations. A list of leaves is coded by a number, in base 1024.

def vv (i : ℕ) : ℕ := Nat.land (Nat.shiftRight VALS (7 * i)) 127

def enc : List ℕ → ℕ
  | [] => 0
  | x :: l => Nat.add (Nat.mul (enc l) 1024) x

def dc : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, k => bif Nat.beq k 0 then [] else (k % 1024) :: dc f (k / 1024)

def Ok (l : List ℕ) : Prop := ∀ x ∈ l, 1 ≤ x ∧ x < 1024

theorem dc_enc : ∀ (l : List ℕ), Ok l → ∀ f, l.length ≤ f → dc f (enc l) = l := by
  intro l
  induction l with
  | nil =>
    intro _ f _
    cases f <;> rfl
  | cons x l ih =>
    intro h f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hx := h x (by simp)
    have e : enc (x :: l) = enc l * 1024 + x := rfl
    have h0 : Nat.beq (enc (x :: l)) 0 = false := by
      apply Bool.eq_false_iff.mpr; rw [Ne, Nat.beq_eq]; omega
    have h1 : enc (x :: l) % 1024 = x := by omega
    have h2 : enc (x :: l) / 1024 = enc l := by omega
    rw [dc, h0, h1, h2, ih (fun y hy => h y (by simp [hy])) f (by simp at hf; omega)]
    rfl

def Nof (l : List ℕ) (L n : ℕ) : Prop := ∀ m, RM ↑(l.map vv) m → ¬ Sep L n m

def LookOK (N : ℕ) (look : ℕ → ℕ → ℕ → Bool) : Prop := ∀ l L n, Ok l → l.length < N → l.length ≤ 16 →
  look (enc l) L n = true → Nof l L n

theorem Sep_sub (L n L' n' m : ℕ) (hL : Nat.land L' L = L') (hn : Nat.land n' n = n')
    (h : Sep L n m) : Sep L' n' m := by
  intro p t hp ht h1 h2
  rw [← hL] at h1
  rw [← hn] at h2
  exact h p t hp ht (land_bit _ _ _ h1).2 (land_bit _ _ _ h2).2

def quick (pa pb : ℕ) : Bool :=
  frc (Nat.land (rc pa) (rc pb)) fun x => bif Nat.beq x 0 then false else
    frc (Nat.land (cc pa) (cc pb)) fun y => !(Nat.beq y 0)

def fin (look : ℕ → ℕ → ℕ → Bool) (L n kA pa kB pb : ℕ) : Bool :=
  (frc (rc pa) fun fx => frc (rc pb) fun fb =>
    frc (Nat.land fx fb) fun x => bif Nat.beq x 0 then look kA fb n || look kB fx n else true) &&
  (frc (cc pa) fun cx => frc (cc pb) fun cb =>
    frc (Nat.land cx cb) fun x => bif Nat.beq x 0 then look kA L cb || look kB L cx else true)

-- every way to put the leaves left on the two sides is refuted
def go (look : ℕ → ℕ → ℕ → Bool) (P L n : ℕ) :
    List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], kA, a, kB, b, _ => Nat.beq kB 0 ||
      (frc (Nat.land P a) fun pa => frc (Nat.land P b) fun pb => fin look L n kA pa kB pb)
  | t :: l, kA, a, kB, b, w =>
      (frc (Nat.land P (Nat.land a t.2.2)) fun pa => frc (Nat.land P (Nat.land b t.2.2)) fun pb =>
        quick pa pb) ||
      ((Nat.beq (Nat.succ t.1) w ||
        (frc (Nat.add (Nat.mul kA 1024) t.1) fun kA' => frc (Nat.land a t.2.1) fun a' =>
          go look P L n l kA' a' kB b 0)) &&
       (frc (Nat.add (Nat.mul kB 1024) t.1) fun kB' => frc (Nat.land b t.2.1) fun b' =>
          go look P L n l kA a kB' b' (Nat.succ t.1)))

def Tr : List ℕ → List (ℕ × ℕ × ℕ)
  | [] => []
  | x :: l => frc (ns (vv x)) fun n => (fun r => frc (Nat.land n (r.headD (0, 0, AL)).2.2) fun u =>
      (x, n, u) :: r) (Tr l)

def TrOK : List (ℕ × ℕ × ℕ) → List ℕ → Prop
  | [], [] => True
  | t :: r, x :: l => t.1 = x ∧ t.2.1 = ns (vv x) ∧
      (∀ i, t.2.2.testBit i = true → ∀ y ∈ x :: l, (ns (vv y)).testBit i = true) ∧ TrOK r l
  | _, _ => False

theorem Tr_ok : ∀ l, TrOK (Tr l) l ∧ ∀ i, ((Tr l).headD (0, 0, AL)).2.2.testBit i = true →
    ∀ y ∈ l, (ns (vv y)).testBit i = true := by
  intro l
  induction l with
  | nil => exact ⟨trivial, by simp⟩
  | cons x l ih =>
    have e : Tr (x :: l) = (x, ns (vv x), Nat.land (ns (vv x)) ((Tr l).headD (0, 0, AL)).2.2) :: Tr l := by
      rw [Tr, frc_eq]; beta_reduce; rw [frc_eq]
    have hu : ∀ i, (Nat.land (ns (vv x)) ((Tr l).headD (0, 0, AL)).2.2).testBit i = true →
        ∀ y ∈ x :: l, (ns (vv y)).testBit i = true := by
      intro i hi y hy
      have hi := land_bit _ _ _ hi
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hi.1
      · exact ih.2 i hi.2 y hy
    rw [e]
    exact ⟨⟨rfl, rfl, hu, ih.1⟩, hu⟩

def Acc (A : Multiset ℕ) (a : ℕ) : Prop := ∀ i, a.testBit i = true → ∀ v ∈ A, (ns v).testBit i = true

theorem fin_sound (look : ℕ → ℕ → ℕ → Bool) (L n m a b : ℕ) (N : ℕ) (hk : LookOK N look)
    (lA lB : List ℕ) (oA : Ok lA) (oB : Ok lB) (nA : lA.length < N) (nB : lB.length < N)
    (sA : lA.length ≤ 16) (sB : lB.length ≤ 16) (hA : RM ↑(lA.map vv) a) (hB : RM ↑(lB.map vv) b)
    (x y : ℕ) (hx : Acc ↑(lA.map vv) x) (hy : Acc ↑(lB.map vv) y) (hm : Sep L n m)
    (e : m = a &&& b ∨ m = a ||| b)
    (h : fin look L n (enc lA) (Nat.land (mat L n) x) (enc lB) (Nat.land (mat L n) y) = true) : False := by
  have hx' : ∀ i, (Nat.land (mat L n) x).testBit i = true → (mat L n).testBit i = true ∧
      ∀ v ∈ (↑(lA.map vv) : Multiset ℕ), (ns v).testBit i = true := fun i hi =>
    ⟨(land_bit _ _ _ hi).1, hx i (land_bit _ _ _ hi).2⟩
  have hy' : ∀ i, (Nat.land (mat L n) y).testBit i = true → (mat L n).testBit i = true ∧
      ∀ v ∈ (↑(lB.map vv) : Multiset ℕ), (ns v).testBit i = true := fun i hi =>
    ⟨(land_bit _ _ _ hi).1, hy i (land_bit _ _ _ hi).2⟩
  unfold fin at h
  rw [Bool.and_eq_true] at h
  simp only [frc_eq] at h
  rcases e with e | e
  · obtain ⟨h1, h2, h3⟩ := and_cond L n m a b _ _ _ _ hm e hA hB hx' hy'
    have h := h.2
    rw [h1] at h
    simp only [cond_true, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hk lA _ _ oA nA sA h a hA h2
    · exact hk lB _ _ oB nB sB h b hB h3
  · obtain ⟨h1, h2, h3⟩ := or_cond L n m a b _ _ _ _ hm e hA hB hx' hy'
    have h := h.1
    rw [h1] at h
    simp only [cond_true, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hk lA _ _ oA nA sA h a hA h2
    · exact hk lB _ _ oB nB sB h b hB h3

theorem quick_sound (L n m a b x y : ℕ) (A B : Multiset ℕ) (hA : RM A a) (hB : RM B b)
    (hx : Acc A x) (hy : Acc B y) (hm : Sep L n m) (e : m = a &&& b ∨ m = a ||| b)
    (h : quick (Nat.land (mat L n) x) (Nat.land (mat L n) y) = true) : False := by
  have hx' : ∀ i, (Nat.land (mat L n) x).testBit i = true → (mat L n).testBit i = true ∧
      ∀ v ∈ A, (ns v).testBit i = true := fun i hi =>
    ⟨(land_bit _ _ _ hi).1, hx i (land_bit _ _ _ hi).2⟩
  have hy' : ∀ i, (Nat.land (mat L n) y).testBit i = true → (mat L n).testBit i = true ∧
      ∀ v ∈ B, (ns v).testBit i = true := fun i hi =>
    ⟨(land_bit _ _ _ hi).1, hy i (land_bit _ _ _ hi).2⟩
  unfold quick at h
  simp only [frc_eq] at h
  rcases e with e | e
  · have h1 := (and_cond L n m a b _ _ _ _ hm e hA hB hx' hy').1
    cases h2 : Nat.beq (Nat.land (rc (Nat.land (mat L n) x)) (rc (Nat.land (mat L n) y))) 0
    · rw [h2, cond_false, h1] at h; exact absurd h (by simp)
    · rw [h2, cond_true] at h; exact absurd h (by simp)
  · have h1 := (or_cond L n m a b _ _ _ _ hm e hA hB hx' hy').1
    rw [h1, cond_true] at h
    exact absurd h (by simp)

theorem Acc_add (A B : Multiset ℕ) (x y : ℕ) (hx : Acc A x) (hy : Acc B y) :
    Acc (A + B) (Nat.land x y) := by
  intro i hi v hv
  have hi := land_bit _ _ _ hi
  rcases Multiset.mem_add.mp hv with h | h
  · exact hx i hi.1 v h
  · exact hy i hi.2 v h

theorem Acc_le (A B : Multiset ℕ) (x : ℕ) (hx : Acc A x) (h : B ≤ A) : Acc B x :=
  fun i hi v hv => hx i hi v (Multiset.mem_of_le h hv)

theorem go_sound (look : ℕ → ℕ → ℕ → Bool) (L n m a b : ℕ) (N : ℕ) (hk : LookOK N look)
    (hm : Sep L n m) (e : m = a &&& b ∨ m = a ||| b) :
    ∀ (l : List ℕ) (tr : List (ℕ × ℕ × ℕ)), TrOK tr l → ∀ (lA lB : List ℕ) (RA RB : Multiset ℕ)
      (x y w : ℕ), (↑l : Multiset ℕ) = RA + RB → Ok l → Ok lA → Ok lB → 1 ≤ lA.length →
      lA.length + lB.length + l.length ≤ N → lA.length + lB.length + l.length ≤ 16 →
      (∀ i, w = i + 1 → i ∉ RA) → (lB = [] → RB ≠ 0) →
      RM (↑(lA.map vv) + RA.map vv) a → RM (↑(lB.map vv) + RB.map vv) b →
      Acc ↑(lA.map vv) x → Acc ↑(lB.map vv) y →
      go look (mat L n) L n tr (enc lA) x (enc lB) y w = true → False := by
  intro l
  induction l with
  | nil =>
    intro tr htr lA lB RA RB x y w hl _ oA oB h1 hN h16 _ hB0 hA hB hx hy h
    have h0 : RA + RB = 0 := by rw [← hl]; rfl
    obtain ⟨r1, r2⟩ := add_eq_zero.mp h0
    rw [r1, Multiset.map_zero, add_zero] at hA
    rw [r2, Multiset.map_zero, add_zero] at hB
    have hlB : lB ≠ [] := fun h => hB0 h r2
    have hlB1 : 1 ≤ lB.length := List.length_pos_of_ne_nil hlB
    cases tr with
    | cons t r => exact htr.elim
    | nil =>
      rw [go, Bool.or_eq_true, frc_eq, frc_eq] at h
      rcases h with h | h
      · rw [Nat.beq_eq] at h
        cases lB with
        | nil => exact hlB rfl
        | cons v lB =>
          have e1 : enc (v :: lB) = enc lB * 1024 + v := rfl
          have := oB v (by simp)
          omega
      · simp only [List.length_nil] at hN h16
        exact fin_sound look L n m a b N hk lA lB oA oB (by omega) (by omega) (by omega) (by omega) hA hB x y
          hx hy hm e h
  | cons v l ih =>
    intro tr htr lA lB RA RB x y w hl ol oA oB h1 hN h16 hw hB0 hA hB hx hy h
    cases tr with
    | nil => exact htr.elim
    | cons t r =>
      obtain ⟨t1, t2, t3, t4⟩ := htr
      have hRA : RA ≤ ↑(v :: l) := by rw [hl]; exact Multiset.le_add_right _ _
      have hRB : RB ≤ ↑(v :: l) := by rw [hl]; exact Multiset.le_add_left _ _
      have hu : Acc (Multiset.map vv ↑(v :: l)) t.2.2 := by
        intro i hi z hz
        obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hz
        exact t3 i hi y' (by simpa using hy')
      rw [go, Bool.or_eq_true, frc_eq, frc_eq] at h
      rcases h with h | h
      · exact quick_sound L n m a b _ _ _ _ hA hB
          (Acc_add _ _ _ _ hx (Acc_le _ _ _ hu (Multiset.map_le_map hRA)))
          (Acc_add _ _ _ _ hy (Acc_le _ _ _ hu (Multiset.map_le_map hRB))) hm e h
      · rw [Bool.and_eq_true, Bool.or_eq_true, t1, t2] at h
        simp only [frc_eq] at h
        have ov := ol v (by simp)
        have ol' : Ok l := fun z hz => ol z (by simp [hz])
        simp only [List.length_cons] at hN h16
        have hv : v ∈ RA + RB := by rw [← hl]; simp
        by_cases hvA : v ∈ RA
        · obtain ⟨RA', rfl⟩ := Multiset.exists_cons_of_mem hvA
          have hl' : (↑l : Multiset ℕ) = RA' + RB := by
            rw [← Multiset.cons_coe, Multiset.cons_add] at hl
            exact (Multiset.cons_inj_right v).mp hl
          have h := h.1.resolve_left (fun hb => hw v (by rw [Nat.beq_eq] at hb; exact hb.symm) (by simp))
          refine ih r t4 (v :: lA) lB RA' RB _ y 0 hl' ol' ?_ oB (by simp) (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (fun i hi => by omega) hB0 ?_ hB ?_ hy h
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact ov
            · exact oA z hz
          · rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add]
            rw [Multiset.map_cons, Multiset.add_cons] at hA
            exact hA
          · intro i hi z hz
            have hi := land_bit _ _ _ hi
            rw [List.map_cons, ← Multiset.cons_coe, Multiset.mem_cons] at hz
            rcases hz with rfl | hz
            · exact hi.2
            · exact hx i hi.1 z hz
        · have hvB : v ∈ RB := (Multiset.mem_add.mp hv).resolve_left hvA
          obtain ⟨RB', rfl⟩ := Multiset.exists_cons_of_mem hvB
          have hl' : (↑l : Multiset ℕ) = RA + RB' := by
            rw [← Multiset.cons_coe, Multiset.add_cons] at hl
            exact (Multiset.cons_inj_right v).mp hl
          refine ih r t4 lA (v :: lB) RA RB' x _ (Nat.succ v) hl' ol' oA ?_ h1 (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (fun i hi => ?_) (by simp) hA ?_ hx ?_ h.2
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact ov
            · exact oB z hz
          · have : i = v := by omega
            rw [this]; exact hvA
          · rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add]
            rw [Multiset.map_cons, Multiset.add_cons] at hB
            exact hB
          · intro i hi z hz
            have hi := land_bit _ _ _ hi
            rw [List.map_cons, ← Multiset.cons_coe, Multiset.mem_cons] at hz
            rcases hz with rfl | hz
            · exact hi.2
            · exact hy i hi.1 z hz

-- the refutation of one relation
def rf (look : ℕ → ℕ → ℕ → Bool) (l : List ℕ) (L n : ℕ) : Bool :=
  match Tr l with
  | [] => true
  | t :: r => frc (mat L n) fun P =>
      (frc (Nat.land P t.2.2) fun x => !(Nat.beq x 0)) ||
      (bif r.isEmpty then false else go look P L n r t.1 t.2.1 0 AL 0)

theorem Acc_nil (x : ℕ) : Acc 0 x := fun i _ v hv => by simp at hv

-- the leaves together do not separate some pair
theorem all_un (S : Multiset ℕ) (L n m u : ℕ) (hm : Sep L n m) (hR : RM S m) (hu : Acc S u)
    (h : Nat.beq (Nat.land (mat L n) u) 0 = false) : False := by
  obtain ⟨i, hi⟩ := bit_of_ne _ h
  have hi := land_bit _ _ _ hi
  obtain ⟨h1, h2, h3⟩ := mat_bit _ _ _ hi.1
  have h4 := hm (i / 8) (i % 8) h3.1 h3.2 h1 h2
  exact RM_un (po i) (zo i) S m hR (fun v hv => (ns_bit v i (hu i hi.2 v hv)).2) h4

theorem rf_sound (look : ℕ → ℕ → ℕ → Bool) (l : List ℕ) (L n : ℕ) (hk : LookOK l.length look)
    (hl : Ok l) (h16 : l.length ≤ 16) (h : rf look l L n = true) : Nof l L n := by
  intro m hR hm
  have htr := Tr_ok l
  unfold rf at h
  cases l with
  | nil =>
    rcases RM_inv _ _ hR with h | ⟨A, B, a, b, h, hA, _⟩
    · have := congrArg Multiset.card h; simp at this
    · exact hA (add_eq_zero.mp h.symm).1
  | cons v l =>
    cases hT : Tr (v :: l) with
    | nil => rw [hT] at htr; exact htr.1.elim
    | cons t r =>
      rw [hT] at h htr
      obtain ⟨⟨t1, t2, t3, t4⟩, _⟩ := htr
      simp only [frc_eq] at h
      rw [Bool.or_eq_true] at h
      have hu : Acc ↑((v :: l).map vv) t.2.2 := by
        intro i hi z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hz)
        exact t3 i hi y hy
      rcases h with h | h
      · exact all_un _ L n m _ hm hR hu (by simpa using h)
      · cases hr : r.isEmpty
        swap
        · rw [hr, cond_true] at h; exact absurd h (by simp)
        rw [hr, cond_false, t1, t2] at h
        rcases RM_inv _ _ hR with h1 | ⟨A, B, a, b, hS, hA0, hB0, hA, hB, e⟩
        · have hc := congrArg Multiset.card h1
          simp at hc
          rw [hc] at t4
          cases r with
          | nil => simp at hr
          | cons => exact t4.elim
        · -- the first leaf is on one of the two sides
          have key : ∀ (A B : Multiset ℕ) (a b : ℕ), (↑((v :: l).map vv) : Multiset ℕ) = A + B →
              B ≠ 0 → RM A a → RM B b → (m = a &&& b ∨ m = a ||| b) → vv v ∈ A → False := by
            intro A B a b hS hB0 hA hB e hvA
            obtain ⟨s, hs, e1, e2, e3, e4, e5⟩ := mem_splits vv l (A.erase (vv v)) B (by
              rw [List.map_cons, ← Multiset.cons_coe] at hS
              have : vv v ::ₘ (↑(l.map vv) : Multiset ℕ) = vv v ::ₘ (A.erase (vv v) + B) := by
                rw [hS, ← Multiset.cons_add, Multiset.cons_erase hvA]
              exact (Multiset.cons_inj_right _).mp this)
            have hperm : (↑l : Multiset ℕ) = ↑s.1 + ↑s.2 := by
              have : ∀ (l : List ℕ), ∀ s ∈ splits l, (↑l : Multiset ℕ) = ↑s.1 + ↑s.2 := by
                intro l
                induction l with
                | nil => intro s hs; simp [splits] at hs; subst hs; rfl
                | cons x l ih =>
                  intro s hs
                  simp only [splits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hs
                  obtain ⟨u, hu, rfl | rfl⟩ := hs
                  · rw [← Multiset.cons_coe, ih u hu, ← Multiset.cons_coe, Multiset.cons_add]
                  · rw [← Multiset.cons_coe, ih u hu, ← Multiset.cons_coe, Multiset.add_cons]
              exact this l s hs
            have ov := hl v (by simp)
            refine go_sound look L n m a b _ hk hm e l r t4 [v] [] ↑s.1 ↑s.2 (ns (vv v)) AL 0 hperm
              (fun z hz => hl z (by simp [hz])) ?_ (by intro z hz; simp at hz) (by simp)
              (by simp only [List.length_cons, List.length_nil]; omega)
              (by simp only [List.length_cons, List.length_nil] at h16 ⊢; omega) (fun i hi => by omega) ?_ ?_ ?_ ?_ ?_ ?_
            · intro z hz
              simp at hz; rw [hz]; exact ov
            · intro _ h0
              apply hB0
              rw [← e2]
              have : s.2 = [] := by simpa using h0
              rw [this]; rfl
            · rw [Multiset.map_coe, e1]
              simp only [List.map_cons, List.map_nil, Multiset.coe_singleton]
              rw [Multiset.singleton_add, Multiset.cons_erase hvA]
              exact hA
            · rw [Multiset.map_coe, e2]
              simpa using hB
            · intro i hi z hz
              simp at hz; rw [hz]; exact hi
            · exact Acc_nil _
            · have e0 : enc [v] = v := by simp [enc]
              have e1 : enc ([] : List ℕ) = 0 := rfl
              rw [e0, e1]; exact h
          have hv : vv v ∈ A + B := by rw [← hS]; simp
          rcases Multiset.mem_add.mp hv with hv | hv
          · exact key A B a b hS hB0 hA hB e hv
          · refine key B A b a (by rw [hS, add_comm]) hA0 hB hA ?_ hv
            rcases e with e | e
            · exact Or.inl (by rw [e, Nat.land_comm])
            · exact Or.inr (by rw [e, Nat.lor_comm])

-- All values of formulas over given leaves that separate a given relation.

theorem sep_mat (L n m : ℕ) (h : Sep L n m) : Nat.beq (Nat.land (mat L n) (ns m)) 0 = true := by
  by_contra hc
  obtain ⟨i, hi⟩ := bit_of_ne _ (Bool.eq_false_iff.mpr hc)
  have hi := land_bit _ _ _ hi
  obtain ⟨h1, h2, h3⟩ := mat_bit _ _ _ hi.1
  exact (ns_bit m i hi.2).2 (h (i / 8) (i % 8) h3.1 h3.2 h1 h2)

def encp : List (ℕ × ℕ) → ℕ
  | [] => 0
  | x :: l => Nat.add (Nat.mul (encp l) 1024) x.1

theorem encp_eq (l : List (ℕ × ℕ)) : encp l = enc (l.map Prod.fst) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [encp, ih]; rfl

def nsp : List (ℕ × ℕ) → ℕ
  | [] => AL
  | x :: l => Nat.land x.2 (nsp l)

def Pr (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, p.2 = ns (vv p.1) ∧ 1 ≤ p.1 ∧ p.1 < 1024

theorem nsp_acc (l : List (ℕ × ℕ)) (h : Pr l) : Acc ↑(l.map fun p => vv p.1) (nsp l) := by
  induction l with
  | nil => intro i _ v hv; simp at hv
  | cons x l ih =>
    intro i hi v hv
    have hi := land_bit _ _ _ hi
    rw [List.map_cons, ← Multiset.cons_coe, Multiset.mem_cons] at hv
    rcases hv with rfl | hv
    · rw [← (h x (by simp)).1]; exact hi.1
    · exact ih (fun p hp => h p (by simp [hp])) i hi.2 v hv

def cmb (op : ℕ → ℕ → ℕ) (P : ℕ) (as bs : List ℕ) : List ℕ :=
  as.flatMap fun a => bs.flatMap fun b => frc (op a b) fun z =>
    bif Nat.beq (Nat.land P (ns z)) 0 then [z] else []

def gqb (rec : List (ℕ × ℕ) → ℕ → ℕ → List ℕ) (x : ℕ × ℕ) (l : List (ℕ × ℕ)) (P L n : ℕ) : List ℕ :=
    (splits l).flatMap fun s => bif s.2.isEmpty then [] else
      frc (Nat.land P (nsp (x :: s.1))) fun pa => frc (Nat.land P (nsp s.2)) fun pb =>
      (frc (rc pa) fun fx => frc (rc pb) fun fb => bif Nat.beq (Nat.land fx fb) 0 then
        cmb Nat.lor P (rec (x :: s.1) fb n) (rec s.2 fx n) else []) ++
      (frc (cc pa) fun cx => frc (cc pb) fun cb => bif Nat.beq (Nat.land cx cb) 0 then
        cmb Nat.land P (rec (x :: s.1) L cb) (rec s.2 L cx) else [])

def gq (look : ℕ → ℕ → ℕ → Bool) : ℕ → List (ℕ × ℕ) → ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | _ + 1, [], _, _ => []
  | f + 1, x :: l, L, n => frc (mat L n) fun P =>
    bif l.isEmpty then (frc (vv x.1) fun v => bif Nat.beq (Nat.land P (ns v)) 0 then [v] else []) else
    bif !(Nat.beq (Nat.land P (nsp (x :: l))) 0) || look (encp (x :: l)) L n then [] else
    gqb (gq look f) x l P L n

theorem mem_cmb (op : ℕ → ℕ → ℕ) (P : ℕ) (as bs : List ℕ) (a b : ℕ) (ha : a ∈ as) (hb : b ∈ bs)
    (h : Nat.beq (Nat.land P (ns (op a b))) 0 = true) : op a b ∈ cmb op P as bs := by
  unfold cmb
  rw [List.mem_flatMap]
  refine ⟨a, ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨b, hb, ?_⟩
  rw [frc_eq, h]
  simp

theorem gqb_mem (rec : List (ℕ × ℕ) → ℕ → ℕ → List ℕ) (x : ℕ × ℕ) (l : List (ℕ × ℕ)) (L n m : ℕ)
    (hl : Pr (x :: l)) (hlen : 1 ≤ l.length) (hR : RM ↑((x :: l).map fun p => vv p.1) m) (hm : Sep L n m)
    (hrec : ∀ (s : List (ℕ × ℕ)) (L n m : ℕ), Pr s → s.length ≤ l.length → RM ↑(s.map fun p => vv p.1) m →
      Sep L n m → m ∈ rec s L n) : m ∈ gqb rec x l (mat L n) L n := by
  have hmat := sep_mat L n m hm
  rcases RM_inv _ _ hR with h | ⟨A, B, a, b, hS, hA0, hB0, hA, hB, e⟩
  · exfalso
    have hc := congrArg Multiset.card h
    have h0 : l = [] := by simpa using hc
    rw [h0] at hlen
    simp at hlen
  · have key : ∀ (A B : Multiset ℕ) (a b : ℕ),
        (↑((x :: l).map fun p => vv p.1) : Multiset ℕ) = A + B → B ≠ 0 → RM A a → RM B b →
        (m = a &&& b ∨ m = a ||| b) → vv x.1 ∈ A → m ∈ gqb rec x l (mat L n) L n := by
      intro A B a b hS hB0 hA hB e hxA
      obtain ⟨s, hs, e1, e2, e3, e4, e5⟩ := mem_splits (fun p : ℕ × ℕ => vv p.1) l (A.erase (vv x.1)) B (by
        rw [List.map_cons, ← Multiset.cons_coe] at hS
        have : vv x.1 ::ₘ (↑(l.map fun p => vv p.1) : Multiset ℕ) = vv x.1 ::ₘ (A.erase (vv x.1) + B) := by
          rw [hS, ← Multiset.cons_add, Multiset.cons_erase hxA]
        exact (Multiset.cons_inj_right _).mp this)
      have p1 : Pr (x :: s.1) := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hl p (by simp)
        · exact hl p (by simp [e3 p hp])
      have p2 : Pr s.2 := fun p hp => hl p (by simp [e4 p hp])
      have hA' : RM ↑((x :: s.1).map fun p => vv p.1) a := by
        rw [List.map_cons, ← Multiset.cons_coe, e1, Multiset.cons_erase hxA]; exact hA
      have hB' : RM ↑(s.2.map fun p => vv p.1) b := by rw [e2]; exact hB
      have hs2 : s.2.isEmpty = false := by
        cases hc : s.2 with
        | nil => rw [hc] at e2; exact absurd e2.symm hB0
        | cons => rfl
      have hs1 : 1 ≤ s.2.length := by
        cases hc : s.2 with
        | nil => rw [hc] at hs2; simp at hs2
        | cons => simp
      have hx' : ∀ i, (Nat.land (mat L n) (nsp (x :: s.1))).testBit i = true → (mat L n).testBit i = true ∧
          ∀ v ∈ (↑((x :: s.1).map fun p => vv p.1) : Multiset ℕ), (ns v).testBit i = true := fun i hi =>
        ⟨(land_bit _ _ _ hi).1, nsp_acc _ p1 i (land_bit _ _ _ hi).2⟩
      have hy' : ∀ i, (Nat.land (mat L n) (nsp s.2)).testBit i = true → (mat L n).testBit i = true ∧
          ∀ v ∈ (↑(s.2.map fun p => vv p.1) : Multiset ℕ), (ns v).testBit i = true := fun i hi =>
        ⟨(land_bit _ _ _ hi).1, nsp_acc _ p2 i (land_bit _ _ _ hi).2⟩
      unfold gqb
      rw [List.mem_flatMap]
      refine ⟨s, hs, ?_⟩
      rw [hs2, cond_false]
      simp only [frc_eq]
      rw [List.mem_append]
      rcases e with e | e
      · right
        obtain ⟨h1, h2, h3⟩ := and_cond L n m a b _ _ _ _ hm e hA' hB' hx' hy'
        rw [h1, cond_true, e]
        refine mem_cmb Nat.land _ _ _ a b
          (hrec _ _ _ a p1 (by simp only [List.length_cons]; omega) hA' h2)
          (hrec _ _ _ b p2 (by omega) hB' h3) ?_
        change Nat.beq (Nat.land (mat L n) (ns (a &&& b))) 0 = true
        rw [← e]; exact hmat
      · left
        obtain ⟨h1, h2, h3⟩ := or_cond L n m a b _ _ _ _ hm e hA' hB' hx' hy'
        rw [h1, cond_true, e]
        refine mem_cmb Nat.lor _ _ _ a b
          (hrec _ _ _ a p1 (by simp only [List.length_cons]; omega) hA' h2)
          (hrec _ _ _ b p2 (by omega) hB' h3) ?_
        change Nat.beq (Nat.land (mat L n) (ns (a ||| b))) 0 = true
        rw [← e]; exact hmat
    have hv : vv x.1 ∈ A + B := by rw [← hS]; simp
    rcases Multiset.mem_add.mp hv with hv | hv
    · exact key A B a b hS hB0 hA hB e hv
    · refine key B A b a (by rw [hS, add_comm]) hA0 hB hA ?_ hv
      rcases e with e | e
      · exact Or.inl (by rw [e, Nat.land_comm])
      · exact Or.inr (by rw [e, Nat.lor_comm])

theorem gq_memN (look : ℕ → ℕ → ℕ → Bool) (N : ℕ) (hk : LookOK N look) : ∀ (f : ℕ) (l : List (ℕ × ℕ))
    (L n m : ℕ), Pr l → l.length ≤ f → l.length ≤ 16 → l.length < N → RM ↑(l.map fun p => vv p.1) m →
    Sep L n m → m ∈ gq look f l L n := by
  intro f
  induction f with
  | zero =>
    intro l L n m _ hf _ _ hR _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rcases RM_inv _ _ hR with h | ⟨A, B, a, b, h, hA, _⟩
    · have := congrArg Multiset.card h; simp at this
    · exact absurd (add_eq_zero.mp h.symm).1 hA
  | succ f ih =>
    intro l L n m hl hf h16 hN hR hm
    cases l with
    | nil =>
      rcases RM_inv _ _ hR with h | ⟨A, B, a, b, h, hA, _⟩
      · have := congrArg Multiset.card h; simp at this
      · exact absurd (add_eq_zero.mp h.symm).1 hA
    | cons x l =>
      have hmat := sep_mat L n m hm
      rw [gq, frc_eq]
      cases hne : l.isEmpty
      swap
      · rw [cond_true, frc_eq]
        have hl0 : l = [] := by simpa using hne
        subst hl0
        rcases RM_inv _ _ hR with h | ⟨A, B, a, b, h, hA, hB, _⟩
        · have e : vv x.1 = m := by simpa using h
          rw [e, hmat]; simp
        · exfalso
          have hc := congrArg Multiset.card h
          have h1 := Multiset.card_pos.mpr hA
          have h2 := Multiset.card_pos.mpr hB
          simp at hc; omega
      · rw [cond_false]
        have hlen : 1 ≤ l.length := by
          cases l with
          | nil => simp at hne
          | cons => simp
        have hcond : (!(Nat.beq (Nat.land (mat L n) (nsp (x :: l))) 0) || look (encp (x :: l)) L n) = false := by
          rw [Bool.or_eq_false_iff]
          constructor
          · cases hb : Nat.beq (Nat.land (mat L n) (nsp (x :: l))) 0
            · exact (all_un _ L n m _ hm hR (nsp_acc _ hl) hb).elim
            · rfl
          · cases hb : look (encp (x :: l)) L n
            · rfl
            · exfalso
              rw [encp_eq] at hb
              refine hk ((x :: l).map Prod.fst) L n ?_ (by simpa using hN) (by simpa using h16) hb m ?_ hm
              · intro y hy
                obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
                exact (hl p hp).2
              · rw [List.map_map]; exact hR
        rw [hcond, cond_false]
        simp only [List.length_cons] at hf h16 hN
        exact gqb_mem _ x l L n m hl hlen hR hm (fun s L n m h1 h2 h3 h4 =>
          ih s L n m h1 (by omega) (by omega) (by omega) h3 h4)

theorem gq_mem (look : ℕ → ℕ → ℕ → Bool) (hk : ∀ N, LookOK N look) (f : ℕ) (l : List (ℕ × ℕ))
    (L n m : ℕ) (hl : Pr l) (hf : l.length ≤ f) (h16 : l.length ≤ 16) (hR : RM ↑(l.map fun p => vv p.1) m)
    (hm : Sep L n m) : m ∈ gq look f l L n :=
  gq_memN look (l.length + 1) (hk _) f l L n m hl hf h16 (by omega) hR hm

-- nothing over l separates: one step, the parts being looked up
def ex (look : ℕ → ℕ → ℕ → Bool) : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, L, n => bif l.isEmpty then false else
      frc (mat L n) fun P => (gqb (gq look 16) x l P L n).isEmpty

theorem ex_sound (look : ℕ → ℕ → ℕ → Bool) (l : List (ℕ × ℕ)) (L n : ℕ) (hk : LookOK l.length look)
    (hl : Pr l) (h16 : l.length ≤ 16) (h : ex look l L n = true) :
    ∀ m, RM ↑(l.map fun p => vv p.1) m → ¬ Sep L n m := by
  intro m hR hm
  cases l with
  | nil =>
    rcases RM_inv _ _ hR with h | ⟨A, B, a, b, h, hA, _⟩
    · have := congrArg Multiset.card h; simp at this
    · exact absurd (add_eq_zero.mp h.symm).1 hA
  | cons x l =>
    rw [ex] at h
    cases hne : l.isEmpty
    · rw [hne, cond_false, frc_eq] at h
      have hlen : 1 ≤ l.length := by
        cases l with
        | nil => simp at hne
        | cons => simp
      simp only [List.length_cons] at h16 hk
      have := gqb_mem (gq look 16) x l L n m hl hlen hR hm (fun s L n m h1 h2 h3 h4 =>
        gq_memN look _ hk 16 s L n m h1 (by omega) (by omega) (by omega) h3 h4)
      rw [List.isEmpty_iff.mp h] at this
      simp at this
    · rw [hne, cond_true] at h; exact absurd h (by simp)

def Dp : List ℕ → List (ℕ × ℕ)
  | [] => []
  | i :: l => frc (ns (vv i)) fun n => (i, n) :: Dp l

theorem Dp_eq (l : List ℕ) : Dp l = l.map fun i => (i, ns (vv i)) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [Dp, frc_eq, ih]; rfl

theorem ex_Nof (look : ℕ → ℕ → ℕ → Bool) (l : List ℕ) (L n : ℕ) (hk : LookOK l.length look)
    (hl : Ok l) (h16 : l.length ≤ 16) (h : ex look (Dp l) L n = true) : Nof l L n := by
  have e : (Dp l).map (fun p => vv p.1) = l.map vv := by rw [Dp_eq, List.map_map]; rfl
  have hlen : (Dp l).length = l.length := by rw [Dp_eq, List.length_map]
  intro m hR
  refine ex_sound look (Dp l) L n (by rw [hlen]; exact hk) ?_ (by omega) h m (by rw [e]; exact hR)
  intro p hp
  rw [Dp_eq] at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨rfl, hl i hi⟩

-- the table: a search tree on the codes, with the refuted relations of each
def lk : BinaryTree (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) → ℕ → ℕ → ℕ → Bool
  | BinaryTree.nil, _, _, _ => false
  | BinaryTree.node v l r, k, L, n =>
    bif Nat.beq k v.1 then (v.2.1 ++ v.2.2).any (fun e => Nat.beq (Nat.land e.1 L) e.1 && Nat.beq (Nat.land e.2 n) e.2)
    else bif Nat.blt k v.1 then lk l k L n else lk r k L n

def ckv (look : ℕ → ℕ → ℕ → Bool) (v : ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) : Bool :=
  (fun l : List ℕ => l.all (fun x => Nat.ble 1 x) && (v.2.1.all (fun e => rf look l.reverse e.1 e.2) &&
    v.2.2.all (fun e => ex look (Dp l) e.1 e.2))) (dc 16 v.1)

def ckt (look : ℕ → ℕ → ℕ → Bool) : BinaryTree (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) → Bool
  | BinaryTree.nil => true
  | BinaryTree.node v l r => ckv look v && (ckt look l && ckt look r)

theorem Nof_perm (l l' : List ℕ) (L n : ℕ) (h : (↑l : Multiset ℕ) = ↑l') (hN : Nof l L n) : Nof l' L n := by
  intro m hR
  refine hN m ?_
  have e : (↑(l.map vv) : Multiset ℕ) = ↑(l'.map vv) := by
    rw [← Multiset.map_coe, ← Multiset.map_coe, h]
  rw [e]; exact hR

theorem lk_sound (look : ℕ → ℕ → ℕ → Bool) (N : ℕ) (hk : LookOK N look) :
    ∀ t : BinaryTree (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)), ckt look t = true → LookOK (N + 1) (lk t) := by
  intro t
  induction t with
  | nil => intro _ l L n _ _ _ h; simp [lk] at h
  | node v t1 t2 ih1 ih2 =>
    intro hc l L n hl hN h16 h
    rw [ckt, Bool.and_eq_true, Bool.and_eq_true] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    rw [lk] at h
    cases hb : Nat.beq (enc l) v.1
    · rw [hb, cond_false] at h
      cases hb2 : Nat.blt (enc l) v.1
      · rw [hb2, cond_false] at h; exact ih2 h3 l L n hl hN h16 h
      · rw [hb2, cond_true] at h; exact ih1 h2 l L n hl hN h16 h
    · rw [hb, cond_true, List.any_eq_true] at h
      obtain ⟨e, he, h⟩ := h
      rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
      rw [Nat.beq_eq] at hb
      unfold ckv at h1
      rw [← hb, dc_enc l hl 16 h16, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true,
        List.all_eq_true] at h1
      have h6 : Nof l e.1 e.2 := by
        rcases List.mem_append.mp he with he | he
        · have h5 := rf_sound look l.reverse e.1 e.2 (fun l' L' n' ho hlen h16' hh =>
            hk l' L' n' ho (by simp at hlen; omega) h16' hh) (fun x hx => hl x (by simpa using hx))
            (by simpa using h16) (h1.2.1 e he)
          exact Nof_perm l.reverse l e.1 e.2 (Multiset.coe_eq_coe.mpr (List.reverse_perm l)) h5
        · exact ex_Nof look l e.1 e.2 (fun l' L' n' ho hlen h16' hh => hk l' L' n' ho (by omega) h16' hh) hl h16
            (h1.2.2 e he)
      intro m hR hm
      exact h6 m hR (Sep_sub _ _ _ _ _ h.1 h.2 hm)

theorem LookOK_all (t : BinaryTree (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))) (h : ckt (lk t) t = true) : ∀ N, LookOK N (lk t) := by
  intro N
  induction N with
  | zero => intro l L n _ hN; exact absurd hN (by omega)
  | succ N ih => exact lk_sound (lk t) N ih t h

-- Complements.

theorem FULL_hi (p : ℕ) (hp : 7 ≤ p) : FULL.testBit p = false := by
  unfold FULL; rw [Nat.testBit_two_pow_sub_one]; simpa using hp

theorem lt_hi (m p : ℕ) (hm : m < 2 ^ 7) (hp : 7 ≤ p) : m.testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hp))

theorem RM_lt (S : Multiset ℕ) (m : ℕ) (h : RM S m) : (∀ v ∈ S, v < 2 ^ 7) → m < 2 ^ 7 := by
  refine h (fun S m => (∀ v ∈ S, v < 2 ^ 7) → m < 2 ^ 7) (fun x hx => hx x (by simp)) ?_
  intro S T a b hS hT
  constructor
  · intro hv
    exact lt_of_le_of_lt Nat.and_le_left (hS (fun v h => hv v (Multiset.mem_add.mpr (Or.inl h))))
  · intro hv
    exact Nat.or_lt_two_pow (hS (fun v h => hv v (Multiset.mem_add.mpr (Or.inl h))))
      (hT (fun v h => hv v (Multiset.mem_add.mpr (Or.inr h))))

theorem cpl_lt (m : ℕ) (h : m < 2 ^ 7) : FULL ^^^ m < 2 ^ 7 :=
  Nat.xor_lt_two_pow (by unfold FULL; norm_num) h

theorem cpl_cpl (m : ℕ) : FULL ^^^ (FULL ^^^ m) = m := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem RM_neg (S : Multiset ℕ) (m : ℕ) (h : RM S m) : (∀ v ∈ S, v < 2 ^ 7) →
    RM (S.map fun v => FULL ^^^ v) (FULL ^^^ m) := by
  have key := h (fun S m => RM S m ∧ ((∀ v ∈ S, v < 2 ^ 7) → RM (S.map fun v => FULL ^^^ v) (FULL ^^^ m)))
    (fun x => ⟨RM_leaf x, fun _ => by rw [Multiset.map_singleton]; exact RM_leaf _⟩) ?_
  · exact key.2
  · intro S T a b hS hT
    have bit : ∀ p, (FULL ^^^ (a &&& b)).testBit p = !((a &&& b).testBit p) ∨ 7 ≤ p := by
      intro p
      by_cases hp : p < 7
      · exact Or.inl (FULL_bit p hp _)
      · exact Or.inr (by omega)
    constructor
    · refine ⟨RM_and hS.1 hT.1, fun hv => ?_⟩
      have v1 : ∀ v ∈ S, v < 2 ^ 7 := fun v h => hv v (Multiset.mem_add.mpr (Or.inl h))
      have v2 : ∀ v ∈ T, v < 2 ^ 7 := fun v h => hv v (Multiset.mem_add.mpr (Or.inr h))
      have l1 := RM_lt _ _ hS.1 v1
      have l2 := RM_lt _ _ hT.1 v2
      have e : FULL ^^^ (a &&& b) = (FULL ^^^ a) ||| (FULL ^^^ b) := by
        apply Nat.eq_of_testBit_eq; intro p
        by_cases hp : p < 7
        · rw [FULL_bit p hp, Nat.testBit_or, FULL_bit p hp, FULL_bit p hp, Nat.testBit_and]
          cases a.testBit p <;> cases b.testBit p <;> rfl
        · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and, FULL_hi p (by omega),
            lt_hi a p l1 (by omega), lt_hi b p l2 (by omega)]
          rfl
      rw [Multiset.map_add, e]
      exact RM_or (hS.2 v1) (hT.2 v2)
    · refine ⟨RM_or hS.1 hT.1, fun hv => ?_⟩
      have v1 : ∀ v ∈ S, v < 2 ^ 7 := fun v h => hv v (Multiset.mem_add.mpr (Or.inl h))
      have v2 : ∀ v ∈ T, v < 2 ^ 7 := fun v h => hv v (Multiset.mem_add.mpr (Or.inr h))
      have l1 := RM_lt _ _ hS.1 v1
      have l2 := RM_lt _ _ hT.1 v2
      have e : FULL ^^^ (a ||| b) = (FULL ^^^ a) &&& (FULL ^^^ b) := by
        apply Nat.eq_of_testBit_eq; intro p
        by_cases hp : p < 7
        · rw [FULL_bit p hp, Nat.testBit_and, FULL_bit p hp, FULL_bit p hp, Nat.testBit_or]
          cases a.testBit p <;> cases b.testBit p <;> rfl
        · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and, FULL_hi p (by omega),
            lt_hi a p l1 (by omega), lt_hi b p l2 (by omega)]
          rfl
      rw [Multiset.map_add, e]
      exact RM_and (hS.2 v1) (hT.2 v2)

-- The check of one state.

def Cv : List Bool → Multiset ℕ → Prop
  | [], S => ∃ m, RM S m ∧ ∀ p < 7, m.testBit p = MM.testBit p
  | true :: ks, S => ∃ Sc rest mc, S = Sc + rest ∧ RM Sc mc ∧ Cv ks (mc ::ₘ mc ::ₘ rest)
  | false :: ks, S => ∃ Sc rest mc, S = Sc + rest ∧ RM Sc mc ∧ Cv ks ((FULL ^^^ mc) ::ₘ rest)

theorem Ch_Cv (o : ℕ) (val : ℕ → ℕ → Bool) (hv : ∀ p < 7, val o p = MM.testBit p) :
    ∀ j S, Ch j S {o} val → ∃ ks, ks.length = j ∧ Cv ks S := by
  intro j
  induction j with
  | zero =>
    rintro S ⟨F, m, h1, h2, h3⟩
    rw [Finset.sum_singleton] at h3
    refine ⟨[], rfl, m o, h3 ▸ h1 o (by simp), fun p hp => ?_⟩
    rw [h2 o (by simp) p hp, hv p hp]
  | succ j ih =>
    rintro S ⟨Sc, rest, mc, h1, h2, h3 | h3⟩
    · obtain ⟨ks, hk, hc⟩ := ih _ h3
      exact ⟨true :: ks, by simp [hk], Sc, rest, mc, h1, h2, hc⟩
    · obtain ⟨ks, hk, hc⟩ := ih _ h3
      exact ⟨false :: ks, by simp [hk], Sc, rest, mc, h1, h2, hc⟩

def Rf (b c : ℕ) (S : Multiset ℕ) : Prop := ∀ ks, ks.count true ≤ b → ks.count false ≤ c → ¬ Cv ks S

-- without complements, some leaf separates every pair
theorem Cv_dir (i : ℕ) (hi : V i) : ∀ ks, ks.count false = 0 → ∀ S, Cv ks S →
    ∃ v ∈ S, v.testBit (po i) = true ∧ v.testBit (zo i) = false := by
  intro ks
  induction ks with
  | nil =>
    rintro _ S ⟨m, h1, h2⟩
    by_contra hno
    push Not at hno
    refine RM_un (po i) (zo i) S m h1 (fun v hv h => ?_) ?_
    · exact absurd h.2 (by simpa using hno v hv h.1)
    · rw [h2 _ (po_ok i hi).1, h2 _ (zo_ok i hi).1]
      exact ⟨(po_ok i hi).2, (zo_ok i hi).2⟩
  | cons k ks ih =>
    intro hk S h
    cases k with
    | false => simp at hk
    | true =>
      obtain ⟨Sc, rest, mc, h1, h2, h3⟩ := h
      obtain ⟨v, hv, hs⟩ := ih (by simpa using hk) _ h3
      have hcase : v = mc ∨ v ∈ rest := by
        simp only [Multiset.mem_cons] at hv
        rcases hv with h | h | h
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inr h
      rcases hcase with rfl | hv
      · by_contra hno
        push Not at hno
        refine RM_un (po i) (zo i) Sc v h2 (fun u hu h => ?_) hs
        exact absurd h.2 (by simpa using hno u (by rw [h1]; exact Multiset.mem_add.mpr (Or.inl hu)) h.1)
      · exact ⟨v, by rw [h1]; exact Multiset.mem_add.mpr (Or.inr hv), hs⟩

-- in any case, some leaf takes two values on every pair
theorem Cv_und (i : ℕ) (hi : V i) : ∀ ks S, Cv ks S → ∃ v ∈ S, v.testBit (po i) ≠ v.testBit (zo i) := by
  have hT := (po_ok i hi).1
  have hT' := (zo_ok i hi).1
  intro ks
  induction ks with
  | nil =>
    rintro S ⟨m, h1, h2⟩
    by_contra hno
    push Not at hno
    have := RM_eq (po i) (zo i) S m h1 hno
    rw [h2 _ hT, h2 _ hT', (po_ok i hi).2, (zo_ok i hi).2] at this
    exact absurd this (by simp)
  | cons k ks ih =>
    intro S h
    obtain ⟨Sc, rest, mc, h1, h2, v, hv, hs⟩ : ∃ Sc rest mc, S = Sc + rest ∧ RM Sc mc ∧
        ∃ v, (v = mc ∨ v = FULL ^^^ mc ∨ v ∈ rest) ∧ v.testBit (po i) ≠ v.testBit (zo i) := by
      cases k with
      | false =>
        obtain ⟨Sc, rest, mc, h1, h2, h3⟩ := h
        obtain ⟨v, hv, hs⟩ := ih _ h3
        refine ⟨Sc, rest, mc, h1, h2, v, ?_, hs⟩
        rcases Multiset.mem_cons.mp hv with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      | true =>
        obtain ⟨Sc, rest, mc, h1, h2, h3⟩ := h
        obtain ⟨v, hv, hs⟩ := ih _ h3
        refine ⟨Sc, rest, mc, h1, h2, v, ?_, hs⟩
        simp only [Multiset.mem_cons] at hv
        rcases hv with h | h | h
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    have hmc : mc.testBit (po i) ≠ mc.testBit (zo i) → ∃ v ∈ S, v.testBit (po i) ≠ v.testBit (zo i) := by
      intro hne
      by_contra hno
      push Not at hno
      exact hne (RM_eq (po i) (zo i) Sc mc h2 (fun u hu => hno u (by rw [h1]; exact Multiset.mem_add.mpr (Or.inl hu))))
    rcases hv with rfl | rfl | hv
    · exact hmc hs
    · apply hmc
      intro e
      apply hs
      rw [FULL_bit _ hT, FULL_bit _ hT', e]
    · exact ⟨v, by rw [h1]; exact Multiset.mem_add.mpr (Or.inr hv), hs⟩

-- complements of leaves: the codes come in pairs
def cm : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | p :: l => frc (Nat.xor p.1 1) fun i => frc (ns (vv i)) fun n => (i, n) :: cm l

theorem cm_eq (l : List (ℕ × ℕ)) : cm l = l.map fun p => (p.1 ^^^ 1, ns (vv (p.1 ^^^ 1))) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [cm, frc_eq]; beta_reduce; rw [frc_eq, ih]; rfl

def M0 : ℕ := mat ONE FZ

theorem M0_V (i : ℕ) (h : M0.testBit i = true) : V i := (mat_bit _ _ _ h).2.2

def gz (look : ℕ → ℕ → ℕ → Bool) (A : List (ℕ × ℕ)) (M : ℕ) : List ℕ :=
  frc (rc M) fun L => frc (cc M) fun n => gq look 16 A L n

theorem gz_mem (look : ℕ → ℕ → ℕ → Bool) (hk : ∀ N, LookOK N look) (A : List (ℕ × ℕ)) (M m : ℕ) (hA : Pr A)
    (h16 : A.length ≤ 16) (hR : RM ↑(A.map fun p => vv p.1) m)
    (hM : ∀ i, M.testBit i = true → V i ∧ m.testBit (po i) = true ∧ m.testBit (zo i) = false) :
    m ∈ gz look A M := by
  unfold gz
  rw [frc_eq, frc_eq]
  refine gq_mem look hk 16 A _ _ m hA h16 h16 hR ?_
  intro p t hp ht h1 h2
  obtain ⟨_, _, i, h3, h4⟩ := rc_bit _ _ h1
  obtain ⟨_, j, h5, h6⟩ := cc_bit _ _ h2
  rw [Nat.mul_div_cancel_left p (by norm_num)] at h4
  have a1 := (hM i h3).2.1
  have a2 := (hM j h5).2.2
  unfold po at a1
  unfold zo at a2
  rw [h4] at a1
  rw [h6] at a2
  exact ⟨a1, a2⟩

-- the closure of one row
def st0 (M : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: l => frc (Nat.shiftLeft 1 (8 * r)) fun L =>
      bif Nat.beq (Nat.land M (mat L FZ)) 0 then st0 M l else L

def nst (M L : ℕ) : ℕ := cc (Nat.land M (mat L FZ))
def lst (M n : ℕ) : ℕ := rc (Nat.land M (mat ONE n))

def Cl (be : Bool) (m L n : ℕ) : Prop := (∀ p, p < 3 → L.testBit (8 * p) = true → m.testBit p = be) ∧
  ∀ t, t < 4 → n.testBit t = true → m.testBit (3 + t) = !be

def Dif (M m : ℕ) : Prop := ∀ i, M.testBit i = true → V i ∧ m.testBit (po i) ≠ m.testBit (zo i)

theorem nst_ok (be : Bool) (M m L : ℕ) (hM : Dif M m)
    (hL : ∀ p, p < 3 → L.testBit (8 * p) = true → m.testBit p = be) :
    ∀ t, t < 4 → (nst M L).testBit t = true → m.testBit (3 + t) = !be := by
  intro t _ h
  obtain ⟨_, i, h1, h2⟩ := cc_bit _ _ h
  have h1 := land_bit _ _ _ h1
  obtain ⟨h3, _, h4⟩ := mat_bit _ _ _ h1.2
  have h5 := hL _ h4.1 h3
  have h6 := (hM i h1.1).2
  unfold po zo at h6
  rw [h5, h2] at h6
  cases be <;> cases hb : m.testBit (3 + t) <;> simp_all

theorem lst_ok (be : Bool) (M m n : ℕ) (hM : Dif M m)
    (hn : ∀ t, t < 4 → n.testBit t = true → m.testBit (3 + t) = !be) :
    ∀ p, p < 3 → (lst M n).testBit (8 * p) = true → m.testBit p = be := by
  intro p _ h
  obtain ⟨_, _, i, h1, h2⟩ := rc_bit _ _ h
  rw [Nat.mul_div_cancel_left p (by norm_num)] at h2
  have h1 := land_bit _ _ _ h1
  obtain ⟨_, h3, h4⟩ := mat_bit _ _ _ h1.2
  have h5 := hn _ h4.2 h3
  have h6 := (hM i h1.1).2
  unfold po zo at h6
  rw [h2, h5] at h6
  cases be <;> cases hb : m.testBit p <;> simp_all

theorem st0_ok (M m : ℕ) : ∀ l : List ℕ, ∃ be, ∀ p, p < 3 → (st0 M l).testBit (8 * p) = true →
    m.testBit p = be := by
  intro l
  induction l with
  | nil => exact ⟨false, fun p _ h => by simp [st0] at h⟩
  | cons r l ih =>
    rw [st0, frc_eq]
    cases Nat.beq (Nat.land M (mat (Nat.shiftLeft 1 (8 * r)) FZ)) 0
    · rw [cond_false]
      refine ⟨m.testBit r, fun p _ h => ?_⟩
      have h : (1 <<< (8 * r)).testBit (8 * p) = true := h
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h
      rw [show p = r by omega]
    · rw [cond_true]; exact ih

def flt (M : ℕ) (l : List ℕ) : List ℕ := l.flatMap fun z =>
  bif Nat.beq (Nat.land M (Nat.land (ns z) (ns (Nat.xor FULL z)))) 0 then [z] else []

def uz (look : ℕ → ℕ → ℕ → Bool) (A A' : List (ℕ × ℕ)) (M : ℕ) : List ℕ :=
  frc (st0 M RW) fun L0 => frc (nst M L0) fun n0 => frc (lst M n0) fun L1 => frc (nst M L1) fun n1 =>
  frc (lst M n1) fun L2 => frc (nst M L2) fun n2 =>
  flt M (gq look 16 A L2 n2 ++ bif Nat.beq L2 0 then [] else
    (gq look 16 A' L2 n2).map fun z => Nat.xor FULL z)

theorem vv_lt (i : ℕ) : vv i < 2 ^ 7 := by
  unfold vv
  have : Nat.land (Nat.shiftRight VALS (7 * i)) 127 ≤ 127 := Nat.and_le_right
  exact lt_of_le_of_lt this (by norm_num)

def cpc : Bool := (List.range NV).all fun i => Nat.blt i 2 ||
  (Nat.beq (vv (Nat.xor i 1)) (Nat.xor FULL (vv i)) && Nat.ble 2 (Nat.xor i 1) && Nat.blt (Nat.xor i 1) NV)

theorem cpc_ok (h : cpc = true) (i : ℕ) (h1 : 2 ≤ i) (h2 : i < NV) :
    vv (i ^^^ 1) = FULL ^^^ vv i ∧ 2 ≤ i ^^^ 1 ∧ i ^^^ 1 < NV := by
  unfold cpc at h
  rw [List.all_eq_true] at h
  have h := h i (List.mem_range.mpr h2)
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with h | h
  · rw [Nat.blt_eq] at h; omega
  · obtain ⟨⟨h3, h4⟩, h5⟩ := h
    rw [Nat.beq_eq] at h3
    rw [Nat.blt_eq] at h5
    exact ⟨h3, Nat.le_of_ble_eq_true h4, h5⟩

def Vd (A : List (ℕ × ℕ)) : Prop := ∀ p ∈ A, 2 ≤ p.1 ∧ p.1 < NV ∧ p.2 = ns (vv p.1)

theorem Vd_Pr (hN : NV ≤ 1024) (A : List (ℕ × ℕ)) (h : Vd A) : Pr A := fun p hp =>
  ⟨(h p hp).2.2, by have := (h p hp).1; omega, lt_of_lt_of_le (h p hp).2.1 hN⟩

theorem cm_Vd (hC : cpc = true) (A : List (ℕ × ℕ)) (h : Vd A) : Vd (cm A) := by
  intro p hp
  rw [cm_eq] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have := cpc_ok hC q.1 (h q hq).1 (h q hq).2.1
  exact ⟨this.2.1, this.2.2, rfl⟩

theorem cm_map (hC : cpc = true) (A : List (ℕ × ℕ)) (h : Vd A) :
    ((cm A).map fun p => vv p.1) = (A.map fun p => vv p.1).map fun v => FULL ^^^ v := by
  rw [cm_eq]
  induction A with
  | nil => rfl
  | cons p A ih =>
    have e := (cpc_ok hC p.1 (h p (by simp)).1 (h p (by simp)).2.1).1
    have ih := ih (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons]
    rw [ih, e]

theorem cm_RM (hC : cpc = true) (A : List (ℕ × ℕ)) (h : Vd A) (m : ℕ)
    (hR : RM ↑(A.map fun p => vv p.1) m) : RM ↑((cm A).map fun p => vv p.1) (FULL ^^^ m) := by
  rw [cm_map hC A h, ← Multiset.map_coe]
  apply RM_neg _ _ hR
  intro v hv
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hv)
  exact vv_lt _

theorem cm_len (A : List (ℕ × ℕ)) : (cm A).length = A.length := by rw [cm_eq, List.length_map]

-- a pair on which neither the leaves nor their complements are separating: the leaves are equal there
theorem eq_of (hC : cpc = true) (hN : NV ≤ 1024) (A : List (ℕ × ℕ)) (h : Vd A) (i : ℕ)
    (h1 : (nsp A).testBit i = true) (h2 : (nsp (cm A)).testBit i = true) :
    ∀ v ∈ (↑(A.map fun p => vv p.1) : Multiset ℕ), v.testBit (po i) = v.testBit (zo i) := by
  intro v hv
  have a1 := ns_bit v i (nsp_acc A (Vd_Pr hN A h) i h1 v hv)
  have a2 := ns_bit (FULL ^^^ v) i (nsp_acc (cm A) (Vd_Pr hN _ (cm_Vd hC A h)) i h2 _ (by
    rw [cm_map hC A h, ← Multiset.map_coe]
    exact Multiset.mem_map_of_mem (fun v => FULL ^^^ v) hv))
  have b1 := a1.2
  have b2 := a2.2
  rw [FULL_bit _ (po_ok i a1.1).1, FULL_bit _ (zo_ok i a1.1).1] at b2
  cases hp : v.testBit (po i) <;> cases hz : v.testBit (zo i) <;> simp_all

theorem uz_mem (hC : cpc = true) (hN : NV ≤ 1024) (look : ℕ → ℕ → ℕ → Bool) (hk : ∀ N, LookOK N look)
    (A : List (ℕ × ℕ)) (M m : ℕ) (hA : Vd A) (h16 : A.length ≤ 16)
    (hR : RM ↑(A.map fun p => vv p.1) m) (hM : Dif M m) : m ∈ uz look A (cm A) M := by
  have hlt : m < 2 ^ 7 := RM_lt _ _ hR (fun v hv => by
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hv)
    exact vv_lt _)
  obtain ⟨be, b0⟩ := st0_ok M m RW
  have b1 := nst_ok be M m _ hM b0
  have b2 := lst_ok be M m _ hM b1
  have b3 := nst_ok be M m _ hM b2
  have b4 := lst_ok be M m _ hM b3
  have b5 := nst_ok be M m _ hM b4
  unfold uz
  simp only [frc_eq]
  set L2 := lst M (nst M (lst M (nst M (st0 M RW)))) with hL2
  set n2 := nst M L2 with hn2
  unfold flt
  rw [List.mem_flatMap]
  refine ⟨m, ?_, ?_⟩
  · rw [List.mem_append]
    by_cases h0 : L2 = 0
    · left
      refine gq_mem look hk 16 A _ _ m (Vd_Pr hN A hA) h16 h16 hR ?_
      intro p t _ _ h1 _
      rw [h0] at h1; simp at h1
    · cases be with
      | true =>
        left
        refine gq_mem look hk 16 A _ _ m (Vd_Pr hN A hA) h16 h16 hR ?_
        intro p t hp ht h1 h2
        exact ⟨b4 p hp h1, by simpa using b5 t ht h2⟩
      | false =>
        right
        have hb : Nat.beq L2 0 = false := Bool.eq_false_iff.mpr (by rw [Ne, Nat.beq_eq]; exact h0)
        rw [hb, cond_false, List.mem_map]
        refine ⟨FULL ^^^ m, gq_mem look hk 16 (cm A) _ _ _ (Vd_Pr hN _ (cm_Vd hC A hA))
          (by rw [cm_len]; exact h16) (by rw [cm_len]; exact h16) (cm_RM hC A hA m hR) ?_, cpl_cpl m⟩
        intro p t hp ht h1 h2
        rw [FULL_bit p (by omega), FULL_bit (3 + t) (by omega), b4 p hp h1, b5 t ht h2]
        exact ⟨rfl, rfl⟩
  · have : Nat.beq (Nat.land M (Nat.land (ns m) (ns (Nat.xor FULL m)))) 0 = true := by
      by_contra hc
      obtain ⟨i, hi⟩ := bit_of_ne _ (Bool.eq_false_iff.mpr hc)
      have hi := land_bit _ _ _ hi
      have hj := land_bit _ _ _ hi.2
      have hd := hM i hi.1
      have a1 := (ns_bit _ _ hj.1).2
      have a2 := (ns_bit (FULL ^^^ m) _ hj.2).2
      rw [FULL_bit _ (po_ok i hd.1).1, FULL_bit _ (zo_ok i hd.1).1] at a2
      have hd2 := hd.2
      cases hp : m.testBit (po i) <;> cases hz : m.testBit (zo i) <;> simp_all
    rw [this]; simp

-- Permutations of the points that keep the function.

def ofb : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (ofb l)

theorem ofb_bit : ∀ (l : List Bool) (p : ℕ), (ofb l).testBit p = l.getD p false := by
  intro l
  induction l with
  | nil => intro p; simp [ofb]
  | cons b l ih =>
    intro p
    cases p with
    | zero => simp [ofb, Nat.testBit_bit_zero]
    | succ p => rw [ofb, Nat.testBit_bit_succ, ih]; simp

def act (g : List ℕ) (v : ℕ) : ℕ := ofb (g.map (Nat.testBit v))

def Gok (g : List ℕ) : Prop := g.length = 7 ∧ ∀ p < 7, g.getD p 0 < 7 ∧
  MM.testBit (g.getD p 0) = MM.testBit p

theorem act_bit (g : List ℕ) (hg : Gok g) (v p : ℕ) :
    (act g v).testBit p = (decide (p < 7) && v.testBit (g.getD p 0)) := by
  unfold act
  rw [ofb_bit]
  by_cases hp : p < 7
  · have hl : p < g.length := by rw [hg.1]; exact hp
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getD_eq_getElem _ _ hl]
    simp [hp]
  · rw [List.getD_eq_default _ _ (by simp [hg.1]; omega)]
    simp [hp]

theorem RM_act (g : List ℕ) (hg : Gok g) (S : Multiset ℕ) (m : ℕ) (h : RM S m) :
    RM (S.map (act g)) (act g m) := by
  refine h (fun S m => RM (S.map (act g)) (act g m)) (fun x => by
    rw [Multiset.map_singleton]; exact RM_leaf _) ?_
  intro S T a b hS hT
  have e1 : act g (a &&& b) = act g a &&& act g b := by
    apply Nat.eq_of_testBit_eq; intro p
    rw [Nat.testBit_and, act_bit g hg, act_bit g hg, act_bit g hg, Nat.testBit_and]
    cases decide (p < 7) <;> simp
  have e2 : act g (a ||| b) = act g a ||| act g b := by
    apply Nat.eq_of_testBit_eq; intro p
    rw [Nat.testBit_or, act_bit g hg, act_bit g hg, act_bit g hg, Nat.testBit_or]
    cases decide (p < 7) <;> simp
  rw [Multiset.map_add, e1, e2]
  exact ⟨RM_and hS hT, RM_or hS hT⟩

theorem act_neg (g : List ℕ) (hg : Gok g) (m : ℕ) : act g (FULL ^^^ m) = FULL ^^^ act g m := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [act_bit g hg]
  by_cases hp : p < 7
  · rw [FULL_bit p hp, act_bit g hg, FULL_bit _ (hg.2 p hp).1]; simp [hp]
  · have e : (FULL ^^^ act g m).testBit p = ((FULL.testBit p) ^^ ((act g m).testBit p)) := Nat.testBit_xor ..
    rw [e, act_bit g hg, FULL_hi p (by omega)]; simp [hp]

theorem Cv_act (g : List ℕ) (hg : Gok g) : ∀ ks S, Cv ks S → Cv ks (S.map (act g)) := by
  intro ks
  induction ks with
  | nil =>
    rintro S ⟨m, h1, h2⟩
    refine ⟨act g m, RM_act g hg _ _ h1, fun p hp => ?_⟩
    rw [act_bit g hg, h2 _ (hg.2 p hp).1, (hg.2 p hp).2]; simp [hp]
  | cons k ks ih =>
    intro S h
    cases k with
    | true =>
      obtain ⟨Sc, rest, mc, h1, h2, h3⟩ := h
      refine ⟨_, rest.map (act g), act g mc, by rw [h1, Multiset.map_add], RM_act g hg _ _ h2, ?_⟩
      have := ih _ h3
      rwa [Multiset.map_cons, Multiset.map_cons] at this
    | false =>
      obtain ⟨Sc, rest, mc, h1, h2, h3⟩ := h
      refine ⟨_, rest.map (act g), act g mc, by rw [h1, Multiset.map_add], RM_act g hg _ _ h2, ?_⟩
      have := ih _ h3
      rwa [Multiset.map_cons, act_neg g hg] at this

theorem Rf_act (g : List ℕ) (hg : Gok g) (b c : ℕ) (S : Multiset ℕ) (h : Rf b c (S.map (act g))) : Rf b c S :=
  fun ks h1 h2 h3 => h ks h1 h2 (Cv_act g hg ks S h3)

theorem RM_ne (S : Multiset ℕ) (m : ℕ) (h : RM S m) : S ≠ 0 := by
  rcases RM_inv S m h with h | ⟨A, B, _, _, h, hA, _⟩
  · rw [h]; simp
  · intro h0; exact hA (add_eq_zero.mp (h ▸ h0)).1

theorem Rf_zero (b c : ℕ) : Rf b c 0 := by
  intro ks _ _ h
  cases ks with
  | nil => obtain ⟨m, h1, _⟩ := h; exact RM_ne _ _ h1 rfl
  | cons k ks =>
    cases k with
    | true =>
      obtain ⟨Sc, rest, mc, h1, h2, _⟩ := h
      exact RM_ne _ _ h2 (add_eq_zero.mp h1.symm).1
    | false =>
      obtain ⟨Sc, rest, mc, h1, h2, _⟩ := h
      exact RM_ne _ _ h2 (add_eq_zero.mp h1.symm).1

def rmv (x : ℕ) : List ℕ → List ℕ → Option (List ℕ)
  | _, [] => none
  | acc, y :: l => bif Nat.beq x y then some (acc ++ l) else rmv x (y :: acc) l

theorem rmv_ok (x : ℕ) : ∀ l acc r, rmv x acc l = some r → (↑acc + ↑l : Multiset ℕ) = x ::ₘ ↑r := by
  intro l
  induction l with
  | nil => intro acc r h; simp [rmv] at h
  | cons y l ih =>
    intro acc r h
    rw [rmv] at h
    cases hb : Nat.beq x y
    · rw [hb, cond_false] at h
      have := ih _ _ h
      rw [← this, ← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]
    · rw [hb, cond_true] at h
      rw [Nat.beq_eq] at hb
      simp only [Option.some.injEq] at h
      rw [← h, ← Multiset.cons_coe, Multiset.add_cons, hb, Multiset.coe_add]

def pm : List ℕ → List ℕ → Bool
  | [], l => l.isEmpty
  | x :: xs, l => match rmv x [] l with
    | none => false
    | some r => pm xs r

theorem pm_ok : ∀ a l, pm a l = true → (↑a : Multiset ℕ) = ↑l := by
  intro a
  induction a with
  | nil => intro l h; rw [pm] at h; have : l = [] := by simpa using h
           rw [this]
  | cons x xs ih =>
    intro l h
    rw [pm] at h
    cases hr : rmv x [] l with
    | none => rw [hr] at h; simp at h
    | some r =>
      rw [hr] at h
      have h1 := rmv_ok x l [] r hr
      have h2 := ih r h
      rw [← Multiset.cons_coe, h2, ← h1]; simp

def sm (l : List ℕ) : ℕ := l.foldr Nat.add 0

def hit (T : List (List (List ℕ))) (h : List (ℕ × ℕ × ℕ)) (ch : List ℕ) : Bool :=
  frc (Nat.mod (sm ch) 512) fun s => h.any fun e => Nat.beq e.1 s &&
    pm (ch.map (act (GS.getD e.2.1 ID))) (((T.getD (e.2.2 / 64) []).getD (e.2.2 % 64) []).map vv)

theorem hit_ok (hG : ∀ g ∈ GS, Gok g) (hI : Gok ID) (b c : ℕ) (T : List (List (List ℕ))) (h : List (ℕ × ℕ × ℕ))
    (ch : List ℕ) (hT : ∀ u ∈ T, ∀ t ∈ u, Rf b c ↑(t.map vv)) (hh : hit T h ch = true) : Rf b c ↑ch := by
  unfold hit at hh
  rw [frc_eq, List.any_eq_true] at hh
  obtain ⟨e, _, he⟩ := hh
  rw [Bool.and_eq_true] at he
  have h1 := pm_ok _ _ he.2
  have hg : Gok (GS.getD e.2.1 ID) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : GS[e.2.1]? with
    | none => exact hI
    | some g => exact hG g (List.mem_of_getElem? h)
  have hR : Rf b c ↑(((T.getD (e.2.2 / 64) []).getD (e.2.2 % 64) []).map vv) := by
    rw [List.getD_eq_getElem?_getD (l := T)]
    cases h : T[e.2.2 / 64]? with
    | none => simpa using Rf_zero b c
    | some u =>
      rw [Option.getD_some, List.getD_eq_getElem?_getD]
      cases h' : u[e.2.2 % 64]? with
      | none => exact Rf_zero b c
      | some t => exact hT u (List.mem_of_getElem? h) t (List.mem_of_getElem? h')
  rw [← h1, ← Multiset.map_coe] at hR
  exact Rf_act _ hg b c _ hR

def mvs (R : List (ℕ × ℕ)) : List ℕ := R.map fun p => vv p.1

def vc (i : ℕ) : ℕ := vv (i ^^^ 1)

def Qd : List ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)
  | [] => []
  | i :: l => frc (ns (vv i)) fun n => frc (ns (vc i)) fun n' =>
      (fun r => frc (Nat.land n (r.headD (0, 0, 0, AL, AL)).2.2.2.1) fun u =>
        frc (Nat.land n' (r.headD (0, 0, 0, AL, AL)).2.2.2.2) fun u' => (i, n, n', u, u') :: r) (Qd l)

def QdOK : List (ℕ × ℕ × ℕ × ℕ × ℕ) → List ℕ → Prop
  | [], [] => True
  | t :: r, x :: l => t.1 = x ∧ t.2.1 = ns (vv x) ∧ t.2.2.1 = ns (vc x) ∧
      (∀ i, t.2.2.2.1.testBit i = true → ∀ y ∈ x :: l, (ns (vv y)).testBit i = true) ∧
      (∀ i, t.2.2.2.2.testBit i = true → ∀ y ∈ x :: l, (ns (vc y)).testBit i = true) ∧ QdOK r l
  | _, _ => False

theorem Qd_ok : ∀ l, QdOK (Qd l) l ∧
    (∀ i, ((Qd l).headD (0, 0, 0, AL, AL)).2.2.2.1.testBit i = true → ∀ y ∈ l, (ns (vv y)).testBit i = true) ∧
    ∀ i, ((Qd l).headD (0, 0, 0, AL, AL)).2.2.2.2.testBit i = true → ∀ y ∈ l, (ns (vc y)).testBit i = true := by
  intro l
  induction l with
  | nil => exact ⟨trivial, by simp, by simp⟩
  | cons x l ih =>
    have e : Qd (x :: l) = (x, ns (vv x), ns (vc x),
        Nat.land (ns (vv x)) ((Qd l).headD (0, 0, 0, AL, AL)).2.2.2.1,
        Nat.land (ns (vc x)) ((Qd l).headD (0, 0, 0, AL, AL)).2.2.2.2) :: Qd l := by
      rw [Qd, frc_eq]; beta_reduce; rw [frc_eq]; beta_reduce; rw [frc_eq]; beta_reduce; rw [frc_eq]
    have hu : ∀ i, (Nat.land (ns (vv x)) ((Qd l).headD (0, 0, 0, AL, AL)).2.2.2.1).testBit i = true →
        ∀ y ∈ x :: l, (ns (vv y)).testBit i = true := by
      intro i hi y hy
      have hi := land_bit _ _ _ hi
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hi.1
      · exact ih.2.1 i hi.2 y hy
    have hu' : ∀ i, (Nat.land (ns (vc x)) ((Qd l).headD (0, 0, 0, AL, AL)).2.2.2.2).testBit i = true →
        ∀ y ∈ x :: l, (ns (vc y)).testBit i = true := by
      intro i hi y hy
      have hi := land_bit _ _ _ hi
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hi.1
      · exact ih.2.2 i hi.2 y hy
    rw [e]
    exact ⟨⟨rfl, rfl, rfl, hu, hu', ih.1⟩, hu, hu'⟩

-- all ways to choose the leaves of the next step, with a test that stops a branch
def dfs (dead : ℕ → ℕ → ℕ → ℕ → Bool)
    (K : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ → ℕ → Bool) :
    List (ℕ × ℕ × ℕ × ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) →
      ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], A, A', R, a, a', r, r', _ => dead a a' r r' || K A A' R r r'
  | t :: l, A, A', R, a, a', r, r', w =>
    (frc (Nat.land a t.2.2.2.1) fun x => frc (Nat.land a' t.2.2.2.2) fun x' =>
      frc (Nat.land r t.2.2.2.1) fun y => frc (Nat.land r' t.2.2.2.2) fun y' => dead x x' y y') ||
    ((Nat.beq (Nat.succ t.1) w ||
      (frc (Nat.land a t.2.1) fun x => frc (Nat.land a' t.2.2.1) fun x' => frc (Nat.xor t.1 1) fun j =>
        dfs dead K l ((t.1, t.2.1) :: A) ((j, t.2.2.1) :: A') R x x' r r' 0)) &&
     (frc (Nat.land r t.2.1) fun y => frc (Nat.land r' t.2.2.1) fun y' =>
        dfs dead K l A A' ((t.1, t.2.1) :: R) a a' y y' (Nat.succ t.1)))

theorem Acc_cons (f : ℕ → ℕ) (x a : ℕ) (S : Multiset ℕ) (h : Acc (S.map f) a) :
    Acc ((x ::ₘ S).map f) (Nat.land a (ns (f x))) := by
  intro i hi v hv
  have hi := land_bit _ _ _ hi
  rw [Multiset.map_cons, Multiset.mem_cons] at hv
  rcases hv with rfl | hv
  · exact hi.2
  · exact h i hi.1 v hv

theorem dfs_sound (dead : ℕ → ℕ → ℕ → ℕ → Bool)
    (K : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ → ℕ → Bool) (SA SR : Multiset ℕ)
    (hd : ∀ a a' r r', Acc (SA.map vv) a → Acc (SA.map vc) a' → Acc (SR.map vv) r → Acc (SR.map vc) r' →
      dead a a' r r' = true → False) :
    ∀ (l : List ℕ) (tr : List (ℕ × ℕ × ℕ × ℕ × ℕ)), QdOK tr l →
      ∀ (A A' R : List (ℕ × ℕ)) (RA RR : Multiset ℕ) (a a' r r' w : ℕ), (↑l : Multiset ℕ) = RA + RR →
      ↑(A.map Prod.fst) + RA = SA → ↑(R.map Prod.fst) + RR = SR → (∀ i, w = i + 1 → i ∉ RA) →
      (∀ p ∈ A, p.2 = ns (vv p.1)) → A' = cm A → (∀ p ∈ R, p.2 = ns (vv p.1)) →
      Acc ((↑(A.map Prod.fst) : Multiset ℕ).map vv) a → Acc ((↑(A.map Prod.fst) : Multiset ℕ).map vc) a' →
      Acc ((↑(R.map Prod.fst) : Multiset ℕ).map vv) r → Acc ((↑(R.map Prod.fst) : Multiset ℕ).map vc) r' →
      dfs dead K tr A A' R a a' r r' w = true →
      ∃ Af Rf r r', K Af (cm Af) Rf r r' = true ∧ ↑(Af.map Prod.fst) = SA ∧ ↑(Rf.map Prod.fst) = SR ∧
        (∀ p ∈ Af, p.2 = ns (vv p.1)) ∧ (∀ p ∈ Rf, p.2 = ns (vv p.1)) ∧
        Acc (SR.map vv) r ∧ Acc (SR.map vc) r' := by
  intro l
  induction l with
  | nil =>
    intro tr htr A A' R RA RR a a' r r' w hl hA hR _ oA eA oR ha ha' hr hr' h
    have h0 : RA + RR = 0 := by rw [← hl]; rfl
    obtain ⟨r1, r2⟩ := add_eq_zero.mp h0
    rw [r1, add_zero] at hA
    rw [r2, add_zero] at hR
    cases tr with
    | cons => exact htr.elim
    | nil =>
      rw [dfs, Bool.or_eq_true] at h
      rw [hA] at ha ha'
      rw [hR] at hr hr'
      rcases h with h | h
      · exact (hd a a' r r' ha ha' hr hr' h).elim
      · rw [eA] at h
        exact ⟨A, R, r, r', h, hA, hR, oA, oR, hr, hr'⟩
  | cons v l ih =>
    intro tr htr A A' R RA RR a a' r r' w hl hA hR hw oA eA oR ha ha' hr hr' h
    cases tr with
    | nil => exact htr.elim
    | cons t tr =>
      obtain ⟨t1, t2, t3, t4, t5, t6⟩ := htr
      rw [dfs, Bool.or_eq_true] at h
      simp only [frc_eq] at h
      rw [t1, t2, t3] at h
      have hRA : RA ≤ ↑(v :: l) := by rw [hl]; exact Multiset.le_add_right _ _
      have hRR : RR ≤ ↑(v :: l) := by rw [hl]; exact Multiset.le_add_left _ _
      have hu : Acc (Multiset.map vv ↑(v :: l)) t.2.2.2.1 := by
        intro i hi z hz
        obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hz
        exact t4 i hi y' (by simpa using hy')
      have hu' : Acc (Multiset.map vc ↑(v :: l)) t.2.2.2.2 := by
        intro i hi z hz
        obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hz
        exact t5 i hi y' (by simpa using hy')
      rcases h with h | h
      · refine (hd _ _ _ _ ?_ ?_ ?_ ?_ h).elim
        · rw [← hA, Multiset.map_add]; exact Acc_add _ _ _ _ ha (Acc_le _ _ _ hu (Multiset.map_le_map hRA))
        · rw [← hA, Multiset.map_add]; exact Acc_add _ _ _ _ ha' (Acc_le _ _ _ hu' (Multiset.map_le_map hRA))
        · rw [← hR, Multiset.map_add]; exact Acc_add _ _ _ _ hr (Acc_le _ _ _ hu (Multiset.map_le_map hRR))
        · rw [← hR, Multiset.map_add]; exact Acc_add _ _ _ _ hr' (Acc_le _ _ _ hu' (Multiset.map_le_map hRR))
      · rw [Bool.and_eq_true, Bool.or_eq_true] at h
        have hv : v ∈ RA + RR := by rw [← hl]; simp
        by_cases hvA : v ∈ RA
        · obtain ⟨RA', rfl⟩ := Multiset.exists_cons_of_mem hvA
          have hl' : (↑l : Multiset ℕ) = RA' + RR := by
            rw [← Multiset.cons_coe, Multiset.cons_add] at hl
            exact (Multiset.cons_inj_right v).mp hl
          have h := h.1.resolve_left (fun hb => hw v (by rw [Nat.beq_eq] at hb; exact hb.symm) (by simp))
          refine ih tr t6 _ _ R RA' RR _ _ r r' 0 hl' ?_ hR (fun i hi => by omega) ?_ ?_ oR ?_ ?_ hr hr' h
          · rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add, ← hA, Multiset.add_cons]
          · intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · rfl
            · exact oA p hp
          · rw [cm_eq, List.map_cons, eA, cm_eq]; rfl
          · rw [List.map_cons, ← Multiset.cons_coe]; exact Acc_cons vv v a _ ha
          · rw [List.map_cons, ← Multiset.cons_coe]; exact Acc_cons vc v a' _ ha'
        · have hvB : v ∈ RR := (Multiset.mem_add.mp hv).resolve_left hvA
          obtain ⟨RR', rfl⟩ := Multiset.exists_cons_of_mem hvB
          have hl' : (↑l : Multiset ℕ) = RA + RR' := by
            rw [← Multiset.cons_coe, Multiset.add_cons] at hl
            exact (Multiset.cons_inj_right v).mp hl
          refine ih tr t6 A A' _ RA RR' a a' _ _ (Nat.succ v) hl' hA ?_ (fun i hi => ?_) oA eA ?_ ha ha' ?_ ?_ h.2
          · rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add, ← hR, Multiset.add_cons]
          · have : i = v := by omega
            rw [this]; exact hvA
          · intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · rfl
            · exact oR p hp
          · rw [List.map_cons, ← Multiset.cons_coe]; exact Acc_cons vv v r _ hr
          · rw [List.map_cons, ← Multiset.cons_coe]; exact Acc_cons vc v r' _ hr'

def dS (a _ r _ : ℕ) : Bool := frc (Nat.land M0 r) fun M => !(Nat.beq (Nat.land (mat (rc M) (cc M)) a) 0)
def dN (_ a' r _ : ℕ) : Bool := frc (Nat.land M0 r) fun M => !(Nat.beq (Nat.land (mat (rc M) (cc M)) a') 0)
def dU (a a' r r' : ℕ) : Bool := !(Nat.beq (Nat.land M0 (Nat.land (Nat.land r r') (Nat.land a a'))) 0)

def KS (look : ℕ → ℕ → ℕ → Bool) (ht : List ℕ → Bool) (A _ R : List (ℕ × ℕ)) (r _ : ℕ) : Bool :=
  R.isEmpty || (frc (Nat.land M0 r) fun M => (gz look A M).all fun z => ht (z :: z :: mvs R))
def KN (look : ℕ → ℕ → ℕ → Bool) (ht : List ℕ → Bool) (_ A' R : List (ℕ × ℕ)) (r _ : ℕ) : Bool :=
  frc (Nat.land M0 r) fun M => (gz look A' M).all fun z => ht (z :: mvs R)
def KUS (look : ℕ → ℕ → ℕ → Bool) (ht : List ℕ → Bool) (A A' R : List (ℕ × ℕ)) (r r' : ℕ) : Bool :=
  frc (Nat.land M0 (Nat.land r r')) fun M => (uz look A A' M).all fun z => ht (z :: z :: mvs R)
def KUN (look : ℕ → ℕ → ℕ → Bool) (ht : List ℕ → Bool) (A A' R : List (ℕ × ℕ)) (r r' : ℕ) : Bool :=
  frc (Nat.land M0 (Nat.land r r')) fun M => (uz look A A' M).all fun z => ht (Nat.xor FULL z :: mvs R)

def rn (dead : ℕ → ℕ → ℕ → ℕ → Bool)
    (K : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ → ℕ → Bool) (l : List ℕ) : Bool :=
  dfs dead K (Qd l) [] [] [] AL AL AL AL 0

def okst (look : ℕ → ℕ → ℕ → Bool) (b c : ℕ) (TS TN : List (List (List ℕ))) (hS hN : List (ℕ × ℕ × ℕ))
    (l : List ℕ) : Bool :=
  l.all (fun i => Nat.ble 2 i && Nat.blt i NV) && (Nat.ble l.length 16 && ((rf look l ONE FZ ||
    (gq look 16 (Dp l.reverse) ONE FZ).isEmpty) &&
  ((bif Nat.beq b 0 then true else bif Nat.beq c 0 then rn dS (KS look (hit TS hS)) l
      else rn dU (KUS look (hit TS hS)) l) &&
   (bif Nat.beq c 0 then true else bif Nat.beq c 1 then rn dN (KN look (hit TN hN)) l
      else rn dU (KUN look (hit TN hN)) l))))

theorem splits_perm {α : Type} : ∀ (l : List α), ∀ s ∈ splits l, (↑l : Multiset α) = ↑s.1 + ↑s.2 := by
  intro l
  induction l with
  | nil => intro s hs; simp [splits] at hs; subst hs; rfl
  | cons x l ih =>
    intro s hs
    simp only [splits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain ⟨u, hu, rfl | rfl⟩ := hs
    · rw [← Multiset.cons_coe, ih u hu, ← Multiset.cons_coe, Multiset.cons_add]
    · rw [← Multiset.cons_coe, ih u hu, ← Multiset.cons_coe, Multiset.add_cons]

theorem agree_sep (m : ℕ) (h : ∀ p < 7, m.testBit p = MM.testBit p) : Sep ONE FZ m := by
  intro p t hp ht _ _
  rw [h p (by omega), h (3 + t) (by omega)]
  unfold MM
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  simp [hp]

theorem okst_sound (hC : cpc = true) (hN : NV ≤ 1024) (hG : ∀ g ∈ GS, Gok g) (hI : Gok ID)
    (look : ℕ → ℕ → ℕ → Bool) (hk : ∀ N, LookOK N look) (b c : ℕ) (TS TN : List (List (List ℕ)))
    (hS hN' : List (ℕ × ℕ × ℕ)) (l : List ℕ) (hTS : b ≠ 0 → ∀ u ∈ TS, ∀ t ∈ u, Rf (b - 1) c ↑(t.map vv))
    (hTN : c ≠ 0 → ∀ u ∈ TN, ∀ t ∈ u, Rf b (c - 1) ↑(t.map vv)) (h : okst look b c TS TN hS hN' l = true) :
    Rf b c ↑(l.map vv) := by
  unfold okst at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have h16 : l.length ≤ 16 := Nat.le_of_ble_eq_true h2
  have hl : ∀ i ∈ l, 2 ≤ i ∧ i < NV := fun i hi => by
    have := h1 i hi
    rw [Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨Nat.le_of_ble_eq_true this.1, this.2⟩
  have hOk : Ok l := fun i hi => ⟨by have := (hl i hi).1; omega, lt_of_lt_of_le (hl i hi).2 hN⟩
  have hDV : Vd (Dp l.reverse) := by
    intro p hp
    rw [Dp_eq] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := hl i (by simpa using hi)
    exact ⟨this.1, this.2, rfl⟩
  have hDm : (↑((Dp l.reverse).map fun p => vv p.1) : Multiset ℕ) = ↑(l.map vv) := by
    rw [Dp_eq, List.map_map]
    change (↑(l.reverse.map vv) : Multiset ℕ) = _
    rw [List.map_reverse]
    exact Multiset.coe_eq_coe.mpr (List.reverse_perm _)
  have hDl : (Dp l.reverse).length ≤ 16 := by rw [Dp_eq]; simpa using h16
  have hNof : Nof l ONE FZ := by
    rw [Bool.or_eq_true] at h3
    rcases h3 with h3 | h3
    · exact rf_sound look l ONE FZ (hk _) hOk h16 h3
    · intro m hR hm
      have := gq_mem look hk 16 (Dp l.reverse) ONE FZ m (Vd_Pr hN _ hDV) hDl hDl (by rw [hDm]; exact hR) hm
      rw [List.isEmpty_iff.mp h3] at this
      simp at this
  intro ks hb hc hCv
  -- the parts of a step
  have split : ∀ (Sc rest : Multiset ℕ) (mc : ℕ), (↑(l.map vv) : Multiset ℕ) = Sc + rest → RM Sc mc →
      ∃ SA SR : Multiset ℕ, (↑l : Multiset ℕ) = SA + SR ∧ SA.map vv = Sc ∧ SR.map vv = rest ∧
        (∀ i ∈ SA, i ∈ l) ∧ (∀ i ∈ SR, i ∈ l) ∧ SA.card ≤ 16 := by
    intro Sc rest mc hS hR
    obtain ⟨s, hs, e1, e2, e3, e4, e5⟩ := mem_splits vv l Sc rest hS
    exact ⟨↑s.1, ↑s.2, splits_perm l s hs, by rw [Multiset.map_coe, e1], by rw [Multiset.map_coe, e2], by
      simpa using e3, by simpa using e4, by simp; omega⟩
  -- what the search gives for the leaves of the step
  have run : ∀ (dead : ℕ → ℕ → ℕ → ℕ → Bool)
      (K : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ → ℕ → Bool) (SA SR : Multiset ℕ) (mc : ℕ),
      (↑l : Multiset ℕ) = SA + SR → (∀ i ∈ SA, i ∈ l) → (∀ i ∈ SR, i ∈ l) → SA.card ≤ 16 → RM (SA.map vv) mc →
      rn dead K l = true →
      (∀ a a' r r', Acc (SA.map vv) a → Acc (SA.map vc) a' → Acc (SR.map vv) r → Acc (SR.map vc) r' →
        dead a a' r r' = true → False) →
      ∃ A R r r', K A (cm A) R r r' = true ∧ Vd A ∧ A.length ≤ 16 ∧ RM ↑(A.map fun p => vv p.1) mc ∧
        (↑(mvs R) : Multiset ℕ) = SR.map vv ∧ Acc (SR.map vv) r ∧ Acc (SR.map vc) r' ∧ (R = [] → SR = 0) := by
    intro dead K SA SR mc hlS hSA hSR h16' hR hrn hd
    obtain ⟨A, R, r, r', k1, k2, k3, k4, k5, k6, k7⟩ := dfs_sound dead K SA SR hd l (Qd l) (Qd_ok l).1 [] [] []
      SA SR AL AL AL AL 0 hlS (by simp) (by simp) (fun i hi => by omega) (by simp) rfl (by simp)
      (fun i _ v hv => by simp at hv) (fun i _ v hv => by simp at hv) (fun i _ v hv => by simp at hv)
      (fun i _ v hv => by simp at hv) hrn
    refine ⟨A, R, r, r', k1, ?_, ?_, ?_, ?_, k6, k7, ?_⟩
    · intro p hp
      have : p.1 ∈ SA := by rw [← k2]; exact Multiset.mem_coe.mpr (List.mem_map_of_mem (f := Prod.fst) hp)
      have := hl p.1 (hSA _ this)
      exact ⟨this.1, this.2, k4 p hp⟩
    · have := congrArg Multiset.card k2
      simp at this; omega
    · have e : (↑(A.map fun p => vv p.1) : Multiset ℕ) = SA.map vv := by
        rw [← k2, Multiset.map_coe, List.map_map]; rfl
      rw [e]; exact hR
    · unfold mvs
      rw [← k3, Multiset.map_coe, List.map_map]; rfl
    · intro h0; rw [← k3, h0]; rfl
  have hcmp : ∀ SA : Multiset ℕ, (∀ i ∈ SA, i ∈ l) → SA.map vc = (SA.map vv).map fun v => FULL ^^^ v := by
    intro SA hSA
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i hi
    have := hl i (hSA i hi)
    exact (cpc_ok hC i this.1 this.2).1
  have hlt : ∀ SA : Multiset ℕ, ∀ v ∈ SA.map vv, v < 2 ^ 7 := by
    intro SA v hv
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hv
    exact vv_lt i
  have heq : ∀ (S : Multiset ℕ), (∀ i ∈ S, i ∈ l) → ∀ r r' i, V i → Acc (S.map vv) r → Acc (S.map vc) r' →
      r.testBit i = true → r'.testBit i = true → ∀ v ∈ S.map vv, v.testBit (po i) = v.testBit (zo i) := by
    intro S hSl r r' i hVi hr hr' h1 h2 v hv
    have b1 := (ns_bit v i (hr i h1 v hv)).2
    have b2 := (ns_bit (FULL ^^^ v) i (hr' i h2 _ (by
      rw [hcmp S hSl]; exact Multiset.mem_map_of_mem (fun v => FULL ^^^ v) hv))).2
    rw [FULL_bit _ (po_ok i hVi).1, FULL_bit _ (zo_ok i hVi).1] at b2
    cases hp : v.testBit (po i) <;> cases hz : v.testBit (zo i) <;> simp_all
  have hdir : ∀ (SR : Multiset ℕ) (r v : ℕ) (ks : List Bool) (S : Multiset ℕ), Acc (SR.map vv) r →
      ks.count false = 0 → Cv ks S → (∀ u ∈ S, u = v ∨ u ∈ SR.map vv) →
      ∀ i, (Nat.land M0 r).testBit i = true → V i ∧ v.testBit (po i) = true ∧ v.testBit (zo i) = false := by
    intro SR r v ks S hr hk0 hCv hmem i hi
    have hi := land_bit _ _ _ hi
    have hVi := M0_V i hi.1
    obtain ⟨u, hu, hs⟩ := Cv_dir i hVi ks hk0 _ hCv
    rcases hmem u hu with rfl | hu
    · exact ⟨hVi, hs⟩
    · exact absurd hs (ns_bit u i (hr i hi.2 u hu)).2
  have hund : ∀ (SR : Multiset ℕ) (r r' v : ℕ) (ks : List Bool) (S : Multiset ℕ), (∀ i ∈ SR, i ∈ l) →
      Acc (SR.map vv) r → Acc (SR.map vc) r' → Cv ks S → (∀ u ∈ S, u = v ∨ u = FULL ^^^ v ∨ u ∈ SR.map vv) →
      Dif (Nat.land M0 (Nat.land r r')) v := by
    intro SR r r' v ks S hSl hr hr' hCv hmem i hi
    have hi := land_bit _ _ _ hi
    have hj := land_bit _ _ _ hi.2
    have hVi := M0_V i hi.1
    refine ⟨hVi, ?_⟩
    obtain ⟨u, hu, hs⟩ := Cv_und i hVi ks _ hCv
    rcases hmem u hu with rfl | rfl | hu
    · exact hs
    · rw [FULL_bit _ (po_ok i hVi).1, FULL_bit _ (zo_ok i hVi).1] at hs
      intro e; exact hs (by rw [e])
    · exact absurd (heq SR hSl r r' i hVi hr hr' hj.1 hj.2 u hu) hs
  -- the two tests that stop a branch
  have hdd : ∀ (SA SR : Multiset ℕ) (m : ℕ) (a r : ℕ), RM SA m → Acc SA a →
      (∀ i, (Nat.land M0 r).testBit i = true → V i ∧ m.testBit (po i) = true ∧ m.testBit (zo i) = false) →
      (!(Nat.beq (Nat.land (mat (rc (Nat.land M0 r)) (cc (Nat.land M0 r))) a) 0)) = true → False := by
    intro SA SR m a r hR ha hM h
    refine all_un SA (rc (Nat.land M0 r)) (cc (Nat.land M0 r)) m a ?_ hR ha (by simpa using h)
    intro p t hp ht h1 h2
    obtain ⟨_, _, i, h3, h4⟩ := rc_bit _ _ h1
    obtain ⟨_, j, h5, h6⟩ := cc_bit _ _ h2
    rw [Nat.mul_div_cancel_left p (by norm_num)] at h4
    have a1 := (hM i h3).2.1
    have a2 := (hM j h5).2.2
    unfold po at a1
    unfold zo at a2
    rw [h4] at a1
    rw [h6] at a2
    exact ⟨a1, a2⟩
  have hdU : ∀ (SA SR : Multiset ℕ) (mc : ℕ), (∀ i ∈ SA, i ∈ l) → (∀ i ∈ SR, i ∈ l) → RM (SA.map vv) mc →
      (∀ r r', Acc (SR.map vv) r → Acc (SR.map vc) r' → Dif (Nat.land M0 (Nat.land r r')) mc) →
      ∀ a a' r r', Acc (SA.map vv) a → Acc (SA.map vc) a' → Acc (SR.map vv) r → Acc (SR.map vc) r' →
        dU a a' r r' = true → False := by
    intro SA SR mc hA hR hRM hD a a' r r' ha ha' hr hr' h
    unfold dU at h
    obtain ⟨i, hi⟩ := bit_of_ne _ (by simpa using h)
    have hi := land_bit _ _ _ hi
    have hj := land_bit _ _ _ hi.2
    have hk' := land_bit _ _ _ hj.2
    have hVi := M0_V i hi.1
    exact (hD r r' hr hr' i (land_bit' _ _ _ hi.1 hj.1)).2
      (RM_eq _ _ _ _ hRM (heq SA hA a a' i hVi ha ha' hk'.1 hk'.2))
  cases ks with
  | nil =>
    obtain ⟨m, r1, r2⟩ := hCv
    exact hNof m r1 (agree_sep m r2)
  | cons k ks =>
    cases k with
    | true =>
      obtain ⟨Sc, rest, mc, e1, r1, r2⟩ := hCv
      rw [List.count_cons_self] at hb
      have hc' : ks.count false ≤ c := by simpa using hc
      have hb0 : b ≠ 0 := by omega
      have hbb : Nat.beq b 0 = false := Bool.eq_false_iff.mpr (by rw [Ne, Nat.beq_eq]; exact hb0)
      rw [hbb, cond_false] at h4
      obtain ⟨SA, SR, p1, p2, p3, p4, p5, p6⟩ := split Sc rest mc e1 r1
      rw [← p2] at r1
      rw [← p3] at r2
      have hin : ∀ u ∈ mc ::ₘ mc ::ₘ SR.map vv, u = mc ∨ u ∈ SR.map vv := by
        intro u hu
        simp only [Multiset.mem_cons] at hu
        rcases hu with h | h | h
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inr h
      have fin : ∀ R : List (ℕ × ℕ), (↑(mvs R) : Multiset ℕ) = SR.map vv →
          hit TS hS (mc :: mc :: mvs R) = true → False := by
        intro R hmR hh
        refine hit_ok hG hI (b - 1) c TS hS _ (hTS hb0) hh ks (by omega) hc' ?_
        rw [← Multiset.cons_coe, ← Multiset.cons_coe, hmR]
        exact r2
      cases hc0 : Nat.beq c 0
      · rw [hc0, cond_false] at h4
        obtain ⟨A, R, r, r', k1, k2, k3, k4, k5, k6, k7, _⟩ := run _ _ SA SR mc p1 p4 p5 p6 r1 h4
          (hdU SA SR mc p4 p5 r1 (fun r r' hr hr' => hund SR r r' mc ks _ p5 hr hr' r2 (fun u hu =>
            (hin u hu).imp id Or.inr)))
        unfold KUS at k1
        rw [frc_eq, List.all_eq_true] at k1
        exact fin R k5 (k1 mc (uz_mem hC hN look hk A _ mc k2 k3 k4 (hund SR r r' mc ks _ p5 k6 k7 r2 (fun u hu =>
          (hin u hu).imp id Or.inr))))
      · rw [hc0, cond_true] at h4
        rw [Nat.beq_eq] at hc0
        have hk0 : ks.count false = 0 := by omega
        obtain ⟨A, R, r, r', k1, k2, k3, k4, k5, k6, k7, k8⟩ := run _ _ SA SR mc p1 p4 p5 p6 r1 h4 (by
          intro a a' r r' ha _ hr _ h
          unfold dS at h
          rw [frc_eq] at h
          exact hdd (SA.map vv) SR mc a r r1 ha (hdir SR r mc ks _ hr hk0 r2 hin) h)
        unfold KS at k1
        rw [Bool.or_eq_true, frc_eq, List.all_eq_true] at k1
        rcases k1 with k1 | k1
        · have hs0 := k8 (by simpa using k1)
          rw [hs0, Multiset.map_zero] at p3 hin r2
          have hfull : RM ↑(l.map vv) mc := by
            rw [e1, ← p2, ← p3, add_zero]; exact r1
          refine hNof mc hfull ?_
          intro p t hp ht _ _
          have hVi : V (8 * p + t) := by
            refine ⟨?_, ?_⟩
            · rw [show (8 * p + t) / 8 = p by omega]; exact hp
            · rw [show (8 * p + t) % 8 = t by omega]; exact ht
          obtain ⟨u, hu, hsu⟩ := Cv_dir _ hVi ks hk0 _ r2
          have hu' : u = mc := by
            rcases hin u hu with h | h
            · exact h
            · simp at h
          rw [hu'] at hsu
          unfold po zo at hsu
          rwa [show (8 * p + t) / 8 = p by omega, show (8 * p + t) % 8 = t by omega] at hsu
        · exact fin R k5 (k1 mc (gz_mem look hk A _ mc (Vd_Pr hN _ k2) k3 k4 (hdir SR r mc ks _ k6 hk0 r2 hin)))
    | false =>
      obtain ⟨Sc, rest, mc, e1, r1, r2⟩ := hCv
      rw [List.count_cons_self] at hc
      have hb' : ks.count true ≤ b := by simpa using hb
      have hc0 : c ≠ 0 := by omega
      have hcb : Nat.beq c 0 = false := Bool.eq_false_iff.mpr (by rw [Ne, Nat.beq_eq]; exact hc0)
      rw [hcb, cond_false] at h5
      obtain ⟨SA, SR, p1, p2, p3, p4, p5, p6⟩ := split Sc rest mc e1 r1
      rw [← p2] at r1
      rw [← p3] at r2
      have hin : ∀ u ∈ (FULL ^^^ mc) ::ₘ SR.map vv, u = FULL ^^^ mc ∨ u ∈ SR.map vv := by
        intro u hu
        exact Multiset.mem_cons.mp hu
      have fin : ∀ R : List (ℕ × ℕ), (↑(mvs R) : Multiset ℕ) = SR.map vv →
          hit TN hN' ((FULL ^^^ mc) :: mvs R) = true → False := by
        intro R hmR hh
        refine hit_ok hG hI b (c - 1) TN hN' _ (hTN hc0) hh ks hb' (by omega) ?_
        rw [← Multiset.cons_coe, hmR]
        exact r2
      cases hc1 : Nat.beq c 1
      · rw [hc1, cond_false] at h5
        obtain ⟨A, R, r, r', k1, k2, k3, k4, k5, k6, k7, _⟩ := run _ _ SA SR mc p1 p4 p5 p6 r1 h5
          (hdU SA SR mc p4 p5 r1 (fun r r' hr hr' => hund SR r r' mc ks _ p5 hr hr' r2 (fun u hu =>
            Or.inr (hin u hu))))
        unfold KUN at k1
        rw [frc_eq, List.all_eq_true] at k1
        exact fin R k5 (k1 mc (uz_mem hC hN look hk A _ mc k2 k3 k4 (hund SR r r' mc ks _ p5 k6 k7 r2 (fun u hu =>
          Or.inr (hin u hu)))))
      · rw [hc1, cond_true] at h5
        rw [Nat.beq_eq] at hc1
        have hk0 : ks.count false = 0 := by omega
        have r1' : RM (SA.map vc) (FULL ^^^ mc) := by
          rw [hcmp SA p4]; exact RM_neg _ _ r1 (hlt SA)
        obtain ⟨A, R, r, r', k1, k2, k3, k4, k5, k6, k7, k8⟩ := run _ _ SA SR mc p1 p4 p5 p6 r1 h5 (by
          intro a a' r r' _ ha' hr _ h
          unfold dN at h
          rw [frc_eq] at h
          exact hdd (SA.map vc) SR _ a' r r1' ha' (hdir SR r _ ks _ hr hk0 r2 hin) h)
        unfold KN at k1
        rw [frc_eq, List.all_eq_true] at k1
        exact fin R k5 (k1 _ (gz_mem look hk (cm A) _ _ (Vd_Pr hN _ (cm_Vd hC _ k2)) (by rw [cm_len]; exact k3)
          (cm_RM hC _ k2 mc k4) (hdir SR r _ ks _ k6 hk0 r2 hin)))

theorem ckt_node (look : ℕ → ℕ → ℕ → Bool) (v : ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) (l r : BinaryTree (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)))
    (h1 : ckv look v = true) (h2 : ckt look l = true) (h3 : ckt look r = true) :
    ckt look (BinaryTree.node v l r) = true := by
  rw [ckt, h1, h2, h3]; rfl

def ckl (look : ℕ → ℕ → ℕ → Bool) (b c : ℕ) (TS TN : List (List (List ℕ)))
    (Z : List (List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ))) : Bool :=
  Z.all fun x => okst look b c TS TN x.2.1 x.2.2 x.1

theorem ckl_ok (hC : cpc = true) (hN : NV ≤ 1024) (hG : ∀ g ∈ GS, Gok g) (hI : Gok ID)
    (look : ℕ → ℕ → ℕ → Bool) (hk : ∀ N, LookOK N look) (b c : ℕ) (TS TN : List (List (List ℕ)))
    (Z : List (List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)))
    (hTS : b ≠ 0 → ∀ u ∈ TS, ∀ t ∈ u, Rf (b - 1) c ↑(t.map vv))
    (hTN : c ≠ 0 → ∀ u ∈ TN, ∀ t ∈ u, Rf b (c - 1) ↑(t.map vv)) (h : ckl look b c TS TN Z = true)
    (T : List (List ℕ)) (hT : T = Z.map Prod.fst) : ∀ t ∈ T, Rf b c ↑(t.map vv) := by
  intro t ht
  rw [hT] at ht
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
  unfold ckl at h
  rw [List.all_eq_true] at h
  exact okst_sound hC hN hG hI look hk b c TS TN _ _ _ hTS hTN (h x hx)

theorem pieces (look : ℕ → ℕ → ℕ → Bool) (b c : ℕ) (TS TN : List (List (List ℕ)))
    (Z : List (List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ))) (k m : ℕ) (hk : 0 < k) (hm : Z.length ≤ k * m)
    (h : ∀ j < m, ckl look b c TS TN ((Z.drop (k * j)).take k) = true) : ckl look b c TS TN Z = true := by
  unfold ckl
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj : i / k < m := by
    rw [Nat.div_lt_iff_lt_mul hk]
    calc i < Z.length := hi
      _ ≤ k * m := hm
      _ = m * k := Nat.mul_comm _ _
  have h1 := h (i / k) hj
  unfold ckl at h1
  rw [List.all_eq_true] at h1
  apply h1
  have e := Nat.div_add_mod i k
  have hr := Nat.mod_lt i hk
  rw [List.mem_iff_getElem]
  refine ⟨i % k, by simp only [List.length_take, List.length_drop]; omega, ?_⟩
  rw [List.getElem_take, List.getElem_drop]
  congr 1

def gok (g : List ℕ) : Bool := Nat.beq g.length 7 && (List.range 7).all fun p =>
  Nat.blt (g.getD p 0) 7 && (Nat.testBit MM (g.getD p 0) == Nat.testBit MM p)

theorem gok_ok (g : List ℕ) (h : gok g = true) : Gok g := by
  unfold gok at h
  rw [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  refine ⟨h.1, fun p hp => ?_⟩
  have := h.2 p (List.mem_range.mpr hp)
  rw [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at this
  exact this

theorem cnt_len : ∀ ks : List Bool, ks.count true + ks.count false = ks.length := by
  intro ks
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    cases k with
    | true => rw [List.count_cons_self, List.count_cons_of_ne (by decide), List.length_cons]; omega
    | false => rw [List.count_cons_self, List.count_cons_of_ne (by decide), List.length_cons]; omega

theorem lower (f : (Fin 3 → Bool) → Bool)
    (hf : ∀ p < 7, f (fun i => Nat.testBit (PT.getD p 0) i) = MM.testBit p) (s e : ℕ)
    (hs : s + 1 ≤ 3 + e)
    (hess : ∀ i < 3, ∃ p < 7, ∃ q < 7, MM.testBit p ≠ MM.testBit q ∧
      ∀ t < 3, t ≠ i → (X p).getD t false = (X q).getD t false)
    (hnt : ∃ p < 7, MM.testBit p = false) (base : List ℕ)
    (hb : pm ((List.range 3).map lf) (base.map vv) = true)
    (hall : ∀ c ≤ e, Rf (e - c) c ↑(base.map vv)) : ¬ HasCircuitSize 3 f s := by
  intro hcs
  obtain ⟨C, hgood, hsize, hrep, hirr⟩ := min_circ f hf s hcs
  have hD : ∀ D : Finset ℕ, D ⊆ Finset.range 3 →
      (∀ x y : List Bool, x.length = 3 → y.length = 3 →
        (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) →
      D = Finset.range 3 := by
    intro D hD8 hD
    apply Finset.Subset.antisymm hD8
    intro i hi
    have hi := Finset.mem_range.mp hi
    by_contra hiD
    obtain ⟨p, hp, q, hq, hne, hpq⟩ := hess i hi
    apply hne
    rw [← hrep p hp, ← hrep q hq]
    apply hD _ _ (X_len _) (X_len _)
    intro t ht
    exact hpq t (Finset.mem_range.mp (hD8 ht)) (fun e => hiD (e ▸ ht))
  have hev : ∀ x, C.eval x = (W C.gates x).getD C.output false := fun x => rfl
  have hv : ∀ p < 7, vl C.gates C.output p = MM.testBit p := fun p hp => hrep p hp
  by_cases ho : C.output < 3 + C.gates.length
  swap
  · have := hD ∅ (by simp) (fun x y hx hy _ => by
      rw [hev, hev, getD_big _ _ (by rw [W_len]; omega), getD_big _ _ (by rw [W_len]; omega)])
    have h3 := congrArg Finset.card this
    simp at h3
  · obtain ⟨D, d1, d2, j, d3, d5⟩ := main C.gates hgood hirr {C.output} (by simpa using ho) (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      obtain ⟨p, hp, h⟩ := hnt
      exact ⟨p, hp, by rw [hw, hv p hp]; exact h⟩)
    have hDa := hD D d1 (fun x y hx hy hxy => d2 x y hx hy hxy C.output (by simp))
    rw [Finset.card_singleton, hDa, Finset.card_range] at d3
    rw [hDa] at d5
    obtain ⟨ks, hk, hc⟩ := Ch_Cv C.output (vl C.gates) hv j _ d5
    have e1 : ((Finset.range 3).val.map lf : Multiset ℕ) = ↑(base.map vv) := by
      rw [← pm_ok _ _ hb]; rfl
    rw [e1] at hc
    have hlen := cnt_len ks
    exact hall (ks.count false) (by omega) ks (by omega) le_rfl hc

def s7 : ℕ := 0x10101

def t0 : BinaryTree (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) := (BinaryTree.node (2101254, [(s7, 15)], []) BinaryTree.nil BinaryTree.nil)

def LK : ℕ → ℕ → ℕ → Bool := lk t0

theorem u0 : ckt LK t0 = true := by decide +kernel

theorem hk : ∀ N, LookOK N LK := LookOK_all t0 u0

theorem hC : cpc = true := by decide +kernel

theorem hN : NV ≤ 1024 := by decide

theorem hG : ∀ g ∈ GS, Gok g := fun g hg => gok_ok g (List.all_eq_true.mp (by decide +kernel : GS.all gok = true) g hg)

theorem hI : Gok ID := gok_ok ID (by decide +kernel)

def Z0_0_0 : List (List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)) := [([2,2,4,6],[],[])]

def T0_0 : List (List (List ℕ)) := [Z0_0_0.map Prod.fst]

theorem k0_0_0_0 : ckl LK 0 0 [] [] ((Z0_0_0.drop (16 * 0)).take 16) = true := by decide +kernel

theorem K0_0_0 : ckl LK 0 0 [] [] Z0_0_0 = true := by
  refine pieces LK 0 0 [] [] Z0_0_0 16 1 (by norm_num) (by decide +kernel) ?_
  intro j hj
  interval_cases j
  · exact k0_0_0_0

theorem a0_0_0 : ∀ t ∈ Z0_0_0.map Prod.fst, Rf 0 0 ↑(t.map vv) :=
  ckl_ok hC hN hG hI LK hk 0 0 [] [] Z0_0_0 (fun h => absurd rfl h) (fun h => absurd rfl h) K0_0_0 _ rfl

theorem Q0_0 : ∀ u ∈ T0_0, ∀ t ∈ u, Rf 0 0 ↑(t.map vv) := by
  intro u hu
  simp only [T0_0, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  · exact a0_0_0

def Z0_1_0 : List (List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)) := [([2,4,6],[],[])]

def T0_1 : List (List (List ℕ)) := [Z0_1_0.map Prod.fst]

theorem k0_1_0_0 : ckl LK 0 1 [] T0_0 ((Z0_1_0.drop (8 * 0)).take 8) = true := by decide +kernel

theorem K0_1_0 : ckl LK 0 1 [] T0_0 Z0_1_0 = true := by
  refine pieces LK 0 1 [] T0_0 Z0_1_0 8 1 (by norm_num) (by decide +kernel) ?_
  intro j hj
  interval_cases j
  · exact k0_1_0_0

theorem a0_1_0 : ∀ t ∈ Z0_1_0.map Prod.fst, Rf 0 1 ↑(t.map vv) :=
  ckl_ok hC hN hG hI LK hk 0 1 [] T0_0 Z0_1_0 (fun h => absurd rfl h) (fun _ => Q0_0) K0_1_0 _ rfl

theorem Q0_1 : ∀ u ∈ T0_1, ∀ t ∈ u, Rf 0 1 ↑(t.map vv) := by
  intro u hu
  simp only [T0_1, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  · exact a0_1_0

def Z1_0_0 : List (List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)) := [([2,4,6],[(145,0,0),(163,1,0),(196,2,0)],[])]

def T1_0 : List (List (List ℕ)) := [Z1_0_0.map Prod.fst]

theorem k1_0_0_0 : ckl LK 1 0 T0_0 [] ((Z1_0_0.drop (2 * 0)).take 2) = true := by decide +kernel

theorem K1_0_0 : ckl LK 1 0 T0_0 [] Z1_0_0 = true := by
  refine pieces LK 1 0 T0_0 [] Z1_0_0 2 1 (by norm_num) (by decide +kernel) ?_
  intro j hj
  interval_cases j
  · exact k1_0_0_0

theorem a1_0_0 : ∀ t ∈ Z1_0_0.map Prod.fst, Rf 1 0 ↑(t.map vv) :=
  ckl_ok hC hN hG hI LK hk 1 0 T0_0 [] Z1_0_0 (fun _ => Q0_0) (fun h => absurd rfl h) K1_0_0 _ rfl

theorem Q1_0 : ∀ u ∈ T1_0, ∀ t ∈ u, Rf 1 0 ↑(t.map vv) := by
  intro u hu
  simp only [T1_0, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  · exact a1_0_0

theorem hall : ∀ c ≤ 1, Rf (1 - c) c ↑(([2, 4, 6] : List ℕ).map vv) := by
  intro c hc
  interval_cases c
  · exact a1_0_0 _ (by decide +kernel)
  · exact a0_1_0 _ (by decide +kernel)

theorem hfun : ∀ p < 7, (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) (fun i => Nat.testBit (PT.getD p 0) i) =
    MM.testBit p := by decide +kernel

end K3

theorem K3 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) t → 4 ≤ t := by
  intro t ht
  by_contra hlt
  obtain ⟨C, h1, h2, h3⟩ := ht
  exact PEqualNP.Outside.L_meta_9255.K3.lower _ PEqualNP.Outside.L_meta_9255.K3.hfun 3 1 (by norm_num) (by decide +kernel) (by decide +kernel)
    [2, 4, 6] (by decide +kernel) PEqualNP.Outside.L_meta_9255.K3.hall ⟨C, h1, by omega, h3⟩

def g3 : (Fin 3 → Bool) → Bool := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

def g5 : (Fin (3 + 2) → Bool) → Bool := fun x => g3 (fun i : Fin 3 => x (Fin.castAdd 2 i)) ||
  (x (Fin.natAdd 3 0) && (x (Fin.castAdd 2 2) || x (Fin.natAdd 3 1)))

def g7 : (Fin (5 + 2) → Bool) → Bool := fun x => g5 (fun i : Fin 5 => x (Fin.castAdd 2 i)) ||
  (x (Fin.natAdd 5 0) && (x (Fin.castAdd 2 3) || x (Fin.natAdd 5 1)))

def g9 : (Fin (7 + 2) → Bool) → Bool := fun x => g7 (fun i : Fin 7 => x (Fin.castAdd 2 i)) ||
  (x (Fin.natAdd 7 0) && (x (Fin.castAdd 2 5) || x (Fin.natAdd 7 1)))

theorem same : ∀ y : Fin 9 → Bool, (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8)) (fun i => (List.ofFn y).getD ([3, 7, 0, 6, 4, 8, 1, 5, 2].getD i 0) false) =
    g9 y := by decide +kernel

end PEqualNP.Outside.L_meta_9255

theorem PEqualNP.Outside.L_meta_9255 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8)) t → 13 ≤ t := by
  intro t h
  by_contra hlt
  have h1 := PEqualNP.Outside.L_meta_9255.Ren.sub 9 9 1000 (fun i => [3, 7, 0, 6, 4, 8, 1, 5, 2].getD i 0) (by decide) _ t (by omega) h
  have e : (fun y : Fin 9 → Bool => (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8)) (fun i => (List.ofFn y).getD ((fun i : ℕ => [3, 7, 0, 6, 4, 8, 1, 5, 2].getD i 0) i) false)) = PEqualNP.Outside.L_meta_9255.g9 :=
    funext PEqualNP.Outside.L_meta_9255.same
  rw [e] at h1
  obtain ⟨s1, a1, c1⟩ := PEqualNP.Outside.L_meta_9255.Path.pathExtension 7 t PEqualNP.Outside.L_meta_9255.g7 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) h1
  obtain ⟨s2, a2, c2⟩ := PEqualNP.Outside.L_meta_9255.Path.pathExtension 5 s1 PEqualNP.Outside.L_meta_9255.g5 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) c1
  obtain ⟨s3, a3, c3⟩ := PEqualNP.Outside.L_meta_9255.Path.pathExtension 3 s2 PEqualNP.Outside.L_meta_9255.g3 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) c2
  have := PEqualNP.Outside.L_meta_9255.K3 s3 c3
  omega
