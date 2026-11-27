import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6524_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev WireVal := Sum Bool ℕ

private def evalVal (w : List Bool) : WireVal → Bool
  | Sum.inl c => c
  | Sum.inr i => w.getD i false

private def circuitStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl circuitStep x := rfl

private lemma foldl_circuitStep_len (gs : List Gate) (w : List Bool) :
    (gs.foldl circuitStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih => rw [List.foldl_cons, ih]; simp [circuitStep]; omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (a d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

private def initEnv (b : Bool) (σ τ : Equiv.Perm (Fin 13)) : List WireVal :=
  List.ofFn (fun i : Fin 13 => Sum.inr (σ.symm i).val) ++
  List.ofFn (fun i : Fin 13 => Sum.inr (13 + (τ.symm i).val)) ++
  [Sum.inl b]

private lemma initEnv_len (b : Bool) (σ τ : Equiv.Perm (Fin 13)) :
    (initEnv b σ τ).length = 27 := by
  simp [initEnv]

private lemma initEnv_wf (b : Bool) (σ τ : Equiv.Perm (Fin 13)) :
    ∀ r ∈ initEnv b σ τ, ∀ w, r = Sum.inr w → w < 26 := by
  intro r hr w hEq
  subst hEq
  simp only [initEnv, List.mem_append, List.mem_ofFn, List.mem_singleton, Set.mem_range] at hr
  rcases hr with (⟨i, hi⟩ | ⟨i, hi⟩) | h
  · injection hi with hi'; rw [← hi']; have := (σ.symm i).isLt; omega
  · injection hi with hi'; rw [← hi']; have := (τ.symm i).isLt; omega
  · cases h

private lemma initEnv_slack (b : Bool) (σ τ : Equiv.Perm (Fin 13)) :
    ∀ i < (initEnv b σ τ).length, i ≠ 26 →
      ∀ c, (initEnv b σ τ).getD i (Sum.inl false) ≠ Sum.inl c := by
  intro i hi hne c hEq
  have hi26 : i < 26 := by rw [initEnv_len] at hi; omega
  have h1 : (initEnv b σ τ).getD i (Sum.inl false) =
      (List.ofFn (fun j : Fin 13 => Sum.inr (σ.symm j).val) ++
        List.ofFn (fun j : Fin 13 => Sum.inr (13 + (τ.symm j).val))).getD i (Sum.inl false) := by
    unfold initEnv
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp; omega)]
  rw [h1] at hEq
  by_cases hi13 : i < 13
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_ofFn] at hEq
    simp [hi13] at hEq
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), List.getElem?_ofFn] at hEq
    simp [show i - 13 < 13 by omega] at hEq

private lemma initEnv_agree (b : Bool) (σ τ : Equiv.Perm (Fin 13)) (x y : Fin 13 → Bool) :
    ∀ i < (initEnv b σ τ).length,
      evalVal (List.ofFn x ++ List.ofFn y) ((initEnv b σ τ).getD i (Sum.inl false)) =
        (List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]).getD i false := by
  intro i hi
  rw [initEnv_len] at hi
  by_cases h26 : i = 26
  · subst h26
    have hL : (initEnv b σ τ).getD 26 (Sum.inl false) = Sum.inl b := by
      unfold initEnv
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    have hR : (List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]).getD 26 false = b := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    rw [hL, hR]; rfl
  · have hi26 : i < 26 := by omega
    by_cases hi13 : i < 13
    · have hL : (initEnv b σ τ).getD i (Sum.inl false) = Sum.inr (σ.symm ⟨i, hi13⟩).val := by
        unfold initEnv
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
            List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
        simp [hi13]
      have hR : (List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]).getD i false =
          x (σ.symm ⟨i, hi13⟩) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
            List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
        simp [hi13]
      rw [hL, hR]
      dsimp only [evalVal]
      have hlt := (σ.symm ⟨i, hi13⟩).isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_ofFn]
      simp [hlt]
    · have hi' : i - 13 < 13 := by omega
      have hL : (initEnv b σ τ).getD i (Sum.inl false) = Sum.inr (13 + (τ.symm ⟨i - 13, hi'⟩).val) := by
        unfold initEnv
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
            List.getElem?_append_right (by simp; omega), List.getElem?_ofFn]
        simp [hi']
      have hR : (List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]).getD i false =
          y (τ.symm ⟨i - 13, hi'⟩) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
            List.getElem?_append_right (by simp; omega), List.getElem?_ofFn]
        simp [hi']
      rw [hL, hR]
      dsimp only [evalVal]
      have hlt := (τ.symm ⟨i - 13, hi'⟩).isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getElem?_ofFn]
      simp [hlt]

private def compileStep (env : List WireVal) (gs : List Gate) (g : Gate) : List WireVal × List Gate :=
  match g.op, g.inputs with
  | GateOp.and, [] => (env ++ [Sum.inl true], gs)
  | GateOp.and, [u] => (env ++ [env.getD u (Sum.inl false)], gs)
  | GateOp.and, [u, v] =>
    match env.getD u (Sum.inl false), env.getD v (Sum.inl false) with
    | Sum.inl false, _ => (env ++ [Sum.inl false], gs)
    | _, Sum.inl false => (env ++ [Sum.inl false], gs)
    | Sum.inl true, rv => (env ++ [rv], gs)
    | ru, Sum.inl true => (env ++ [ru], gs)
    | Sum.inr a, Sum.inr b => (env ++ [Sum.inr (26 + gs.length)], gs ++ [⟨GateOp.and, [a, b]⟩])
  | GateOp.or, [] => (env ++ [Sum.inl false], gs)
  | GateOp.or, [u] => (env ++ [env.getD u (Sum.inl false)], gs)
  | GateOp.or, [u, v] =>
    match env.getD u (Sum.inl false), env.getD v (Sum.inl false) with
    | Sum.inl true, _ => (env ++ [Sum.inl true], gs)
    | _, Sum.inl true => (env ++ [Sum.inl true], gs)
    | Sum.inl false, rv => (env ++ [rv], gs)
    | ru, Sum.inl false => (env ++ [ru], gs)
    | Sum.inr a, Sum.inr b => (env ++ [Sum.inr (26 + gs.length)], gs ++ [⟨GateOp.or, [a, b]⟩])
  | _, _ => (env ++ [Sum.inl false], gs)

private def compileFold : List Gate → List WireVal → List Gate → List WireVal × List Gate
  | [], env, gs => (env, gs)
  | g :: rest, env, gs =>
    let p := compileStep env gs g
    compileFold rest p.1 p.2

private def GatesWf (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ (j : Fin gs.length), ∀ w ∈ (gs.get j).inputs, w < 26 + j.val)

private lemma gatesWf_snoc (gs : List Gate) (g : Gate) (hwf : GatesWf gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (hback : ∀ w ∈ g.inputs, w < 26 + gs.length) :
    GatesWf (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hwf.1 g' h
    · exact ⟨hop, hlen⟩
  · intro j w hw
    have hj : j.val < gs.length + 1 := by simpa using j.isLt
    by_cases hlt : j.val < gs.length
    · have hget : (gs ++ [g]).get j = gs.get ⟨j.val, hlt⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hlt]
      rw [hget] at hw
      exact hwf.2 ⟨j.val, hlt⟩ w hw
    · have heq : j.val = gs.length := by omega
      have hget : (gs ++ [g]).get j = g := by
        simp [List.get_eq_getElem, List.getElem_append_right (by omega : gs.length ≤ j.val), heq]
      rw [hget] at hw
      rw [heq]
      exact hback w hw

private lemma env_getD_wf (env : List WireVal) (n : ℕ)
    (henv : ∀ r ∈ env, ∀ w, r = Sum.inr w → w < n) (i : ℕ) :
    ∀ w, env.getD i (Sum.inl false) = Sum.inr w → w < n := by
  intro w hw
  by_cases hi : i < env.length
  · have hmem : env.getD i (Sum.inl false) ∈ env := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    exact henv _ hmem w hw
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hw
    cases hw

private lemma compileStep_spec (env : List WireVal) (gs : List Gate) (g : Gate)
    (hg_op : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hg_len : g.inputs.length ≤ 2)
    (hg_back : ∀ u ∈ g.inputs, u < env.length)
    (hwf : GatesWf gs)
    (henv : ∀ r ∈ env, ∀ w, r = Sum.inr w → w < 26 + gs.length)
    (hsize : gs.length + 27 ≤ env.length)
    (hslack : ∀ i < env.length, i ≠ 26 → (∃ c, env.getD i (Sum.inl false) = Sum.inl c) → gs.length + 27 < env.length) :
    let p := compileStep env gs g
    p.1.length = env.length + 1 ∧
    p.2.length + 27 ≤ p.1.length ∧
    GatesWf p.2 ∧
    (∀ r ∈ p.1, ∀ w, r = Sum.inr w → w < 26 + p.2.length) ∧
    (∀ i < p.1.length, i ≠ 26 → (∃ c, p.1.getD i (Sum.inl false) = Sum.inl c) → p.2.length + 27 < p.1.length) ∧
    (∀ (inpD wC : List Bool), inpD.length = 26 → wC.length = env.length →
      (∀ i < env.length, evalVal (gs.foldl circuitStep inpD) (env.getD i (Sum.inl false)) = wC.getD i false) →
      ∀ i < p.1.length, evalVal (p.2.foldl circuitStep inpD) (p.1.getD i (Sum.inl false)) = (circuitStep wC g).getD i false) := by
  rcases g with ⟨op, ins⟩
  dsimp only at hg_op hg_len hg_back
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg_op
  have hkeep0 : ∀ (r : WireVal),
      (∀ w, r = Sum.inr w → w < 26 + gs.length) →
      (∀ (inpD wC : List Bool), inpD.length = 26 → wC.length = env.length →
        (∀ i < env.length, evalVal (gs.foldl circuitStep inpD) (env.getD i (Sum.inl false)) = wC.getD i false) →
        evalVal (gs.foldl circuitStep inpD) r = op.eval (ins.map fun j => wC.getD j false)) →
      (env ++ [r]).length = env.length + 1 ∧
      gs.length + 27 ≤ (env ++ [r]).length ∧
      GatesWf gs ∧
      (∀ r' ∈ env ++ [r], ∀ w, r' = Sum.inr w → w < 26 + gs.length) ∧
      (∀ i < (env ++ [r]).length, i ≠ 26 → (∃ c, (env ++ [r]).getD i (Sum.inl false) = Sum.inl c) → gs.length + 27 < (env ++ [r]).length) ∧
      (∀ (inpD wC : List Bool), inpD.length = 26 → wC.length = env.length →
        (∀ i < env.length, evalVal (gs.foldl circuitStep inpD) (env.getD i (Sum.inl false)) = wC.getD i false) →
        ∀ i < (env ++ [r]).length, evalVal (gs.foldl circuitStep inpD) ((env ++ [r]).getD i (Sum.inl false)) =
          (circuitStep wC ⟨op, ins⟩).getD i false) := by
    intro r hr_wf hr_ev
    refine ⟨by simp, by simp; omega, hwf, ?_, ?_, ?_⟩
    · intro r' hr' w hw
      simp only [List.mem_append, List.mem_singleton] at hr'
      rcases hr' with h | rfl
      · exact henv r' h w hw
      · exact hr_wf w hw
    · intro _ _ _ _; simp; omega
    · intro inpD wC hinpD hwC hagree i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < env.length
      · rw [getD_snoc_lt env r (Sum.inl false) i hlt]
        unfold circuitStep
        rw [getD_snoc_lt wC _ false i (by omega)]
        exact hagree i hlt
      · have heq : i = env.length := by omega
        subst heq
        rw [getD_snoc_eq]
        unfold circuitStep
        rw [← hwC, getD_snoc_eq]
        exact hr_ev inpD wC hinpD hwC hagree
  have hkeep1 : ∀ (a b : ℕ), a < 26 + gs.length → b < 26 + gs.length →
      (∀ (inpD wC : List Bool), inpD.length = 26 → wC.length = env.length →
        (∀ i < env.length, evalVal (gs.foldl circuitStep inpD) (env.getD i (Sum.inl false)) = wC.getD i false) →
        op.eval [(gs.foldl circuitStep inpD).getD a false, (gs.foldl circuitStep inpD).getD b false] =
          op.eval (ins.map fun j => wC.getD j false)) →
      (env ++ [Sum.inr (26 + gs.length)]).length = env.length + 1 ∧
      (gs ++ [Gate.mk op [a, b]]).length + 27 ≤ (env ++ [Sum.inr (26 + gs.length)]).length ∧
      GatesWf (gs ++ [Gate.mk op [a, b]]) ∧
      (∀ r' ∈ env ++ [Sum.inr (26 + gs.length)], ∀ w, r' = Sum.inr w → w < 26 + (gs ++ [Gate.mk op [a, b]]).length) ∧
      (∀ i < (env ++ [Sum.inr (26 + gs.length)]).length, i ≠ 26 →
        (∃ c, (env ++ [Sum.inr (26 + gs.length)]).getD i (Sum.inl false) = Sum.inl c) →
        (gs ++ [Gate.mk op [a, b]]).length + 27 < (env ++ [Sum.inr (26 + gs.length)]).length) ∧
      (∀ (inpD wC : List Bool), inpD.length = 26 → wC.length = env.length →
        (∀ i < env.length, evalVal (gs.foldl circuitStep inpD) (env.getD i (Sum.inl false)) = wC.getD i false) →
        ∀ i < (env ++ [Sum.inr (26 + gs.length)]).length,
          evalVal ((gs ++ [Gate.mk op [a, b]]).foldl circuitStep inpD)
            ((env ++ [Sum.inr (26 + gs.length)]).getD i (Sum.inl false)) =
          (circuitStep wC (Gate.mk op ins)).getD i false) := by
    intro a b ha hb hev1
    have hgn : op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hg_op
    have hwf' : GatesWf (gs ++ [Gate.mk op [a, b]]) := by
      apply gatesWf_snoc gs (Gate.mk op [a, b]) hwf hgn (by simp)
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    refine ⟨by simp, by simp; omega, hwf', ?_, ?_, ?_⟩
    · intro r' hr' w hw
      simp only [List.mem_append, List.mem_singleton] at hr'
      rcases hr' with h | rfl
      · have := henv r' h w hw; simp; omega
      · injection hw with hw'; simp; omega
    · intro i hi hne hci
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < env.length
      · rw [getD_snoc_lt env _ (Sum.inl false) i hlt] at hci
        have := hslack i hlt hne hci; omega
      · have heq : i = env.length := by omega
        subst heq; rw [getD_snoc_eq] at hci; rcases hci with ⟨c, hc⟩; cases hc
    · intro inpD wC hinpD hwC hagree i hi
      simp only [List.length_append, List.length_singleton] at hi
      have hfold : (gs ++ [Gate.mk op [a, b]]).foldl circuitStep inpD =
          circuitStep (gs.foldl circuitStep inpD) (Gate.mk op [a, b]) := by
        rw [List.foldl_append]; rfl
      have hlenD : (gs.foldl circuitStep inpD).length = 26 + gs.length := by
        rw [foldl_circuitStep_len, hinpD]
      by_cases hlt : i < env.length
      · rw [getD_snoc_lt env _ (Sum.inl false) i hlt, hfold]
        have hval_eq : evalVal (circuitStep (gs.foldl circuitStep inpD) (Gate.mk op [a, b])) (env.getD i (Sum.inl false)) =
            evalVal (gs.foldl circuitStep inpD) (env.getD i (Sum.inl false)) := by
          cases hr : env.getD i (Sum.inl false) with
          | inl c => rfl
          | inr idx =>
            have hidx : idx < 26 + gs.length := env_getD_wf env (26 + gs.length) henv i idx hr
            dsimp only [evalVal, circuitStep]
            exact getD_snoc_lt _ _ false idx (by omega)
        rw [hval_eq]
        unfold circuitStep
        rw [getD_snoc_lt wC _ false i (by omega)]
        exact hagree i hlt
      · have heq : i = env.length := by omega
        subst heq
        rw [getD_snoc_eq, hfold]
        dsimp only [evalVal, circuitStep]
        rw [← hlenD, getD_snoc_eq, ← hwC, getD_snoc_eq]
        simpa [List.map] using hev1 inpD wC hinpD hwC hagree
  rcases hg_op with rfl | rfl
  · -- GateOp.and
    rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
    · exact hkeep0 (Sum.inl true) (fun _ h => by cases h) (fun _ _ _ _ _ => rfl)
    · have hu : u < env.length := hg_back u (by simp)
      exact hkeep0 (env.getD u (Sum.inl false)) (env_getD_wf env _ henv u) (fun inpD wC _ _ hagree => by
        have h := hagree u hu
        simp [GateOp.eval]; exact h)
    · have hu : u < env.length := hg_back u (by simp)
      have hv : v < env.length := hg_back v (by simp)
      dsimp only [compileStep]
      cases hru : env.getD u (Sum.inl false) with
      | inl cu =>
        cases cu with
        | false =>
          exact hkeep0 (Sum.inl false) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
            have h1 := hagree u hu; rw [hru] at h1; dsimp only [evalVal] at h1
            simp only [GateOp.eval, evalVal, List.map, List.all_cons, List.all_nil, id_eq, ← h1]; rfl)
        | true =>
          cases hrv : env.getD v (Sum.inl false) with
          | inl cv =>
            cases cv with
            | false =>
              exact hkeep0 (Sum.inl false) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
                have h2 := hagree v hv; rw [hrv] at h2; dsimp only [evalVal] at h2
                simp only [GateOp.eval, evalVal, List.map, List.all_cons, List.all_nil, id_eq, ← h2]
                cases wC.getD u false <;> rfl)
            | true =>
              exact hkeep0 (Sum.inl true) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
                have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
                dsimp only [evalVal] at h1 h2
                simp only [GateOp.eval, evalVal, List.map, List.all_cons, List.all_nil, id_eq, ← h1, ← h2]; rfl)
          | inr b =>
            exact hkeep0 (Sum.inr b) (fun w hw => by injection hw with hw'; subst hw'; exact env_getD_wf env _ henv v b hrv)
              (fun inpD wC _ _ hagree => by
                have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
                dsimp only [evalVal] at h1 h2
                simp only [GateOp.eval, evalVal, List.map, List.all_cons, List.all_nil, id_eq, ← h1, ← h2]
                cases (List.foldl circuitStep inpD gs).getD b false <;> rfl)
      | inr a =>
        cases hrv : env.getD v (Sum.inl false) with
        | inl cv =>
          cases cv with
          | false =>
            exact hkeep0 (Sum.inl false) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
              have h2 := hagree v hv; rw [hrv] at h2; dsimp only [evalVal] at h2
              simp only [GateOp.eval, evalVal, List.map, List.all_cons, List.all_nil, id_eq, ← h2]
              cases wC.getD u false <;> rfl)
          | true =>
            exact hkeep0 (Sum.inr a) (fun w hw => by injection hw with hw'; subst hw'; exact env_getD_wf env _ henv u a hru)
              (fun inpD wC _ _ hagree => by
                have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
                dsimp only [evalVal] at h1 h2
                simp only [GateOp.eval, evalVal, List.map, List.all_cons, List.all_nil, id_eq, ← h1, ← h2]
                cases (List.foldl circuitStep inpD gs).getD a false <;> rfl)
        | inr b =>
          exact hkeep1 a b (env_getD_wf env _ henv u a hru) (env_getD_wf env _ henv v b hrv)
            (fun inpD wC _ _ hagree => by
              have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
              dsimp only [evalVal] at h1 h2
              simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, ← h1, ← h2])
    · simp at hg_len
  · -- GateOp.or
    rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
    · exact hkeep0 (Sum.inl false) (fun _ h => by cases h) (fun _ _ _ _ _ => rfl)
    · have hu : u < env.length := hg_back u (by simp)
      exact hkeep0 (env.getD u (Sum.inl false)) (env_getD_wf env _ henv u) (fun inpD wC _ _ hagree => by
        have h := hagree u hu
        simp [GateOp.eval]; exact h)
    · have hu : u < env.length := hg_back u (by simp)
      have hv : v < env.length := hg_back v (by simp)
      dsimp only [compileStep]
      cases hru : env.getD u (Sum.inl false) with
      | inl cu =>
        cases cu with
        | true =>
          exact hkeep0 (Sum.inl true) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
            have h1 := hagree u hu; rw [hru] at h1; dsimp only [evalVal] at h1
            simp only [GateOp.eval, evalVal, List.map, List.any_cons, List.any_nil, id_eq, ← h1]; rfl)
        | false =>
          cases hrv : env.getD v (Sum.inl false) with
          | inl cv =>
            cases cv with
            | true =>
              exact hkeep0 (Sum.inl true) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
                have h2 := hagree v hv; rw [hrv] at h2; dsimp only [evalVal] at h2
                simp only [GateOp.eval, evalVal, List.map, List.any_cons, List.any_nil, id_eq, ← h2]
                cases wC.getD u false <;> rfl)
            | false =>
              exact hkeep0 (Sum.inl false) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
                have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
                dsimp only [evalVal] at h1 h2
                simp only [GateOp.eval, evalVal, List.map, List.any_cons, List.any_nil, id_eq, ← h1, ← h2]; rfl)
          | inr b =>
            exact hkeep0 (Sum.inr b) (fun w hw => by injection hw with hw'; subst hw'; exact env_getD_wf env _ henv v b hrv)
              (fun inpD wC _ _ hagree => by
                have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
                dsimp only [evalVal] at h1 h2
                simp only [GateOp.eval, evalVal, List.map, List.any_cons, List.any_nil, id_eq, ← h1, ← h2]
                cases (List.foldl circuitStep inpD gs).getD b false <;> rfl)
      | inr a =>
        cases hrv : env.getD v (Sum.inl false) with
        | inl cv =>
          cases cv with
          | true =>
            exact hkeep0 (Sum.inl true) (fun _ h => by cases h) (fun inpD wC _ _ hagree => by
              have h2 := hagree v hv; rw [hrv] at h2; dsimp only [evalVal] at h2
              simp only [GateOp.eval, evalVal, List.map, List.any_cons, List.any_nil, id_eq, ← h2]
              cases wC.getD u false <;> rfl)
          | false =>
            exact hkeep0 (Sum.inr a) (fun w hw => by injection hw with hw'; subst hw'; exact env_getD_wf env _ henv u a hru)
              (fun inpD wC _ _ hagree => by
                have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
                dsimp only [evalVal] at h1 h2
                simp only [GateOp.eval, evalVal, List.map, List.any_cons, List.any_nil, id_eq, ← h1, ← h2]
                cases (List.foldl circuitStep inpD gs).getD a false <;> rfl)
        | inr b =>
          exact hkeep1 a b (env_getD_wf env _ henv u a hru) (env_getD_wf env _ henv v b hrv)
            (fun inpD wC _ _ hagree => by
              have h1 := hagree u hu; have h2 := hagree v hv; rw [hru] at h1; rw [hrv] at h2
              dsimp only [evalVal] at h1 h2
              simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, ← h1, ← h2])
    · simp at hg_len

private lemma compileFold_spec (cgs : List Gate) (env : List WireVal) (gs : List Gate)
    (hmono : ∀ g ∈ cgs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hback : ∀ (j : Fin cgs.length), ∀ u ∈ (cgs.get j).inputs, u < env.length + j.val)
    (hwf : GatesWf gs)
    (henv : ∀ r ∈ env, ∀ w, r = Sum.inr w → w < 26 + gs.length)
    (hsize : gs.length + 27 ≤ env.length)
    (hslack : ∀ i < env.length, i ≠ 26 → (∃ c, env.getD i (Sum.inl false) = Sum.inl c) → gs.length + 27 < env.length) :
    let p := compileFold cgs env gs
    p.1.length = env.length + cgs.length ∧
    p.2.length + 27 ≤ p.1.length ∧
    GatesWf p.2 ∧
    (∀ r ∈ p.1, ∀ w, r = Sum.inr w → w < 26 + p.2.length) ∧
    (∀ i < p.1.length, i ≠ 26 → (∃ c, p.1.getD i (Sum.inl false) = Sum.inl c) → p.2.length + 27 < p.1.length) ∧
    (∀ (inpD wC : List Bool), inpD.length = 26 → wC.length = env.length →
      (∀ i < env.length, evalVal (gs.foldl circuitStep inpD) (env.getD i (Sum.inl false)) = wC.getD i false) →
      ∀ i < p.1.length, evalVal (p.2.foldl circuitStep inpD) (p.1.getD i (Sum.inl false)) = (cgs.foldl circuitStep wC).getD i false) := by
  induction cgs generalizing env gs with
  | nil =>
    refine ⟨by simp [compileFold], hsize, hwf, henv, hslack, fun _ _ _ _ hagree i hi => hagree i hi⟩
  | cons g rest ih =>
    have hg := hmono g List.mem_cons_self
    have hg_back : ∀ u ∈ g.inputs, u < env.length := fun u hu => by
      have h := hback ⟨0, by simp⟩ u hu
      simpa using h
    have hst := compileStep_spec env gs g hg.1 hg.2 hg_back hwf henv hsize hslack
    rcases hst with ⟨hlen1, hsize1, hwf1, henv1, hslack1, hev1⟩
    have hrest_mono : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    have hrest_back : ∀ (j : Fin rest.length), ∀ u ∈ (rest.get j).inputs, u < (compileStep env gs g).1.length + j.val := by
      intro j u hu
      have h := hback ⟨j.val + 1, by simp⟩ u hu
      dsimp only at h
      rw [hlen1]; omega
    have hih := ih (compileStep env gs g).1 (compileStep env gs g).2 hrest_mono hrest_back hwf1 henv1 hsize1 hslack1
    rcases hih with ⟨hlen2, hsize2, hwf2, henv2, hslack2, hev2⟩
    refine ⟨by simp [compileFold, hlen2, hlen1]; omega, hsize2, hwf2, henv2, hslack2, ?_⟩
    intro inpD wC hinpD hwC hagree i hi
    have hwC1 : (circuitStep wC g).length = (compileStep env gs g).1.length := by
      simp [circuitStep, hwC, hlen1]
    exact hev2 inpD (circuitStep wC g) hinpD hwC1 (hev1 inpD wC hinpD hwC hagree) i hi

private lemma main_proof (C : Circuit) (b : Bool) (σ τ : Equiv.Perm (Fin 13))
    (hmono : Monotone2 C)
    (hback : ∀ (j : Fin C.gates.length), ∀ u ∈ (C.gates.get j).inputs, u < 27 + j.val)
    (hout : C.output ≠ 26) :
    ∃ (D : Circuit),
      Monotone2 D ∧
      (∀ (j : Fin D.gates.length), ∀ w ∈ (D.gates.get j).inputs, w < 26 + j.val) ∧
      D.size ≤ C.size ∧
      ∀ (x y : Fin 13 → Bool),
        D.eval (List.ofFn x ++ List.ofFn y) =
          C.eval (List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]) := by
  let e0 := initEnv b σ τ
  have he0_len : e0.length = 27 := initEnv_len b σ τ
  have hwf0 : GatesWf [] := ⟨fun _ h => (by cases h), fun j _ _ => absurd j.isLt (by simp)⟩
  have hback0 : ∀ (j : Fin C.gates.length), ∀ u ∈ (C.gates.get j).inputs, u < e0.length + j.val := by
    intro j u hu; rw [he0_len]; exact hback j u hu
  have hslack0 : ∀ i < e0.length, i ≠ 26 → (∃ c, e0.getD i (Sum.inl false) = Sum.inl c) → ([] : List Gate).length + 27 < e0.length := by
    intro i hi hne ⟨c, hc⟩
    exact absurd hc (initEnv_slack b σ τ i hi hne c)
  have hfold := compileFold_spec C.gates e0 [] hmono hback0 hwf0 (initEnv_wf b σ τ) (by simp [he0_len]) hslack0
  generalize compileFold C.gates e0 [] = p at hfold
  rcases hfold with ⟨hlen, hsize, hwf, henv, hslack, hev⟩
  have hp1_len : p.1.length = 27 + C.gates.length := by rw [hlen, he0_len]
  by_cases hlt : C.output < 27 + C.gates.length
  · cases hres : p.1.getD C.output (Sum.inl false) with
    | inr w =>
      refine ⟨⟨p.2, w⟩, hwf.1, hwf.2, by change p.2.length ≤ C.gates.length; omega, ?_⟩
      intro x y
      let inpD := List.ofFn x ++ List.ofFn y
      let inpC := List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]
      have hinpD : inpD.length = 26 := by simp [inpD]
      have hinpC : inpC.length = e0.length := by simp [inpC, he0_len]
      have hag := hev inpD inpC hinpD hinpC (initEnv_agree b σ τ x y) C.output (by omega)
      rw [hres] at hag
      change (p.2.foldl circuitStep inpD).getD w false = (C.gates.foldl circuitStep inpC).getD C.output false
      exact hag
    | inl c =>
      have hlt_len : p.2.length < C.gates.length := by
        have hs := hslack C.output (by omega) hout ⟨c, hres⟩
        omega
      let gc : Gate := ⟨if c then GateOp.and else GateOp.or, []⟩
      have hgc_op : gc.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
        cases c <;> simp [gc]
      have hwf' : GatesWf (p.2 ++ [gc]) := gatesWf_snoc p.2 gc hwf hgc_op (by simp [gc]) (fun _ h => by cases h)
      refine ⟨⟨p.2 ++ [gc], 26 + p.2.length⟩, hwf'.1, hwf'.2, by change (p.2 ++ [gc]).length ≤ C.gates.length; simp; omega, ?_⟩
      intro x y
      let inpD := List.ofFn x ++ List.ofFn y
      let inpC := List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]
      have hinpD : inpD.length = 26 := by simp [inpD]
      have hinpC : inpC.length = e0.length := by simp [inpC, he0_len]
      have hag := hev inpD inpC hinpD hinpC (initEnv_agree b σ τ x y) C.output (by omega)
      rw [hres] at hag
      dsimp only [evalVal] at hag
      change ((p.2 ++ [gc]).foldl circuitStep inpD).getD (26 + p.2.length) false =
        (C.gates.foldl circuitStep inpC).getD C.output false
      rw [List.foldl_append, ← hag]
      have hlenD : (p.2.foldl circuitStep inpD).length = 26 + p.2.length := by
        rw [foldl_circuitStep_len, hinpD]
      change (p.2.foldl circuitStep inpD ++ [gc.op.eval (gc.inputs.map fun i => (p.2.foldl circuitStep inpD).getD i false)]).getD
        (26 + p.2.length) false = c
      rw [← hlenD, getD_snoc_eq]
      cases c <;> rfl
  · refine ⟨⟨p.2, 26 + p.2.length⟩, hwf.1, hwf.2, by change p.2.length ≤ C.gates.length; omega, ?_⟩
    intro x y
    let inpD := List.ofFn x ++ List.ofFn y
    let inpC := List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm) ++ [b]
    change (p.2.foldl circuitStep inpD).getD (26 + p.2.length) false =
      (C.gates.foldl circuitStep inpC).getD C.output false
    have hlenD : (p.2.foldl circuitStep inpD).length = 26 + p.2.length := by
      rw [foldl_circuitStep_len]; simp [inpD]
    have hlenC : (C.gates.foldl circuitStep inpC).length = 27 + C.gates.length := by
      rw [foldl_circuitStep_len]; simp [inpC]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_6524_aux

theorem PEqualNP.Outside.L_meta_6524 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 x4 : Equiv.Perm (Fin (13 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) → x1.output ≠ (26 : ℕ) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x8.gates.length), ∀ x10 ∈ (x8.gates.get x9).inputs, x10 < (26 : ℕ) + ↑x9) ∧ x8.size ≤ x1.size ∧ ∀ (x9 x10 : Fin (13 : ℕ) → Bool), x8.eval (List.ofFn x9 ++ List.ofFn x10) = x1.eval (List.ofFn (x9 ∘ ⇑(Equiv.symm x3)) ++ List.ofFn (x10 ∘ ⇑(Equiv.symm x4)) ++ [x2]) :=
  PEqualNP.Outside.L_meta_6524_aux.main_proof
