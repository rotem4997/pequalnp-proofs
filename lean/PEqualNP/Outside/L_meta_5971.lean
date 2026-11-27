import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5971_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

/-! ## Section 1: U2 Circuit Model and Translation from FanInTwo -/

private abbrev WireRef := Sum Bool (ℕ × Bool)

private structure U2Gate where
  a : ℕ
  b : ℕ
  pa : Bool
  pb : Bool
deriving DecidableEq

private structure U2Circuit where
  gates : List U2Gate
  out : WireRef

private def u2Step (w : List Bool) (g : U2Gate) : List Bool :=
  w ++ [((w.getD g.a false) != g.pa) && ((w.getD g.b false) != g.pb)]

private def u2Wires (gs : List U2Gate) (x : List Bool) : List Bool :=
  gs.foldl u2Step x

private def u2Val (gs : List U2Gate) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
  (u2Wires gs (List.ofFn x)).getD w false

private def refEval (w : List Bool) : WireRef → Bool
  | Sum.inl c => c
  | Sum.inr (i, fl) => (w.getD i false) != fl

private def refWf (bound : ℕ) : WireRef → Prop
  | Sum.inl _ => True
  | Sum.inr (i, _) => i < bound

private def flipRef (fl : Bool) : WireRef → WireRef
  | Sum.inl c => Sum.inl (c != fl)
  | Sum.inr (i, f) => Sum.inr (i, f != fl)

private def u2Eval (D : U2Circuit) (x : Fin 9 → Bool) : Bool :=
  refEval (u2Wires D.gates (List.ofFn x)) D.out

private def U2GatesWf (gs : List U2Gate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].a < 9 + j ∧ gs[j].b < 9 + j

private def U2Wf (D : U2Circuit) : Prop :=
  U2GatesWf D.gates ∧ refWf (9 + D.gates.length) D.out

private lemma refEval_flipRef (w : List Bool) (fl : Bool) (r : WireRef) :
    refEval w (flipRef fl r) = (refEval w r != fl) := by
  rcases r with c | ⟨i, f⟩ <;> cases fl <;> simp [refEval, flipRef]

private lemma refWf_flipRef (bound : ℕ) (fl : Bool) (r : WireRef) :
    refWf bound (flipRef fl r) ↔ refWf bound r := by
  rcases r with c | ⟨i, f⟩ <;> simp [refWf, flipRef]

private lemma refWf_mono {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) {r : WireRef} (hr : refWf b₁ r) :
    refWf b₂ r := by
  rcases r with c | ⟨i, f⟩
  · trivial
  · exact Nat.lt_of_lt_of_le hr h

private lemma u2Wires_nil (x : List Bool) : u2Wires [] x = x := rfl

private lemma u2Wires_cons (g : U2Gate) (gs : List U2Gate) (x : List Bool) :
    u2Wires (g :: gs) x = u2Wires gs (u2Step x g) := rfl

private lemma u2Wires_append (gs₁ gs₂ : List U2Gate) (x : List Bool) :
    u2Wires (gs₁ ++ gs₂) x = u2Wires gs₂ (u2Wires gs₁ x) := by
  simp [u2Wires, List.foldl_append]

private lemma u2Wires_snoc (gs : List U2Gate) (g : U2Gate) (x : List Bool) :
    u2Wires (gs ++ [g]) x = u2Step (u2Wires gs x) g := by
  rw [u2Wires_append]; rfl

private lemma u2Wires_length (gs : List U2Gate) (x : List Bool) :
    (u2Wires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [u2Wires]
  | cons g gs ih =>
    rw [u2Wires_cons, ih]
    simp [u2Step]
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (v d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_snoc_eq' {α : Type*} (l : List α) (v d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [v]).getD i d = v := by
  subst hi
  simp [List.getD_eq_getElem?_getD]

private lemma u2Wires_getD_lt (gs : List U2Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (u2Wires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [u2Wires_cons, ih (u2Step x g) (by simp only [u2Step, List.length_append, List.length_singleton]; omega)]
    exact getD_snoc_lt x _ false i hi

private lemma u2Val_input (gs : List U2Gate) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    u2Val gs x i = x ⟨i, hi⟩ := by
  unfold u2Val
  rw [u2Wires_getD_lt gs (List.ofFn x) i (by rw [List.length_ofFn]; exact hi)]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]

private lemma u2Val_take (gs : List U2Gate) (x : Fin 9 → Bool) (j u : ℕ) (hj : j ≤ gs.length)
    (hu : u < 9 + j) :
    (u2Wires (gs.take j) (List.ofFn x)).getD u false = u2Val gs x u := by
  unfold u2Val
  have hs : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_rhs => rw [hs, u2Wires_append]
  exact (u2Wires_getD_lt _ _ u (by rw [u2Wires_length, List.length_ofFn, List.length_take]; omega)).symm

private lemma u2Val_gate (gs : List U2Gate) (x : Fin 9 → Bool) (j : ℕ) (hj : j < gs.length)
    (ha : gs[j].a < 9 + j) (hb : gs[j].b < 9 + j) :
    u2Val gs x (9 + j) = ((u2Val gs x gs[j].a != gs[j].pa) && (u2Val gs x gs[j].b != gs[j].pb)) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have hlen : (u2Wires (gs.take j) (List.ofFn x)).length = 9 + j := by
    rw [u2Wires_length, List.length_ofFn, List.length_take]
    omega
  rw [← u2Val_take gs x j gs[j].a (by omega) ha, ← u2Val_take gs x j gs[j].b (by omega) hb]
  unfold u2Val
  conv_lhs => rw [hsplit, u2Wires_append, u2Wires_cons]
  rw [u2Wires_getD_lt _ _ (9 + j) (by simp only [u2Step, List.length_append, List.length_singleton]; omega)]
  unfold u2Step
  exact getD_snoc_eq' _ _ false (9 + j) hlen.symm

private lemma refEval_snoc_of_wf (w : List Bool) (v : Bool) (r : WireRef)
    (hr : refWf w.length r) :
    refEval (w ++ [v]) r = refEval w r := by
  rcases r with c | ⟨i, f⟩
  · rfl
  · simp only [refEval]
    rw [getD_snoc_lt w v false i hr]

private lemma refEval_append_of_wf (gs₁ gs₂ : List U2Gate) (x : List Bool) (r : WireRef)
    (hr : refWf (x.length + gs₁.length) r) :
    refEval (u2Wires (gs₁ ++ gs₂) x) r = refEval (u2Wires gs₁ x) r := by
  rcases r with c | ⟨i, f⟩
  · rfl
  · simp only [refEval]
    rw [u2Wires_append, u2Wires_getD_lt gs₂ _ i (by rw [u2Wires_length]; exact hr)]

private def evalAndRef (ea eb : WireRef) (gs : List U2Gate) : WireRef × List U2Gate :=
  match ea, eb with
  | Sum.inl false, _ => (Sum.inl false, gs)
  | _, Sum.inl false => (Sum.inl false, gs)
  | Sum.inl true, eb => (eb, gs)
  | ea, Sum.inl true => (ea, gs)
  | Sum.inr (wa, fa), Sum.inr (wb, fb) =>
    (Sum.inr (9 + gs.length, false), gs ++ [⟨wa, wb, fa, fb⟩])

private lemma evalAndRef_spec (ea eb : WireRef) (gs : List U2Gate)
    (hwa : refWf (9 + gs.length) ea) (hwb : refWf (9 + gs.length) eb) (hwf : U2GatesWf gs) :
    let res := evalAndRef ea eb gs
    U2GatesWf res.2 ∧
    refWf (9 + res.2.length) res.1 ∧
    gs.length ≤ res.2.length ∧
    res.2.length ≤ gs.length + 1 ∧
    (∀ x : List Bool, x.length = 9 →
      (∀ i < 9 + gs.length, (u2Wires res.2 x).getD i false = (u2Wires gs x).getD i false) ∧
      refEval (u2Wires res.2 x) res.1 = (refEval (u2Wires gs x) ea && refEval (u2Wires gs x) eb)) := by
  rcases ea with ca | ⟨wa, fa⟩ <;> rcases eb with cb | ⟨wb, fb⟩
  · cases ca <;> cases cb <;> simp [evalAndRef, hwf, refWf, refEval]
  · cases ca
    · simp [evalAndRef, hwf, refWf, refEval]
    · simp [evalAndRef, hwf, hwb, refEval]
  · cases cb
    · simp [evalAndRef, hwf, refWf, refEval]
    · simp [evalAndRef, hwf, hwa, refEval]
  · simp only [evalAndRef]
    refine ⟨?_, ?_, by simp, by simp, ?_⟩
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · rw [List.getElem_append_left hlt]
        exact hwf j hlt
      · have heq : j = gs.length := by omega
        subst heq
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
        exact ⟨hwa, hwb⟩
    · simp [refWf]
    · intro x hx
      have hlen : (u2Wires gs x).length = 9 + gs.length := by rw [u2Wires_length, hx]
      constructor
      · intro i hi
        rw [u2Wires_snoc, u2Step, getD_snoc_lt _ _ _ i (by omega)]
      · rw [u2Wires_snoc, u2Step]
        simp only [refEval, Bool.bne_false]
        exact getD_snoc_eq' _ _ false (9 + gs.length) hlen.symm

private lemma evalAndRef_noGate (ea eb : WireRef) (gs : List U2Gate)
    (h : (∃ ca, ea = Sum.inl ca) ∨ (∃ cb, eb = Sum.inl cb)) :
    (evalAndRef ea eb gs).2 = gs := by
  rcases h with ⟨ca, rfl⟩ | ⟨cb, rfl⟩
  · cases ca <;> rcases eb with cb | ⟨wb, fb⟩ <;> (try cases cb) <;> rfl
  · cases cb <;> rcases ea with ca | ⟨wa, fa⟩ <;> (try cases ca) <;> rfl

private lemma evalAndRef_const_left (eb : WireRef) (gs : List U2Gate) :
    (evalAndRef (Sum.inl false) eb gs).1 = Sum.inl false := by
  rfl

private lemma evalAndRef_const_right (ea : WireRef) (gs : List U2Gate) :
    (evalAndRef ea (Sum.inl false) gs).1 = Sum.inl false := by
  rcases ea with ca | ⟨wa, fa⟩
  · cases ca <;> rfl
  · rfl

private lemma evalAndRef_const_both (ca cb : Bool) (gs : List U2Gate) :
    ∃ c, (evalAndRef (Sum.inl ca) (Sum.inl cb) gs).1 = Sum.inl c := by
  cases ca <;> cases cb <;> exact ⟨_, rfl⟩

/-! ### Translation from Circuit to U2Circuit -/

private def circuitStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl circuitStep x := rfl

private def toU2Step (env : List WireRef) (gs : List U2Gate) (g : Gate) :
    List WireRef × List U2Gate :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (env ++ [Sum.inl true], gs)
    | u :: _ => (env ++ [flipRef true (env.getD u (Sum.inl false))], gs)
  | GateOp.and =>
    match g.inputs with
    | [] => (env ++ [Sum.inl true], gs)
    | [u] => (env ++ [env.getD u (Sum.inl false)], gs)
    | [u, v] =>
      let res := evalAndRef (env.getD u (Sum.inl false)) (env.getD v (Sum.inl false)) gs
      (env ++ [res.1], res.2)
    | _ => (env ++ [Sum.inl false], gs)
  | GateOp.or =>
    match g.inputs with
    | [] => (env ++ [Sum.inl false], gs)
    | [u] => (env ++ [env.getD u (Sum.inl false)], gs)
    | [u, v] =>
      let res := evalAndRef (flipRef true (env.getD u (Sum.inl false)))
        (flipRef true (env.getD v (Sum.inl false))) gs
      (env ++ [flipRef true res.1], res.2)
    | _ => (env ++ [Sum.inl false], gs)
  | _ => (env ++ [Sum.inl false], gs)

private def initEnv : List WireRef :=
  (List.range 9).map fun i => Sum.inr (i, false)

private def toU2Fold (cgs : List Gate) (env : List WireRef) (gs : List U2Gate) :
    List WireRef × List U2Gate :=
  cgs.foldl (fun st g => toU2Step st.1 st.2 g) (env, gs)

private def toU2 (C : Circuit) : U2Circuit :=
  let res := toU2Fold C.gates initEnv []
  ⟨res.2, res.1.getD C.output (Sum.inl false)⟩

private lemma getD_env_wf (env : List WireRef) (b : ℕ) (henv : ∀ r ∈ env, refWf b r) (u : ℕ) :
    refWf b (env.getD u (Sum.inl false)) := by
  by_cases hu : u < env.length
  · rw [List.getD_eq_getElem _ _ hu]
    exact henv _ (List.getElem_mem hu)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu)]
    trivial

private lemma getD_env_eval (env : List WireRef) (cw uw : List Bool)
    (hlen : env.length = cw.length)
    (hagree : ∀ i < env.length, refEval uw (env.getD i (Sum.inl false)) = cw.getD i false)
    (u : ℕ) :
    refEval uw (env.getD u (Sum.inl false)) = cw.getD u false := by
  by_cases hu : u < env.length
  · exact hagree u hu
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu),
        List.getD_eq_default _ _ (by omega)]
    rfl

private lemma toU2Fold_spec (cgs : List Gate) (env : List WireRef) (gs : List U2Gate)
    (hfan : ∀ g ∈ cgs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hwf : U2GatesWf gs)
    (henv : ∀ r ∈ env, refWf (9 + gs.length) r) :
    let res := toU2Fold cgs env gs
    U2GatesWf res.2 ∧
    (∀ r ∈ res.1, refWf (9 + res.2.length) r) ∧
    res.1.length = env.length + cgs.length ∧
    res.2.length + (cgs.filter fun g => decide (g.op = GateOp.not)).length ≤ gs.length + cgs.length ∧
    (∀ (x : List Bool) (cw : List Bool), x.length = 9 → env.length = cw.length →
      (∀ i < env.length, refEval (u2Wires gs x) (env.getD i (Sum.inl false)) = cw.getD i false) →
      ∀ i < res.1.length,
        refEval (u2Wires res.2 x) (res.1.getD i (Sum.inl false)) = (cgs.foldl circuitStep cw).getD i false) := by
  induction cgs generalizing env gs with
  | nil =>
    refine ⟨hwf, henv, by simp [toU2Fold], by simp [toU2Fold], ?_⟩
    intro x cw _ _ hagree i hi
    exact hagree i hi
  | cons g cgs ih =>
    have hg := hfan g List.mem_cons_self
    have hcgs : ∀ g' ∈ cgs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')
    have hstep :
        let st := toU2Step env gs g
        U2GatesWf st.2 ∧
        (∀ r ∈ st.1, refWf (9 + st.2.length) r) ∧
        st.1.length = env.length + 1 ∧
        st.2.length + (if g.op = GateOp.not then 1 else 0) ≤ gs.length + 1 ∧
        (∀ (x cw : List Bool), x.length = 9 → env.length = cw.length →
          (∀ i < env.length, refEval (u2Wires gs x) (env.getD i (Sum.inl false)) = cw.getD i false) →
          ∀ i < st.1.length,
            refEval (u2Wires st.2 x) (st.1.getD i (Sum.inl false)) = (circuitStep cw g).getD i false) := by
      rcases g with ⟨op, ins⟩
      rcases hg with ⟨hop, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · -- AND
        rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · trivial
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              rfl
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · exact getD_env_wf env _ henv u
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              simpa [GateOp.eval] using getD_env_eval env cw (u2Wires gs x) hlc hagree u
        · have hsp := evalAndRef_spec (env.getD u (Sum.inl false)) (env.getD v (Sum.inl false)) gs
            (getD_env_wf env _ henv u) (getD_env_wf env _ henv v) hwf
          rcases hsp with ⟨hwf', hrf', hle1, hle2, hev⟩
          refine ⟨hwf', ?_, by simp [toU2Step], by dsimp only [toU2Step]; simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]; omega, ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            dsimp only [toU2Step]
            rcases hr with hr | rfl
            · exact refWf_mono (by omega) (henv r hr)
            · exact hrf'
          · intro x cw hx hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            obtain ⟨hpres, hval⟩ := hev x hx
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              have hrw := getD_env_wf env _ henv i
              have hsame : refEval (u2Wires (evalAndRef (env.getD u (Sum.inl false)) (env.getD v (Sum.inl false)) gs).2 x)
                  (env.getD i (Sum.inl false)) =
                  refEval (u2Wires gs x) (env.getD i (Sum.inl false)) := by
                rcases hri : env.getD i (Sum.inl false) with c | ⟨idx, fl⟩
                · rfl
                · rw [hri] at hrw
                  simp only [refEval]
                  rw [hpres idx hrw]
              rw [hsame]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq, hval]
              rw [getD_env_eval env cw (u2Wires gs x) hlc hagree u,
                  getD_env_eval env cw (u2Wires gs x) hlc hagree v]
              simp [GateOp.eval]
        · simp at hlen
      · -- OR
        rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · trivial
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              rfl
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · exact getD_env_wf env _ henv u
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              simpa [GateOp.eval] using getD_env_eval env cw (u2Wires gs x) hlc hagree u
        · have hsp := evalAndRef_spec (flipRef true (env.getD u (Sum.inl false)))
            (flipRef true (env.getD v (Sum.inl false))) gs
            ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv u))
            ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv v)) hwf
          rcases hsp with ⟨hwf', hrf', hle1, hle2, hev⟩
          refine ⟨hwf', ?_, by simp [toU2Step], by dsimp only [toU2Step]; simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]; omega, ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            dsimp only [toU2Step]
            rcases hr with hr | rfl
            · exact refWf_mono (by omega) (henv r hr)
            · exact (refWf_flipRef _ _ _).mpr hrf'
          · intro x cw hx hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            obtain ⟨hpres, hval⟩ := hev x hx
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              have hrw := getD_env_wf env _ henv i
              have hsame : refEval (u2Wires (evalAndRef (flipRef true (env.getD u (Sum.inl false)))
                    (flipRef true (env.getD v (Sum.inl false))) gs).2 x)
                  (env.getD i (Sum.inl false)) =
                  refEval (u2Wires gs x) (env.getD i (Sum.inl false)) := by
                rcases hri : env.getD i (Sum.inl false) with c | ⟨idx, fl⟩
                · rfl
                · rw [hri] at hrw
                  simp only [refEval]
                  rw [hpres idx hrw]
              rw [hsame]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq, refEval_flipRef, hval,
                  refEval_flipRef, refEval_flipRef]
              rw [getD_env_eval env cw (u2Wires gs x) hlc hagree u,
                  getD_env_eval env cw (u2Wires gs x) hlc hagree v]
              cases h1 : cw.getD u false <;> cases h2 : cw.getD v false <;>
                simp [GateOp.eval, List.getD_eq_getElem?_getD] at h1 h2 ⊢ <;> simp [h1, h2]
        · simp at hlen
      · -- NOT
        rcases ins with _ | ⟨u, rest⟩
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · trivial
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              rfl
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · exact (refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv u)
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq, refEval_flipRef]
              rw [getD_env_eval env cw (u2Wires gs x) hlc hagree u]
              simp [GateOp.eval]
    rcases hstep with ⟨hwf1, henv1, hlen1, hsize1, hev1⟩
    have ih' := ih (toU2Step env gs g).1 (toU2Step env gs g).2 hcgs hwf1 henv1
    rcases ih' with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
    refine ⟨hwf2, henv2, ?_, ?_, ?_⟩
    · change (toU2Fold cgs (toU2Step env gs g).1 (toU2Step env gs g).2).1.length = env.length + (g :: cgs).length
      simp only [List.length_cons]; omega
    · change (toU2Fold cgs (toU2Step env gs g).1 (toU2Step env gs g).2).2.length +
        ((g :: cgs).filter fun g => decide (g.op = GateOp.not)).length ≤ gs.length + (g :: cgs).length
      simp only [List.filter_cons, List.length_cons]
      by_cases hnot : g.op = GateOp.not
      · simp only [hnot, decide_true, ↓reduceIte, List.length_cons] at hsize1 ⊢; omega
      · simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte] at hsize1 ⊢; omega
    · intro x cw hx hlc hagree i hi
      simp only [toU2Fold, List.foldl_cons] at hi ⊢
      exact hev2 x (circuitStep cw g) hx (by simp [circuitStep, hlen1, hlc])
        (hev1 x cw hx hlc hagree) i hi

private lemma toU2_spec (C : Circuit) (hfan : FanInTwo C) :
    U2Wf (toU2 C) ∧
    (toU2 C).gates.length ≤ C.size - PEqualNP.NotBracket.notCount C ∧
    (∀ x : Fin 9 → Bool, u2Eval (toU2 C) x = C.eval (List.ofFn x)) := by
  have hinit_wf : ∀ r ∈ initEnv, refWf (9 + ([] : List U2Gate).length) r := by
    intro r hr
    simp only [initEnv, List.mem_map, List.mem_range] at hr
    rcases hr with ⟨i, hi, rfl⟩
    exact hi
  have hsp := toU2Fold_spec C.gates initEnv [] hfan (fun j hj => by simp at hj) hinit_wf
  rcases hsp with ⟨hwf, henv, hlen, hsize, hev⟩
  refine ⟨⟨hwf, getD_env_wf _ _ henv C.output⟩, ?_, ?_⟩
  · change (toU2Fold C.gates initEnv []).2.length ≤ C.gates.length -
      (C.gates.filter fun g => decide (g.op = GateOp.not)).length
    simp only [List.length_nil, Nat.zero_add] at hsize
    omega
  · intro x
    have hagree0 : ∀ i < initEnv.length,
        refEval (u2Wires [] (List.ofFn x)) (initEnv.getD i (Sum.inl false)) =
          (List.ofFn x).getD i false := by
      intro i hi
      simp only [initEnv, List.length_map, List.length_range] at hi
      have hget : initEnv.getD i (Sum.inl false) = Sum.inr (i, false) := by
        simp [initEnv, List.getD_eq_getElem?_getD, hi]
      rw [hget]
      simp [refEval, u2Wires]
    have hcw : (toU2Fold C.gates initEnv []).1.length = (C.wires (List.ofFn x)).length := by
      have hcwl : ∀ (gs : List Gate) (w : List Bool), (gs.foldl circuitStep w).length = w.length + gs.length := by
        intro gs; induction gs with
        | nil => intro w; simp
        | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [circuitStep]; omega
      rw [wires_eq_foldl, hcwl, hlen]
      simp [initEnv]
    unfold u2Eval toU2 Circuit.eval
    rw [wires_eq_foldl]
    exact getD_env_eval _ _ _ hcw (hev (List.ofFn x) (List.ofFn x) (by simp) (by simp [initEnv]) hagree0) C.output

/-! ## Section 2: Minimal U2 Circuits, Deletion, and Constant-Propagation Restriction -/

private def HasU2Size (f : (Fin 9 → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ D : U2Circuit, U2Wf D ∧ D.gates.length ≤ s ∧ ∀ x, u2Eval D x = f x

private def IsMinU2 (f : (Fin 9 → Bool) → Bool) (D : U2Circuit) : Prop :=
  U2Wf D ∧ (∀ x, u2Eval D x = f x) ∧
  ∀ D' : U2Circuit, U2Wf D' → (∀ x, u2Eval D' x = f x) → D.gates.length ≤ D'.gates.length

private lemma exists_minU2 {f : (Fin 9 → Bool) → Bool} {s : ℕ} (h : HasU2Size f s) :
    ∃ D : U2Circuit, IsMinU2 f D ∧ D.gates.length ≤ s := by
  classical
  have hex : ∃ m, HasU2Size f m := ⟨s, h⟩
  let m := Nat.find hex
  have hm : HasU2Size f m := Nat.find_spec hex
  have hle : m ≤ s := Nat.find_min' hex h
  rcases hm with ⟨D, hwf, hlen, hev⟩
  refine ⟨D, ⟨hwf, hev, ?_⟩, Nat.le_trans hlen hle⟩
  intro D' hwf' hev'
  have hmle : m ≤ D'.gates.length := Nat.find_min' hex ⟨D', hwf', Nat.le_refl _, hev'⟩
  omega

/-- Generic single-pass U2 gate compilation/restriction/deletion engine. -/
private def passStep (env : List WireRef) (gs : List U2Gate) (g : U2Gate) :
    List WireRef × List U2Gate :=
  let ea := flipRef g.pa (env.getD g.a (Sum.inl false))
  let eb := flipRef g.pb (env.getD g.b (Sum.inl false))
  let res := evalAndRef ea eb gs
  (env ++ [res.1], res.2)

private def passFold (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate) :
    List WireRef × List U2Gate :=
  cgs.foldl (fun st g => passStep st.1 st.2 g) (env, gs)

private lemma passFold_spec (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate)
    (hwf : U2GatesWf gs)
    (henv : ∀ r ∈ env, refWf (9 + gs.length) r) :
    let res := passFold cgs env gs
    U2GatesWf res.2 ∧
    (∀ r ∈ res.1, refWf (9 + res.2.length) r) ∧
    res.1.length = env.length + cgs.length ∧
    res.2.length ≤ gs.length + cgs.length ∧
    (∀ (x y : List Bool), x.length = 9 → env.length = y.length →
      (∀ i < env.length, refEval (u2Wires gs x) (env.getD i (Sum.inl false)) = y.getD i false) →
      ∀ i < res.1.length,
        refEval (u2Wires res.2 x) (res.1.getD i (Sum.inl false)) = (u2Wires cgs y).getD i false) := by
  induction cgs generalizing env gs with
  | nil =>
    refine ⟨hwf, henv, by simp [passFold], by simp [passFold], ?_⟩
    intro x y _ _ hagree i hi
    exact hagree i hi
  | cons g cgs ih =>
    have hsp := evalAndRef_spec (flipRef g.pa (env.getD g.a (Sum.inl false)))
      (flipRef g.pb (env.getD g.b (Sum.inl false))) gs
      ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv g.a))
      ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv g.b)) hwf
    rcases hsp with ⟨hwf1, hrf1, hle1, hle2, hev1⟩
    have hst1 : (passStep env gs g).1.length = env.length + 1 := by simp [passStep]
    have hst2_ge : gs.length ≤ (passStep env gs g).2.length := hle1
    have hst2_le : (passStep env gs g).2.length ≤ gs.length + 1 := hle2
    have henv1 : ∀ r ∈ (passStep env gs g).1, refWf (9 + (passStep env gs g).2.length) r := by
      intro r hr
      simp only [passStep, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact refWf_mono (by omega) (henv r hr)
      · exact hrf1
    have ih' := ih (passStep env gs g).1 (passStep env gs g).2 hwf1 henv1
    rcases ih' with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
    refine ⟨hwf2, henv2, ?_, ?_, ?_⟩
    · change (passFold cgs (passStep env gs g).1 (passStep env gs g).2).1.length = env.length + (g :: cgs).length
      simp only [List.length_cons]; omega
    · change (passFold cgs (passStep env gs g).1 (passStep env gs g).2).2.length ≤ gs.length + (g :: cgs).length
      simp only [List.length_cons]; omega
    · intro x y hx hly hagree i hi
      simp only [passFold, List.foldl_cons, u2Wires_cons] at hi ⊢
      apply hev2 x (u2Step y g) hx (by simp [passStep, u2Step, hly])
      · intro k hk
        simp only [passStep, List.length_append, List.length_singleton] at hk
        simp only [passStep, u2Step]
        obtain ⟨hpres, hval⟩ := hev1 x hx
        by_cases hlt : k < env.length
        · rw [getD_snoc_lt _ _ _ k hlt, getD_snoc_lt _ _ _ k (by omega)]
          have hrw := getD_env_wf env _ henv k
          have hsame : refEval (u2Wires (evalAndRef (flipRef g.pa (env.getD g.a (Sum.inl false)))
                (flipRef g.pb (env.getD g.b (Sum.inl false))) gs).2 x)
              (env.getD k (Sum.inl false)) =
              refEval (u2Wires gs x) (env.getD k (Sum.inl false)) := by
            rcases hrk : env.getD k (Sum.inl false) with c | ⟨idx, fl⟩
            · rfl
            · rw [hrk] at hrw
              simp only [refEval]
              rw [hpres idx hrw]
          rw [hsame]
          exact hagree k hlt
        · have heq : k = env.length := by omega
          subst heq
          rw [getD_snoc_eq, hly, getD_snoc_eq, hval, refEval_flipRef, refEval_flipRef]
          rw [getD_env_eval env y (u2Wires gs x) hly hagree g.a,
              getD_env_eval env y (u2Wires gs x) hly hagree g.b]
      · exact hi

/-- Delete gate `j` by substituting `repl` (valid at `< 9 + j`) for wire `9 + j`. -/
private def deleteGateAt (D : U2Circuit) (j : ℕ) (repl : WireRef) : U2Circuit :=
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  let env0 : List WireRef := ((List.range (9 + j)).map fun i => Sum.inr (i, false)) ++ [repl]
  let res := passFold post env0 pre
  let out' := match D.out with
    | Sum.inl c => Sum.inl c
    | Sum.inr (w, fl) => flipRef fl (res.1.getD w (Sum.inl false))
  ⟨res.2, out'⟩

private lemma deleteGateAt_spec (D : U2Circuit) (hD : U2Wf D) (j : ℕ) (hj : j < D.gates.length)
    (repl : WireRef) (hrepl_wf : refWf (9 + j) repl)
    (hrepl_eq : ∀ x : Fin 9 → Bool,
      refEval (u2Wires (D.gates.take j) (List.ofFn x)) repl = u2Val D.gates x (9 + j)) :
    U2Wf (deleteGateAt D j repl) ∧
    (deleteGateAt D j repl).gates.length ≤ D.gates.length - 1 ∧
    ∀ x : Fin 9 → Bool, u2Eval (deleteGateAt D j repl) x = u2Eval D x := by
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hpost_len : post.length = D.gates.length - (j + 1) := by simp [post]
  have hpre_wf : U2GatesWf pre := by
    intro k hk
    have hk' : k < j := by omega
    have hkl : k < D.gates.length := by omega
    have := hD.1 k hkl
    simpa [pre, List.getElem_take] using this
  let env0 : List WireRef := ((List.range (9 + j)).map fun i => Sum.inr (i, false)) ++ [repl]
  have henv0_wf : ∀ r ∈ env0, refWf (9 + pre.length) r := by
    intro r hr
    simp only [env0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    rcases hr with ⟨i, hi, rfl⟩ | rfl
    · simp only [refWf]; omega
    · rw [hpre_len]; exact hrepl_wf
  have hsp := passFold_spec post env0 pre hpre_wf henv0_wf
  rcases hsp with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
  refine ⟨⟨hwf2, ?_⟩, ?_, ?_⟩
  · dsimp only [deleteGateAt]
    rcases D.out with c | ⟨w, fl⟩
    · trivial
    · exact (refWf_flipRef _ _ _).mpr (getD_env_wf _ _ henv2 w)
  · change (passFold post env0 pre).2.length ≤ D.gates.length - 1; omega
  · intro x
    have hsplit : D.gates = pre ++ D.gates[j] :: post := by
      simp only [pre, post]
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    let y0 := u2Wires (pre ++ [D.gates[j]]) (List.ofFn x)
    have hy0_len : y0.length = 9 + j + 1 := by
      simp only [y0, u2Wires_length, List.length_ofFn, List.length_append, List.length_singleton, hpre_len]
      omega
    have henv0_len : env0.length = y0.length := by
      simp [env0, hy0_len]
    have hagree0 : ∀ i < env0.length,
        refEval (u2Wires pre (List.ofFn x)) (env0.getD i (Sum.inl false)) = y0.getD i false := by
      intro i hi
      simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton] at hi
      by_cases hlt : i < 9 + j
      · have hget : env0.getD i (Sum.inl false) = Sum.inr (i, false) := by
          simp only [env0]
          rw [getD_snoc_lt _ _ _ i (by simp; exact hlt)]
          simp [List.getD_eq_getElem?_getD, hlt]
        rw [hget]
        simp only [refEval, Bool.bne_false, y0, u2Wires_snoc, u2Step]
        rw [getD_snoc_lt _ _ _ i (by rw [u2Wires_length, List.length_ofFn, hpre_len]; exact hlt)]
      · have heq : i = 9 + j := by omega
        subst heq
        have hget : env0.getD (9 + j) (Sum.inl false) = repl := by
          exact getD_snoc_eq' _ repl (Sum.inl false) (9 + j) (by simp)
        rw [hget, hrepl_eq x]
        unfold u2Val
        conv_lhs => rw [hsplit, u2Wires_append, u2Wires_cons]
        rw [u2Wires_getD_lt post _ (9 + j) (by simp only [u2Step, u2Wires_length, List.length_ofFn, hpre_len, List.length_append, List.length_singleton]; omega)]
        simp only [y0, u2Wires_snoc]
    have hfull : u2Wires post y0 = u2Wires D.gates (List.ofFn x) := by
      conv_rhs => rw [hsplit]
      rw [u2Wires_append, u2Wires_cons]
      simp only [y0, u2Wires_snoc]
    have hev_all := hev2 (List.ofFn x) y0 (by simp) henv0_len hagree0
    rw [hfull] at hev_all
    dsimp only [u2Eval, deleteGateAt]
    rcases hout : D.out with c | ⟨w, fl⟩
    · rfl
    · rw [refEval_flipRef]
      have hw : w < 9 + D.gates.length := by
        have := hD.2; rw [hout] at this; exact this
      have hw' : w < (passFold post env0 pre).1.length := by
        rw [hlen2]; simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
      rw [hev_all w hw']
      rfl

/-- Delete a dead gate `j` (not read by any gate `k > j` and not `D.out`). -/
private lemma deleteDeadGate (D : U2Circuit) (hD : U2Wf D) (j : ℕ) (hj : j < D.gates.length)
    (hout : ∀ fl, D.out ≠ Sum.inr (9 + j, fl))
    (hdead : ∀ k (hk : k < D.gates.length), j < k → D.gates[k].a ≠ 9 + j ∧ D.gates[k].b ≠ 9 + j) :
    U2Wf (deleteGateAt D j (Sum.inl false)) ∧
    (deleteGateAt D j (Sum.inl false)).gates.length ≤ D.gates.length - 1 ∧
    ∀ x : Fin 9 → Bool, u2Eval (deleteGateAt D j (Sum.inl false)) x = u2Eval D x := by
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hpost_len : post.length = D.gates.length - (j + 1) := by simp [post]
  have hpre_wf : U2GatesWf pre := by
    intro k hk
    have hk' : k < D.gates.length := by omega
    simpa [pre, List.getElem_take] using hD.1 k hk'
  let env0 : List WireRef := ((List.range (9 + j)).map fun i => Sum.inr (i, false)) ++ [Sum.inl false]
  have henv0_wf : ∀ r ∈ env0, refWf (9 + pre.length) r := by
    intro r hr
    simp only [env0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    rcases hr with ⟨i, hi, rfl⟩ | rfl
    · simp only [refWf]; omega
    · trivial
  have hsp := passFold_spec post env0 pre hpre_wf henv0_wf
  rcases hsp with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
  refine ⟨⟨hwf2, ?_⟩, ?_, ?_⟩
  · dsimp only [deleteGateAt]
    rcases D.out with c | ⟨w, fl⟩
    · trivial
    · exact (refWf_flipRef _ _ _).mpr (getD_env_wf _ _ henv2 w)
  · change (passFold post env0 pre).2.length ≤ D.gates.length - 1; omega
  · intro x
    let wpre := u2Wires pre (List.ofFn x)
    let y1 := wpre ++ [false]
    let y2 := u2Step wpre D.gates[j]
    have hwpre_len : wpre.length = 9 + j := by simp [wpre, u2Wires_length, hpre_len]
    have hsplit : D.gates = pre ++ D.gates[j] :: post := by
      simp only [pre, post]; rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hagree_post : ∀ (gs : List U2Gate) (w₁ w₂ : List Bool),
        w₁.length = w₂.length →
        (∀ g ∈ gs, g.a ≠ 9 + j ∧ g.b ≠ 9 + j) →
        (∀ i, i ≠ 9 + j → w₁.getD i false = w₂.getD i false) →
        ∀ i, i ≠ 9 + j → (u2Wires gs w₁).getD i false = (u2Wires gs w₂).getD i false := by
      intro gs
      induction gs with
      | nil => intro w₁ w₂ _ _ h i hi; exact h i hi
      | cons g gs ih =>
        intro w₁ w₂ hl hno h
        have hg := hno g List.mem_cons_self
        have hstep_eq : ((w₁.getD g.a false != g.pa) && (w₁.getD g.b false != g.pb)) =
            ((w₂.getD g.a false != g.pa) && (w₂.getD g.b false != g.pb)) := by
          rw [h g.a hg.1, h g.b hg.2]
        rw [u2Wires_cons, u2Wires_cons]
        apply ih (u2Step w₁ g) (u2Step w₂ g) (by simp [u2Step, hl])
          (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
        intro i hi
        by_cases hlt : i < w₁.length
        · simp only [u2Step]
          rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
          exact h i hi
        · by_cases heq : i = w₁.length
          · subst heq
            simp only [u2Step]
            rw [getD_snoc_eq, hl, getD_snoc_eq, hstep_eq]
          · simp only [u2Step]
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hno_post : ∀ g ∈ post, g.a ≠ 9 + j ∧ g.b ≠ 9 + j := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
      have hlt : j + 1 + t < D.gates.length := by simp [post] at ht; omega
      have := hdead (j + 1 + t) hlt (by omega)
      simpa [post, List.getElem_drop] using this
    have hy12 : ∀ i, i ≠ 9 + j → (u2Wires post y1).getD i false = (u2Wires post y2).getD i false := by
      apply hagree_post post y1 y2 (by simp [y1, y2, u2Step]) hno_post
      intro i hi
      by_cases hlt : i < wpre.length
      · simp only [y1, y2, u2Step]
        rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i hlt]
      · simp only [y1, y2, u2Step]
        have hgt : wpre.length + 1 ≤ i := by omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hagree0 : ∀ i < env0.length,
        refEval wpre (env0.getD i (Sum.inl false)) = y1.getD i false := by
      intro i hi
      simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton] at hi
      by_cases hlt : i < 9 + j
      · have hget : env0.getD i (Sum.inl false) = Sum.inr (i, false) := by
          simp only [env0]; rw [getD_snoc_lt _ _ _ i (by simp; exact hlt)]
          simp [List.getD_eq_getElem?_getD, hlt]
        rw [hget]
        simp only [refEval, Bool.bne_false, y1]
        rw [getD_snoc_lt _ _ _ i (by omega)]
      · have heq : i = 9 + j := by omega
        subst heq
        have hget : env0.getD (9 + j) (Sum.inl false) = Sum.inl false :=
          getD_snoc_eq' _ (Sum.inl false) (Sum.inl false) (9 + j) (by simp)
        rw [hget]
        simp only [refEval, y1]
        exact (getD_snoc_eq' wpre false false (9 + j) hwpre_len.symm).symm
    have hev_all := hev2 (List.ofFn x) y1 (by simp) (by simp [env0, y1, hwpre_len]) hagree0
    have hfull2 : u2Wires post y2 = u2Wires D.gates (List.ofFn x) := by
      conv_rhs => rw [hsplit]
      rw [u2Wires_append, u2Wires_cons]
    dsimp only [u2Eval, deleteGateAt]
    rcases hout_eq : D.out with c | ⟨w, fl⟩
    · rfl
    · rw [refEval_flipRef]
      have hw : w < 9 + D.gates.length := by
        have := hD.2; rw [hout_eq] at this; exact this
      have hw' : w < (passFold post env0 pre).1.length := by
        rw [hlen2]; simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
      have hwne : w ≠ 9 + j := fun heq => hout fl (by rw [hout_eq, heq])
      rw [hev_all w hw', hy12 w hwne, hfull2]
      rfl

/-! ### Minimality Corollaries -/

private lemma min_has_reader_or_out {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (j : ℕ) (hj : j < D.gates.length) :
    (∃ fl, D.out = Sum.inr (9 + j, fl)) ∨
    ∃ k, ∃ (hk : k < D.gates.length), j < k ∧ (D.gates[k].a = 9 + j ∨ D.gates[k].b = 9 + j) := by
  by_contra hno
  push Not at hno
  obtain ⟨hwf', hlen', hev'⟩ := deleteDeadGate D hmin.1 j hj hno.1 (fun k hk hjk => hno.2 k hk hjk)
  have hbad := hmin.2.2 _ hwf' (fun x => (hev' x).trans (hmin.2.1 x))
  omega

private lemma min_no_self {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (j : ℕ) (hj : j < D.gates.length) :
    D.gates[j].a ≠ D.gates[j].b := by
  intro heq
  have ha := (hmin.1.1 j hj).1
  have hb := (hmin.1.1 j hj).2
  by_cases hpol : D.gates[j].pa = D.gates[j].pb
  · let repl : WireRef := Sum.inr (D.gates[j].a, D.gates[j].pa)
    have hsp := deleteGateAt_spec D hmin.1 j hj repl ha (fun x => by
      rw [u2Val_gate D.gates x j hj ha hb, ← heq, ← hpol, Bool.and_self]
      simp only [repl, refEval]
      rw [u2Val_take D.gates x j D.gates[j].a (by omega) ha])
    have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
    omega
  · let repl : WireRef := Sum.inl false
    have hsp := deleteGateAt_spec D hmin.1 j hj repl trivial (fun x => by
      rw [u2Val_gate D.gates x j hj ha hb, ← heq]
      cases u2Val D.gates x D.gates[j].a <;> cases hp1 : D.gates[j].pa <;> cases hp2 : D.gates[j].pb <;>
        simp_all [repl, refEval])
    have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
    omega

/-- In-place replacement of gate `j` by an equivalent gate `g'`. -/
private def replaceGateAt (D : U2Circuit) (j : ℕ) (g' : U2Gate) : U2Circuit :=
  ⟨D.gates.set j g', D.out⟩

private lemma list_set_split {α : Type*} (l : List α) (j : ℕ) (v : α) (hj : j < l.length) :
    l.set j v = l.take j ++ v :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih j (by simpa using hj)

private lemma replaceGateAt_spec (D : U2Circuit) (hD : U2Wf D) (j : ℕ) (hj : j < D.gates.length)
    (g' : U2Gate) (ha' : g'.a < 9 + j) (hb' : g'.b < 9 + j)
    (heq : ∀ x : Fin 9 → Bool,
      ((u2Val D.gates x g'.a != g'.pa) && (u2Val D.gates x g'.b != g'.pb)) = u2Val D.gates x (9 + j)) :
    U2Wf (replaceGateAt D j g') ∧
    (replaceGateAt D j g').gates.length = D.gates.length ∧
    ∀ x : Fin 9 → Bool, u2Eval (replaceGateAt D j g') x = u2Eval D x := by
  have hlen : (D.gates.set j g').length = D.gates.length := List.length_set
  have hwf : U2Wf (replaceGateAt D j g') := by
    refine ⟨?_, ?_⟩
    · intro k hk
      have hk' : k < D.gates.length := by rwa [replaceGateAt, hlen] at hk
      by_cases hkj : k = j
      · subst hkj
        simp [replaceGateAt, List.getElem_set_self, ha', hb']
      · simp only [replaceGateAt, List.getElem_set_ne (Ne.symm hkj)]
        exact hD.1 k hk'
    · simpa [replaceGateAt, hlen] using hD.2
  refine ⟨hwf, hlen, fun x => ?_⟩
  have hwires : u2Wires (D.gates.set j g') (List.ofFn x) = u2Wires D.gates (List.ofFn x) := by
    have hs1 : D.gates.set j g' = D.gates.take j ++ g' :: D.gates.drop (j + 1) :=
      list_set_split D.gates j g' hj
    have hs2 : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    rw [hs1, u2Wires_append, u2Wires_cons]
    conv_rhs => rw [hs2, u2Wires_append, u2Wires_cons]
    congr 1
    let w0 := u2Wires (D.gates.take j) (List.ofFn x)
    have hpre : ∀ u < 9 + j, w0.getD u false = u2Val D.gates x u :=
      fun u hu => u2Val_take D.gates x j u (by omega) hu
    have hg_eval : ((w0.getD g'.a false != g'.pa) && (w0.getD g'.b false != g'.pb)) =
        ((w0.getD D.gates[j].a false != D.gates[j].pa) && (w0.getD D.gates[j].b false != D.gates[j].pb)) := by
      rw [hpre g'.a ha', hpre g'.b hb', heq x,
          u2Val_gate D.gates x j hj (hD.1 j hj).1 (hD.1 j hj).2,
          hpre D.gates[j].a (hD.1 j hj).1, hpre D.gates[j].b (hD.1 j hj).2]
    simp only [u2Step, w0] at hg_eval ⊢
    rw [hg_eval]
  unfold u2Eval replaceGateAt
  rw [hwires]

/-- Helper: gate 0 reads `(v, p0)` and `(u, q0)`, and gate `j1 > 0` reads `(v, p1)` and `(9, q1)`. -/
private lemma min_gate0_interact {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v u : ℕ) (p0 q0 : Bool) (hv : v < 9) (hu : u < 9)
    (hg0 : ∀ x : Fin 9 → Bool, u2Val D.gates x 9 = ((u2Val D.gates x v != p0) && (u2Val D.gates x u != q0)))
    (j1 : ℕ) (hj1 : j1 < D.gates.length) (hj1_pos : 0 < j1)
    (p1 q1 : Bool)
    (hg1 : ∀ x : Fin 9 → Bool, u2Val D.gates x (9 + j1) = ((u2Val D.gates x v != p1) && (u2Val D.gates x 9 != q1))) :
    p1 = p0 ∧ q1 = true ∧
    ((∃ fl, D.out = Sum.inr (9, fl)) ∨
      ∃ k, ∃ (hk : k < D.gates.length), 0 < k ∧ k ≠ j1 ∧ (D.gates[k].a = 9 ∨ D.gates[k].b = 9)) := by
  by_cases hp : p1 = p0
  · subst hp
    cases q1 with
    | false =>
      have hrepl : ∀ x : Fin 9 → Bool,
          refEval (u2Wires (D.gates.take j1) (List.ofFn x)) (Sum.inr (9, false)) = u2Val D.gates x (9 + j1) := by
        intro x
        simp only [refEval, Bool.bne_false]
        rw [u2Val_take D.gates x j1 9 (by omega) (by omega), hg1 x, hg0 x]
        cases (u2Val D.gates x v != p1) <;> cases (u2Val D.gates x u != q0) <;> rfl
      have hsp := deleteGateAt_spec D hmin.1 j1 hj1 (Sum.inr (9, false)) (by simp [refWf]; omega) hrepl
      have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
      omega
    | true =>
      refine ⟨rfl, rfl, ?_⟩
      let g' : U2Gate := ⟨v, u, p1, !q0⟩
      have hrep := replaceGateAt_spec D hmin.1 j1 hj1 g' (by dsimp [g']; omega) (by dsimp [g']; omega) (fun x => by
        dsimp [g']
        rw [hg1 x, hg0 x]
        cases u2Val D.gates x v <;> cases u2Val D.gates x u <;> cases p1 <;> cases q0 <;> rfl)
      have hmin' : IsMinU2 f (replaceGateAt D j1 g') :=
        ⟨hrep.1, fun x => (hrep.2.2 x).trans (hmin.2.1 x),
         fun D' h1 h2 => by rw [hrep.2.1]; exact hmin.2.2 D' h1 h2⟩
      rcases min_has_reader_or_out hmin' 0 (by rw [hrep.2.1]; exact h0) with hout | ⟨k, hk, hk0, hkr⟩
      · exact Or.inl hout
      · have hk' : k < D.gates.length := by rwa [replaceGateAt, List.length_set] at hk
        have hkne : k ≠ j1 := by
          intro heq; subst heq
          simp only [replaceGateAt, List.getElem_set_self, g'] at hkr
          omega
        simp only [replaceGateAt, List.getElem_set_ne (Ne.symm hkne)] at hkr
        exact Or.inr ⟨k, hk', hk0, hkne, hkr⟩
  · cases q1 with
    | false =>
      have hsp := deleteGateAt_spec D hmin.1 j1 hj1 (Sum.inl false) trivial (fun x => by
        rw [hg1 x, hg0 x]
        cases u2Val D.gates x v <;> cases u2Val D.gates x u <;> cases p0 <;> cases p1 <;>
          simp_all [refEval])
      have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
      omega
    | true =>
      have hrepl : ∀ x : Fin 9 → Bool,
          refEval (u2Wires (D.gates.take j1) (List.ofFn x)) (Sum.inr (v, p1)) = u2Val D.gates x (9 + j1) := by
        intro x
        simp only [refEval]
        rw [u2Val_take D.gates x j1 v (by omega) (by omega), hg1 x, hg0 x]
        cases u2Val D.gates x v <;> cases u2Val D.gates x u <;> cases p0 <;> cases p1 <;> simp_all
      have hsp := deleteGateAt_spec D hmin.1 j1 hj1 (Sum.inr (v, p1)) (by simp [refWf]; omega) hrepl
      have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
      omega

/-! ### Constant-Propagation Restriction and Gate Elimination Bounds -/

private def isConstRef : WireRef → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

private lemma isConstRef_flipRef (fl : Bool) (r : WireRef) :
    isConstRef (flipRef fl r) = isConstRef r := by
  rcases r with c | ⟨i, f⟩ <;> rfl

private lemma isConstRef_true_iff (r : WireRef) :
    isConstRef r = true ↔ ∃ c, r = Sum.inl c := by
  rcases r with c | ⟨i, f⟩
  · simp [isConstRef]
  · simp [isConstRef]

private lemma passFold_getD_lt (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate)
    (i : ℕ) (hi : i < env.length) :
    (passFold cgs env gs).1.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
  induction cgs generalizing env gs with
  | nil => rfl
  | cons g cgs ih =>
    change (passFold cgs (passStep env gs g).1 (passStep env gs g).2).1.getD i (Sum.inl false) = _
    rw [ih _ _ (by simp [passStep]; omega)]
    exact getD_snoc_lt env _ (Sum.inl false) i hi

private lemma passFold_count_elim (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate)
    (hcgs_wf : ∀ j (hj : j < cgs.length), cgs[j].a < env.length + j ∧ cgs[j].b < env.length + j) :
    let E := (passFold cgs env gs).1
    (passFold cgs env gs).2.length +
      ((List.finRange cgs.length).filter fun j =>
        isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
        isConstRef (E.getD cgs[j.val].b (Sum.inl false))).length =
      gs.length + cgs.length ∧
    ∀ j (hj : j < cgs.length),
      let ea := flipRef cgs[j].pa (E.getD cgs[j].a (Sum.inl false))
      let eb := flipRef cgs[j].pb (E.getD cgs[j].b (Sum.inl false))
      ((ea = Sum.inl false ∨ eb = Sum.inl false) → E.getD (env.length + j) (Sum.inl false) = Sum.inl false) ∧
      ((isConstRef ea = true ∧ isConstRef eb = true) → isConstRef (E.getD (env.length + j) (Sum.inl false)) = true) := by
  induction cgs generalizing env gs with
  | nil =>
    refine ⟨by simp [passFold], fun j hj => by simp at hj⟩
  | cons g cgs ih =>
    let st := passStep env gs g
    have hst_len : st.1.length = env.length + 1 := by simp [st, passStep]
    have h0_wf := hcgs_wf 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0_wf
    have hga : g.a < env.length := h0_wf.1
    have hgb : g.b < env.length := h0_wf.2
    have hcgs_wf' : ∀ j (hj : j < cgs.length), cgs[j].a < st.1.length + j ∧ cgs[j].b < st.1.length + j := by
      intro j hj
      have h := hcgs_wf (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at h
      omega
    obtain ⟨ih_cnt, ih_gate⟩ := ih st.1 st.2 hcgs_wf'
    let E := (passFold (g :: cgs) env gs).1
    have hE_eq : E = (passFold cgs st.1 st.2).1 := rfl
    have hEa : E.getD g.a (Sum.inl false) = env.getD g.a (Sum.inl false) := by
      rw [hE_eq, passFold_getD_lt cgs st.1 st.2 g.a (by omega)]
      exact getD_snoc_lt env _ (Sum.inl false) g.a hga
    have hEb : E.getD g.b (Sum.inl false) = env.getD g.b (Sum.inl false) := by
      rw [hE_eq, passFold_getD_lt cgs st.1 st.2 g.b (by omega)]
      exact getD_snoc_lt env _ (Sum.inl false) g.b hgb
    have hE0 : E.getD env.length (Sum.inl false) =
        (evalAndRef (flipRef g.pa (env.getD g.a (Sum.inl false)))
          (flipRef g.pb (env.getD g.b (Sum.inl false))) gs).1 := by
      rw [hE_eq, passFold_getD_lt cgs st.1 st.2 env.length (by omega)]
      exact getD_snoc_eq env _ (Sum.inl false)
    have hstep_cnt :
        st.2.length + (if (isConstRef (E.getD g.a (Sum.inl false)) ||
            isConstRef (E.getD g.b (Sum.inl false))) = true then 1 else 0) = gs.length + 1 := by
      rw [hEa, hEb]
      dsimp only [st, passStep]
      rcases ha : env.getD g.a (Sum.inl false) with ca | ⟨wa, fa⟩ <;>
        rcases hb : env.getD g.b (Sum.inl false) with cb | ⟨wb, fb⟩
      · cases ca <;> cases cb <;> cases g.pa <;> cases g.pb <;>
          simp [isConstRef, flipRef, evalAndRef]
      · cases ca <;> cases g.pa <;> simp [isConstRef, flipRef, evalAndRef]
      · cases cb <;> cases g.pb <;> simp [isConstRef, flipRef, evalAndRef]
      · simp [isConstRef, flipRef, evalAndRef]
    constructor
    · have hfin : ((List.finRange (g :: cgs).length).filter fun j =>
          isConstRef (E.getD (g :: cgs)[j.val].a (Sum.inl false)) ||
          isConstRef (E.getD (g :: cgs)[j.val].b (Sum.inl false))).length =
          (if (isConstRef (E.getD g.a (Sum.inl false)) ||
              isConstRef (E.getD g.b (Sum.inl false))) = true then 1 else 0) +
          ((List.finRange cgs.length).filter fun j =>
            isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
            isConstRef (E.getD cgs[j.val].b (Sum.inl false))).length := by
        have hfr : List.finRange (g :: cgs).length =
            ⟨0, Nat.zero_lt_succ _⟩ :: (List.finRange cgs.length).map Fin.succ := List.finRange_succ
        rw [hfr, List.filter_cons]
        have hmap : ((List.finRange cgs.length).map Fin.succ).filter (fun j : Fin (g :: cgs).length =>
              isConstRef (E.getD (g :: cgs)[j.val].a (Sum.inl false)) ||
              isConstRef (E.getD (g :: cgs)[j.val].b (Sum.inl false))) =
            ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
              isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
              isConstRef (E.getD cgs[j.val].b (Sum.inl false))).map Fin.succ := by
          rw [List.filter_map]
          rfl
        rw [hmap]
        dsimp only
        simp only [List.getElem_cons_zero]
        have hif : ∀ b : Bool,
            (if b = true then
              (⟨0, Nat.zero_lt_succ _⟩ : Fin (g :: cgs).length) ::
                ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
                  isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
                  isConstRef (E.getD cgs[j.val].b (Sum.inl false))).map Fin.succ
            else
              ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
                isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
                isConstRef (E.getD cgs[j.val].b (Sum.inl false))).map Fin.succ).length =
            (if b = true then 1 else 0) +
              ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
                isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
                isConstRef (E.getD cgs[j.val].b (Sum.inl false))).length := by
          intro b; cases b
          · simp
          · simp; omega
        exact hif _
      change (passFold cgs st.1 st.2).2.length + _ = gs.length + (g :: cgs).length
      rw [hfin]
      change (passFold cgs st.1 st.2).2.length + ((if (isConstRef ((passFold cgs st.1 st.2).1.getD g.a (Sum.inl false)) ||
          isConstRef ((passFold cgs st.1 st.2).1.getD g.b (Sum.inl false))) = true then 1 else 0) +
          ((List.finRange cgs.length).filter fun j =>
            isConstRef ((passFold cgs st.1 st.2).1.getD cgs[j.val].a (Sum.inl false)) ||
            isConstRef ((passFold cgs st.1 st.2).1.getD cgs[j.val].b (Sum.inl false))).length) =
        gs.length + (g :: cgs).length
      change st.2.length + (if (isConstRef ((passFold cgs st.1 st.2).1.getD g.a (Sum.inl false)) ||
          isConstRef ((passFold cgs st.1 st.2).1.getD g.b (Sum.inl false))) = true then 1 else 0) =
        gs.length + 1 at hstep_cnt
      simp only [List.length_cons]
      omega
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hEa, hEb, hE0]
        constructor
        · intro h
          rcases h with ha | hb
          · rw [ha]; exact evalAndRef_const_left _ _
          · rw [hb]; exact evalAndRef_const_right _ _
        · rintro ⟨ha, hb⟩
          obtain ⟨ca, hca⟩ := (isConstRef_true_iff _).mp ha
          obtain ⟨cb, hcb⟩ := (isConstRef_true_iff _).mp hb
          rw [hca, hcb]
          obtain ⟨c, hc⟩ := evalAndRef_const_both ca cb gs
          rw [hc]; rfl
      | succ j =>
        have hj' : j < cgs.length := by simpa using hj
        have h := ih_gate j hj'
        have hidx : env.length + (j + 1) = st.1.length + j := by omega
        simp only [List.getElem_cons_succ]
        rw [hidx]
        exact h

private def restrictEnv (v : Fin 9) (val : Bool) : List WireRef :=
  (List.range 9).map fun i => if i = v.val then Sum.inl val else Sum.inr (i, false)

private def restrictRun (gs : List U2Gate) (v : Fin 9) (val : Bool) : List WireRef × List U2Gate :=
  passFold gs (restrictEnv v val) []

private def restrictU2 (D : U2Circuit) (v : Fin 9) (val : Bool) : U2Circuit :=
  let res := restrictRun D.gates v val
  let out' := match D.out with
    | Sum.inl c => Sum.inl c
    | Sum.inr (w, fl) => flipRef fl (res.1.getD w (Sum.inl false))
  ⟨res.2, out'⟩

private def elimSet (D : U2Circuit) (v : Fin 9) (val : Bool) : Finset (Fin D.gates.length) :=
  let E := (restrictRun D.gates v val).1
  Finset.univ.filter fun j : Fin D.gates.length =>
    isConstRef (E.getD D.gates[j.val].a (Sum.inl false)) = true ∨
    isConstRef (E.getD D.gates[j.val].b (Sum.inl false)) = true

private lemma restrictU2_spec (D : U2Circuit) (hD : U2Wf D) (v : Fin 9) (val : Bool) :
    let E := (restrictRun D.gates v val).1
    U2Wf (restrictU2 D v val) ∧
    (∀ x : Fin 9 → Bool, u2Eval (restrictU2 D v val) x = u2Eval D (Function.update x v val)) ∧
    (restrictU2 D v val).gates.length + (elimSet D v val).card = D.gates.length ∧
    E.getD v.val (Sum.inl false) = Sum.inl val ∧
    (∀ j (hj : j < D.gates.length),
      let ea := flipRef D.gates[j].pa (E.getD D.gates[j].a (Sum.inl false))
      let eb := flipRef D.gates[j].pb (E.getD D.gates[j].b (Sum.inl false))
      ((ea = Sum.inl false ∨ eb = Sum.inl false) → E.getD (9 + j) (Sum.inl false) = Sum.inl false) ∧
      ((isConstRef ea = true ∧ isConstRef eb = true) → isConstRef (E.getD (9 + j) (Sum.inl false)) = true)) := by
  have henv_len : (restrictEnv v val).length = 9 := by simp [restrictEnv]
  have henv_wf : ∀ r ∈ restrictEnv v val, refWf (9 + ([] : List U2Gate).length) r := by
    intro r hr
    simp only [restrictEnv, List.mem_map, List.mem_range] at hr
    rcases hr with ⟨i, hi, rfl⟩
    by_cases h : i = v.val
    · simp [h, refWf]
    · simp [h, refWf]; omega
  have hsp := passFold_spec D.gates (restrictEnv v val) [] (fun j hj => by simp at hj) henv_wf
  rcases hsp with ⟨hwf2, henv2, hlen2, _, hev2⟩
  have hcnt := passFold_count_elim D.gates (restrictEnv v val) [] (by
    intro j hj; rw [henv_len]; exact hD.1 j hj)
  rcases hcnt with ⟨hsum, hgate⟩
  refine ⟨⟨hwf2, ?_⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [restrictU2]
    rcases D.out with c | ⟨w, fl⟩
    · trivial
    · exact (refWf_flipRef _ _ _).mpr (getD_env_wf _ _ henv2 w)
  · intro x
    have hagree0 : ∀ i < (restrictEnv v val).length,
        refEval (u2Wires [] (List.ofFn x)) ((restrictEnv v val).getD i (Sum.inl false)) =
          (List.ofFn (Function.update x v val)).getD i false := by
      intro i hi
      rw [henv_len] at hi
      have hget : (restrictEnv v val).getD i (Sum.inl false) =
          if i = v.val then Sum.inl val else Sum.inr (i, false) := by
        simp [restrictEnv, List.getD_eq_getElem?_getD, hi]
      rw [hget]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
      by_cases h : i = v.val
      · simp only [h, ↓reduceIte, refEval, Function.update_self]
      · have hfin : (⟨i, hi⟩ : Fin 9) ≠ v := fun heq => h (congrArg Fin.val heq)
        simp only [h, ↓reduceIte, refEval, Bool.bne_false, u2Wires, List.foldl_nil,
          Function.update_of_ne hfin]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
    have hev_all := hev2 (List.ofFn x) (List.ofFn (Function.update x v val)) (by simp)
      (by simp [henv_len]) hagree0
    dsimp only [u2Eval, restrictU2]
    rcases hout : D.out with c | ⟨w, fl⟩
    · rfl
    · rw [refEval_flipRef]
      have hw : w < 9 + D.gates.length := by
        have := hD.2; rw [hout] at this; exact this
      have hw' : w < (restrictRun D.gates v val).1.length := by
        change w < (passFold D.gates (restrictEnv v val) []).1.length
        rw [hlen2, henv_len]; exact hw
      unfold restrictRun
      rw [hev_all w hw']
      rfl
  · change (restrictRun D.gates v val).2.length + (elimSet D v val).card = D.gates.length
    have hcard_eq : (elimSet D v val).card =
        ((List.finRange D.gates.length).filter fun j =>
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].a (Sum.inl false)) ||
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].b (Sum.inl false))).length := by
      have hnodup : ((List.finRange D.gates.length).filter fun j =>
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].a (Sum.inl false)) ||
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].b (Sum.inl false))).Nodup :=
        (List.nodup_finRange _).filter _
      rw [← List.toFinset_card_of_nodup hnodup]
      congr 1
      ext j
      simp [elimSet, Bool.or_eq_true]
    rw [hcard_eq]
    simpa [restrictRun] using hsum
  · unfold restrictRun
    rw [passFold_getD_lt D.gates (restrictEnv v val) [] v.val (by rw [henv_len]; exact v.isLt)]
    simp [restrictEnv, List.getD_eq_getElem?_getD, v.isLt]
  · intro j hj
    have h := hgate j hj
    rw [henv_len] at h
    exact h

private lemma not_out_of_isConst {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hD : U2Wf D) (hev : ∀ x, u2Eval D x = f x) (v : Fin 9) (val : Bool)
    (hnc : ∃ x y : Fin 9 → Bool, f (Function.update x v val) ≠ f (Function.update y v val))
    (j : ℕ) (hconst : isConstRef ((restrictRun D.gates v val).1.getD (9 + j) (Sum.inl false)) = true) :
    ∀ fl, D.out ≠ Sum.inr (9 + j, fl) := by
  intro fl hout
  obtain ⟨c, hc⟩ := (isConstRef_true_iff _).mp hconst
  obtain ⟨hwf', hev', _⟩ := restrictU2_spec D hD v val
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev, ← hev, ← hev' x, ← hev' y]
  unfold u2Eval restrictU2
  rw [hout]
  dsimp only
  rw [hc]
  simp [refEval, flipRef]

private lemma elim_ge_1 {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (v : Fin 9) (val : Bool)
    (j : ℕ) (hj : j < D.gates.length) (hread : D.gates[j].a = v.val ∨ D.gates[j].b = v.val) :
    ∃ s', s' + 1 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v val)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, _⟩ := restrictU2_spec D hmin.1 v val
  have hjmem : (⟨j, hj⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hread with ha | hb
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have hcard : 1 ≤ (elimSet D v val).card := Finset.one_le_card.mpr ⟨⟨j, hj⟩, hjmem⟩
  exact ⟨(restrictU2 D v val).gates.length, by omega,
    restrictU2 D v val, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

private lemma elim_ge_2_ctrl {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (v : Fin 9) (p : Bool)
    (hnc : ∃ x y : Fin 9 → Bool, f (Function.update x v p) ≠ f (Function.update y v p))
    (j : ℕ) (hj : j < D.gates.length)
    (hread : (D.gates[j].a = v.val ∧ D.gates[j].pa = p) ∨ (D.gates[j].b = v.val ∧ D.gates[j].pb = p)) :
    ∃ s', s' + 2 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v p)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, hgate⟩ := restrictU2_spec D hmin.1 v p
  have hEj : (restrictRun D.gates v p).1.getD (9 + j) (Sum.inl false) = Sum.inl false := by
    apply (hgate j hj).1
    rcases hread with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
    · left; rw [ha, hpa, hEv]; cases p <;> rfl
    · right; rw [hb, hpb, hEv]; cases p <;> rfl
  have hnotout := not_out_of_isConst hmin.1 hmin.2.1 v p hnc j (by rw [hEj]; rfl)
  rcases min_has_reader_or_out hmin j hj with ⟨fl, hout⟩ | ⟨k, hk, hjk, hkr⟩
  · exact (hnotout fl hout).elim
  · have hjmem : (⟨j, hj⟩ : Fin D.gates.length) ∈ elimSet D v p := by
      simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hread with ⟨ha, _⟩ | ⟨hb, _⟩
      · left; rw [ha, hEv]; rfl
      · right; rw [hb, hEv]; rfl
    have hkmem : (⟨k, hk⟩ : Fin D.gates.length) ∈ elimSet D v p := by
      simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hkr with ha | hb
      · left; rw [ha, hEj]; rfl
      · right; rw [hb, hEj]; rfl
    have hne : (⟨j, hj⟩ : Fin D.gates.length) ≠ ⟨k, hk⟩ := fun h => by
      have hjk' : j = k := congrArg Fin.val h
      omega
    have hsub : ({⟨j, hj⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v p := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hcard : 2 ≤ (elimSet D v p).card := by
      calc 2 = ({⟨j, hj⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)).card := by
            rw [Finset.card_pair hne]
        _ ≤ (elimSet D v p).card := Finset.card_le_card hsub
    exact ⟨(restrictU2 D v p).gates.length, by omega,
      restrictU2 D v p, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

private lemma elim_ge_2_two {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (v : Fin 9) (val : Bool)
    (j0 j1 : ℕ) (hj0 : j0 < D.gates.length) (hj1 : j1 < D.gates.length) (hne : j0 ≠ j1)
    (hr0 : D.gates[j0].a = v.val ∨ D.gates[j0].b = v.val)
    (hr1 : D.gates[j1].a = v.val ∨ D.gates[j1].b = v.val) :
    ∃ s', s' + 2 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v val)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, _⟩ := restrictU2_spec D hmin.1 v val
  have hmem : ∀ (j : ℕ) (hj : j < D.gates.length),
      (D.gates[j].a = v.val ∨ D.gates[j].b = v.val) →
      (⟨j, hj⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    intro j hj hr
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr with ha | hb
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have hsub : ({⟨j0, hj0⟩, ⟨j1, hj1⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v val := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem j0 hj0 hr0
    · exact hmem j1 hj1 hr1
  have hcard : 2 ≤ (elimSet D v val).card := by
    calc 2 = ({⟨j0, hj0⟩, ⟨j1, hj1⟩} : Finset (Fin D.gates.length)).card := by
          rw [Finset.card_pair (fun h => hne (congrArg Fin.val h))]
      _ ≤ (elimSet D v val).card := Finset.card_le_card hsub
  exact ⟨(restrictU2 D v val).gates.length, by omega,
    restrictU2 D v val, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

/-- Helper to extract the canonical form of gate 0 reading `(v, p0)` and `(u, q0)`. -/
private lemma gate0_eval_form {D : U2Circuit} (hD : U2Wf D) (h0 : 0 < D.gates.length)
    (v : ℕ) (p0 : Bool)
    (hr : (D.gates[0].a = v ∧ D.gates[0].pa = p0) ∨ (D.gates[0].b = v ∧ D.gates[0].pb = p0)) :
    ∃ u q0, u < 9 ∧
      ∀ x : Fin 9 → Bool, u2Val D.gates x 9 = ((u2Val D.gates x v != p0) && (u2Val D.gates x u != q0)) := by
  have ha0 := (hD.1 0 h0).1
  have hb0 := (hD.1 0 h0).2
  rcases hr with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
  · refine ⟨D.gates[0].b, D.gates[0].pb, by omega, fun x => ?_⟩
    have h := u2Val_gate D.gates x 0 h0 ha0 hb0
    simpa [ha, hpa] using h
  · refine ⟨D.gates[0].a, D.gates[0].pa, by omega, fun x => ?_⟩
    have h := u2Val_gate D.gates x 0 h0 ha0 hb0
    rw [hb, hpb, Bool.and_comm] at h
    simpa using h

/-- Helper to extract the canonical form of gate `j1` reading `(v, p1)` and `(9, q1)`. -/
private lemma gateJ_eval_form {D : U2Circuit} (hD : U2Wf D) (j1 : ℕ) (hj1 : j1 < D.gates.length)
    (v : ℕ) (hv : v < 9) (p1 : Bool)
    (hrv : (D.gates[j1].a = v ∧ D.gates[j1].pa = p1) ∨ (D.gates[j1].b = v ∧ D.gates[j1].pb = p1))
    (hr9 : D.gates[j1].a = 9 ∨ D.gates[j1].b = 9) :
    ∃ q1, ∀ x : Fin 9 → Bool, u2Val D.gates x (9 + j1) = ((u2Val D.gates x v != p1) && (u2Val D.gates x 9 != q1)) := by
  have ha1 := (hD.1 j1 hj1).1
  have hb1 := (hD.1 j1 hj1).2
  rcases hrv with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
  · rcases hr9 with h9 | h9
    · omega
    · refine ⟨D.gates[j1].pb, fun x => ?_⟩
      have h := u2Val_gate D.gates x j1 hj1 ha1 hb1
      simpa [ha, hpa, h9] using h
  · rcases hr9 with h9 | h9
    · refine ⟨D.gates[j1].pa, fun x => ?_⟩
      have h := u2Val_gate D.gates x j1 hj1 ha1 hb1
      rw [hb, hpb, h9, Bool.and_comm] at h
      exact h
    · omega

private lemma elim_ge_3_opp {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v : Fin 9) (p0 : Bool)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = p0) ∨ (D.gates[0].b = v.val ∧ D.gates[0].pb = p0))
    (j1 : ℕ) (hj1 : j1 < D.gates.length) (hj1_pos : 0 < j1)
    (hr1 : (D.gates[j1].a = v.val ∧ D.gates[j1].pa = !p0) ∨ (D.gates[j1].b = v.val ∧ D.gates[j1].pb = !p0))
    (val : Bool)
    (hnc : ∃ x y : Fin 9 → Bool, f (Function.update x v val) ≠ f (Function.update y v val)) :
    ∃ s', s' + 3 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v val)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, hgate⟩ := restrictU2_spec D hmin.1 v val
  have h0_mem : (⟨0, h0⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr0 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have h1_mem : (⟨j1, hj1⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr1 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  by_cases hvp : val = p0
  · subst hvp
    have hE0 : (restrictRun D.gates v val).1.getD 9 (Sum.inl false) = Sum.inl false := by
      have := (hgate 0 h0).1
      apply this
      rcases hr0 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
      · left; rw [ha, hpa, hEv]; cases val <;> rfl
      · right; rw [hb, hpb, hEv]; cases val <;> rfl
    have hnotout := not_out_of_isConst hmin.1 hmin.2.1 v val hnc 0 (by simp only [Nat.add_zero]; rw [hE0]; rfl)
    rcases min_has_reader_or_out hmin 0 h0 with ⟨fl, hout⟩ | ⟨k, hk, hk0, hkr⟩
    · exact (hnotout fl hout).elim
    · have hkne : k ≠ j1 := by
        intro heq; subst heq
        obtain ⟨u, q0, hu, hg0⟩ := gate0_eval_form hmin.1 h0 v.val val hr0
        obtain ⟨q1, hg1⟩ := gateJ_eval_form hmin.1 k hk v.val v.isLt (!val) hr1 hkr
        have hint := min_gate0_interact hmin h0 v.val u val q0 v.isLt hu hg0 k hk hk0 (!val) q1 hg1
        cases val <;> simp at hint
      have hk_mem : (⟨k, hk⟩ : Fin D.gates.length) ∈ elimSet D v val := by
        simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hkr with ha | hb
        · left; rw [ha, hE0]; rfl
        · right; rw [hb, hE0]; rfl
      have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v val := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard : 3 ≤ (elimSet D v val).card := by
        have h3 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h; exact hkne (congrArg Fin.val h).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = k := congrArg Fin.val h; omega⟩
        calc 3 = _ := h3.symm
          _ ≤ (elimSet D v val).card := Finset.card_le_card hsub
      exact ⟨(restrictU2 D v val).gates.length, by omega,
        restrictU2 D v val, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩
  · have hval_eq : val = !p0 := by cases val <;> cases p0 <;> simp_all
    subst hval_eq
    have hE1 : (restrictRun D.gates v (!p0)).1.getD (9 + j1) (Sum.inl false) = Sum.inl false := by
      apply (hgate j1 hj1).1
      rcases hr1 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
      · left; rw [ha, hpa, hEv]; cases p0 <;> rfl
      · right; rw [hb, hpb, hEv]; cases p0 <;> rfl
    have hnotout := not_out_of_isConst hmin.1 hmin.2.1 v (!p0) hnc j1 (by rw [hE1]; rfl)
    rcases min_has_reader_or_out hmin j1 hj1 with ⟨fl, hout⟩ | ⟨k, hk, hk1, hkr⟩
    · exact (hnotout fl hout).elim
    · have hk_mem : (⟨k, hk⟩ : Fin D.gates.length) ∈ elimSet D v (!p0) := by
        simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hkr with ha | hb
        · left; rw [ha, hE1]; rfl
        · right; rw [hb, hE1]; rfl
      have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v (!p0) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard : 3 ≤ (elimSet D v (!p0)).card := by
        have h3 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h; have h' : j1 = k := congrArg Fin.val h; omega
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = k := congrArg Fin.val h; omega⟩
        calc 3 = _ := h3.symm
          _ ≤ (elimSet D v (!p0)).card := Finset.card_le_card hsub
      exact ⟨(restrictU2 D v (!p0)).gates.length, by omega,
        restrictU2 D v (!p0), hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

private lemma elim_ge_4_same {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v : Fin 9) (p0 : Bool)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = p0) ∨ (D.gates[0].b = v.val ∧ D.gates[0].pb = p0))
    (j1 : ℕ) (hj1 : j1 < D.gates.length) (hj1_pos : 0 < j1)
    (hr1 : (D.gates[j1].a = v.val ∧ D.gates[j1].pa = p0) ∨ (D.gates[j1].b = v.val ∧ D.gates[j1].pb = p0))
    (hnc : ∃ x y : Fin 9 → Bool, f (Function.update x v p0) ≠ f (Function.update y v p0)) :
    ∃ s', s' + 4 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v p0)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, hgate⟩ := restrictU2_spec D hmin.1 v p0
  have hE0 : (restrictRun D.gates v p0).1.getD 9 (Sum.inl false) = Sum.inl false := by
    apply (hgate 0 h0).1
    rcases hr0 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
    · left; rw [ha, hpa, hEv]; cases p0 <;> rfl
    · right; rw [hb, hpb, hEv]; cases p0 <;> rfl
  have hE1 : (restrictRun D.gates v p0).1.getD (9 + j1) (Sum.inl false) = Sum.inl false := by
    apply (hgate j1 hj1).1
    rcases hr1 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
    · left; rw [ha, hpa, hEv]; cases p0 <;> rfl
    · right; rw [hb, hpb, hEv]; cases p0 <;> rfl
  have h0_mem : (⟨0, h0⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr0 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have h1_mem : (⟨j1, hj1⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr1 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have hnotout0 := not_out_of_isConst hmin.1 hmin.2.1 v p0 hnc 0 (by simp only [Nat.add_zero]; rw [hE0]; rfl)
  have hnotout1 := not_out_of_isConst hmin.1 hmin.2.1 v p0 hnc j1 (by rw [hE1]; rfl)
  -- Find reader k1 of j1 (automatically k1 > j1 > 0)
  obtain ⟨k1, hk1, hk1_gt, hk1_r⟩ :
      ∃ k1, ∃ (hk1 : k1 < D.gates.length), j1 < k1 ∧ (D.gates[k1].a = 9 + j1 ∨ D.gates[k1].b = 9 + j1) := by
    rcases min_has_reader_or_out hmin j1 hj1 with ⟨fl, hout⟩ | h
    · exact (hnotout1 fl hout).elim
    · exact h
  -- Find reader k0 ≠ j1 of gate 0
  obtain ⟨k0, hk0, hk0_pos, hk0_ne, hk0_r⟩ :
      ∃ k0, ∃ (hk0 : k0 < D.gates.length), 0 < k0 ∧ k0 ≠ j1 ∧ (D.gates[k0].a = 9 ∨ D.gates[k0].b = 9) := by
    rcases min_has_reader_or_out hmin 0 h0 with ⟨fl, hout⟩ | ⟨k, hk, hk_pos, hkr⟩
    · exact (hnotout0 fl hout).elim
    · by_cases hkj : k = j1
      · subst hkj
        obtain ⟨u, q0, hu, hg0⟩ := gate0_eval_form hmin.1 h0 v.val p0 hr0
        obtain ⟨q1, hg1⟩ := gateJ_eval_form hmin.1 k hk v.val v.isLt p0 hr1 hkr
        have hint := min_gate0_interact hmin h0 v.val u p0 q0 v.isLt hu hg0 k hk hk_pos p0 q1 hg1
        rcases hint.2.2 with ⟨fl, hout⟩ | h2
        · exact (hnotout0 fl hout).elim
        · exact h2
      · exact ⟨k, hk, hk_pos, hkj, hkr⟩
  have hk0_mem : (⟨k0, hk0⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hk0_r with ha | hb
    · left; rw [ha, hE0]; rfl
    · right; rw [hb, hE0]; rfl
  have hk1_mem : (⟨k1, hk1⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hk1_r with ha | hb
    · left; rw [ha, hE1]; rfl
    · right; rw [hb, hE1]; rfl
  have hcard4 : 4 ≤ (elimSet D v p0).card := by
    by_cases hkk : k0 = k1
    · subst hkk
      -- k0 reads BOTH 9 and 9 + j1 (which are distinct since j1 > 0), so both inputs of k0 are const!
      have hboth : isConstRef ((restrictRun D.gates v p0).1.getD D.gates[k0].a (Sum.inl false)) = true ∧
          isConstRef ((restrictRun D.gates v p0).1.getD D.gates[k0].b (Sum.inl false)) = true := by
        rcases hk0_r with ha0 | hb0 <;> rcases hk1_r with ha1 | hb1
        · omega
        · exact ⟨by rw [ha0, hE0]; rfl, by rw [hb1, hE1]; rfl⟩
        · exact ⟨by rw [ha1, hE1]; rfl, by rw [hb0, hE0]; rfl⟩
        · omega
      have hEk0 : isConstRef ((restrictRun D.gates v p0).1.getD (9 + k0) (Sum.inl false)) = true := by
        apply (hgate k0 hk0).2
        rw [isConstRef_flipRef, isConstRef_flipRef]
        exact hboth
      have hnotoutk := not_out_of_isConst hmin.1 hmin.2.1 v p0 hnc k0 hEk0
      rcases min_has_reader_or_out hmin k0 hk0 with ⟨fl, hout⟩ | ⟨r, hr, hr_gt, hrr⟩
      · exact (hnotoutk fl hout).elim
      · have hr_mem : (⟨r, hr⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
          simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hrr with ha | hb
          · left; rw [ha]; exact hEk0
          · right; rw [hb]; exact hEk0
        have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨r, hr⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v p0 := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have h4 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨r, hr⟩} : Finset (Fin D.gates.length)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h; have h' : k0 = r := congrArg Fin.val h; omega
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : j1 = k0 := congrArg Fin.val h; omega,
                   fun h => by have h' : j1 = r := congrArg Fin.val h; omega⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = k0 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = r := congrArg Fin.val h; omega⟩
        calc 4 = _ := h4.symm
          _ ≤ (elimSet D v p0).card := Finset.card_le_card hsub
    · have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨k1, hk1⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v p0 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption
      have h4 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨k1, hk1⟩} : Finset (Fin D.gates.length)).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h; exact hkk (congrArg Fin.val h)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hk0_ne (congrArg Fin.val h).symm,
                 fun h => by have h' : j1 = k1 := congrArg Fin.val h; omega⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                 fun h => by have h' : 0 = k0 := congrArg Fin.val h; omega,
                 fun h => by have h' : 0 = k1 := congrArg Fin.val h; omega⟩
      calc 4 = _ := h4.symm
        _ ≤ (elimSet D v p0).card := Finset.card_le_card hsub
  exact ⟨(restrictU2 D v p0).gates.length, by omega,
    restrictU2 D v p0, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

/-! ### Slot-Counting Lower Bound and Single-Fanout First-Gate Lemma -/

private def u2Slots (D : U2Circuit) : List ℕ :=
  (match D.out with | Sum.inl _ => [] | Sum.inr (w, _) => [w]) ++
    D.gates.flatMap fun g => [g.a, g.b]

private lemma u2Slots_length (D : U2Circuit) :
    (u2Slots D).length ≤ 2 * D.gates.length + 1 := by
  have hflat : ∀ gs : List U2Gate, (gs.flatMap fun g => [g.a, g.b]).length = 2 * gs.length := by
    intro gs; induction gs with
    | nil => simp
    | cons g gs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega
  unfold u2Slots
  rw [List.length_append, hflat]
  rcases D.out with c | ⟨w, fl⟩
  · simp
  · simp; omega

private lemma u2Wires_agree_except (gs : List U2Gate) (u : ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length)
    (hno : ∀ g ∈ gs, g.a ≠ u ∧ g.b ≠ u)
    (hagree : ∀ i, i ≠ u → w₁.getD i false = w₂.getD i false) :
    ∀ i, i ≠ u → (u2Wires gs w₁).getD i false = (u2Wires gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hagree
  | cons g gs ih =>
    have hg := hno g List.mem_cons_self
    have hstep_eq : ((w₁.getD g.a false != g.pa) && (w₁.getD g.b false != g.pb)) =
        ((w₂.getD g.a false != g.pa) && (w₂.getD g.b false != g.pb)) := by
      rw [hagree g.a hg.1, hagree g.b hg.2]
    rw [u2Wires_cons, u2Wires_cons]
    apply ih (u2Step w₁ g) (u2Step w₂ g) (by simp [u2Step, hlen])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    by_cases hlt : i < w₁.length
    · simp only [u2Step]
      rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
      exact hagree i hi
    · by_cases heq : i = w₁.length
      · subst heq
        simp only [u2Step]
        rw [getD_snoc_eq, hlen, getD_snoc_eq, hstep_eq]
      · simp only [u2Step]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma essential_mem_u2Slots {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hev : ∀ x, u2Eval D x = f x) (v : Fin 9)
    (hess : ∃ x y : Fin 9 → Bool, (∀ i, i ≠ v → x i = y i) ∧ f x ≠ f y) :
    v.val ∈ u2Slots D := by
  by_contra hnot
  obtain ⟨x, y, hxy, hne⟩ := hess
  have hout : ∀ fl, D.out ≠ Sum.inr (v.val, fl) := by
    intro fl h
    apply hnot
    simp [u2Slots, h]
  have hno : ∀ g ∈ D.gates, g.a ≠ v.val ∧ g.b ≠ v.val := by
    intro g hg
    constructor <;> intro heq <;> apply hnot
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, hg, by simp [heq]⟩)
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, hg, by simp [heq]⟩)
  have hagree0 : ∀ i, i ≠ v.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro i hi
    by_cases hlt : i < 9
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      exact hxy ⟨i, hlt⟩ (fun h => hi (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
  have hagree := u2Wires_agree_except D.gates v.val (List.ofFn x) (List.ofFn y) (by simp) hno hagree0
  apply hne
  rw [← hev x, ← hev y]
  unfold u2Eval
  rcases h : D.out with c | ⟨w, fl⟩
  · rfl
  · simp only [refEval]
    have hw : w ≠ v.val := fun heq => hout fl (by rw [h, heq])
    rw [hagree w hw]

private lemma slot_lower_bound {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (S : Finset (Fin 9))
    (hS : ∀ v ∈ S, ∃ x y : Fin 9 → Bool, (∀ i, i ≠ v → x i = y i) ∧ f x ≠ f y) :
    S.card - 1 ≤ D.gates.length := by
  let A : Finset ℕ := S.image Fin.val
  let B : Finset ℕ := (Finset.range D.gates.length).image (fun j => 9 + j)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    simp only [A, B, Finset.mem_image, Finset.mem_range] at hwA hwB
    rcases hwA with ⟨v, _, rfl⟩
    rcases hwB with ⟨j, _, hj⟩
    have := v.isLt; omega
  have hA : A.card = S.card := Finset.card_image_of_injective S Fin.val_injective
  have hB : B.card = D.gates.length := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  have hsub : A ∪ B ⊆ (u2Slots D).toFinset := by
    intro w hw
    rw [List.mem_toFinset]
    simp only [Finset.mem_union, A, B, Finset.mem_image, Finset.mem_range] at hw
    rcases hw with ⟨v, hvS, rfl⟩ | ⟨j, hj, rfl⟩
    · exact essential_mem_u2Slots hmin.2.1 v (hS v hvS)
    · rcases min_has_reader_or_out hmin j hj with ⟨fl, hout⟩ | ⟨k, hk, _, hkr⟩
      · simp [u2Slots, hout]
      · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨D.gates[k], List.getElem_mem hk, ?_⟩)
        rcases hkr with ha | hb
        · simp [ha]
        · simp [hb]
  have hle1 : (A ∪ B).card ≤ (u2Slots D).toFinset.card := Finset.card_le_card hsub
  have hle2 : (u2Slots D).toFinset.card ≤ (u2Slots D).length := List.toFinset_card_le _
  have hle3 := u2Slots_length D
  rw [Finset.card_union_of_disjoint hdisj, hA, hB] at hle1
  omega

private lemma single_fanout_first_gate {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v u : Fin 9) (pv pu : Bool) (hvu : v ≠ u)
    (hg0 : ∀ x : Fin 9 → Bool, u2Val D.gates x 9 = ((u2Val D.gates x v.val != pv) && (u2Val D.gates x u.val != pu)))
    (hout : ∀ fl, D.out ≠ Sum.inr (v.val, fl))
    (hno : ∀ k (hk : k < D.gates.length), 0 < k → D.gates[k].a ≠ v.val ∧ D.gates[k].b ≠ v.val) :
    ∀ x : Fin 9 → Bool,
      f (Function.update (Function.update x u pu) v false) =
      f (Function.update (Function.update x u pu) v true) := by
  intro x
  let x0 := Function.update (Function.update x u pu) v false
  let x1 := Function.update (Function.update x u pu) v true
  have hsplit : D.gates = D.gates[0] :: D.gates.drop 1 :=
    List.drop_eq_getElem_cons h0
  have hstep0 : ∀ z : Fin 9 → Bool, z u = pu →
      (u2Step (List.ofFn z) D.gates[0]).getD 9 false = false := by
    intro z hzu
    have h1 := hg0 z
    have hu_val : u2Val D.gates z u.val = pu := by rw [u2Val_input _ _ u.val u.isLt]; exact hzu
    rw [hu_val] at h1
    have hfalse : u2Val D.gates z 9 = false := by
      rw [h1]; cases (u2Val D.gates z v.val != pv) <;> cases pu <;> rfl
    unfold u2Val at hfalse
    rw [hsplit, u2Wires_cons] at hfalse
    rw [u2Wires_getD_lt _ _ 9 (by simp only [u2Step, List.length_append, List.length_ofFn, List.length_singleton]; omega)] at hfalse
    exact hfalse
  have hno_drop : ∀ g ∈ D.gates.drop 1, g.a ≠ v.val ∧ g.b ≠ v.val := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    have hlt : 1 + t < D.gates.length := by simp at ht; omega
    have h := hno (1 + t) hlt (by omega)
    simpa [List.getElem_drop, Nat.add_comm] using h
  have hstep_agree : ∀ i, i ≠ v.val →
      (u2Step (List.ofFn x0) D.gates[0]).getD i false = (u2Step (List.ofFn x1) D.gates[0]).getD i false := by
    intro i hi
    by_cases hlt : i < 9
    · simp only [u2Step]
      rw [getD_snoc_lt _ _ _ i (by rw [List.length_ofFn]; exact hlt),
          getD_snoc_lt _ _ _ i (by rw [List.length_ofFn]; exact hlt),
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have hne : (⟨i, hlt⟩ : Fin 9) ≠ v := fun h => hi (congrArg Fin.val h)
      simp [x0, x1, Function.update_of_ne hne]
    · by_cases heq : i = 9
      · subst heq
        rw [hstep0 x0 (by simp [x0, Function.update_of_ne hvu.symm]),
            hstep0 x1 (by simp [x1, Function.update_of_ne hvu.symm])]
      · simp only [u2Step]
        rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
  have hfinal := u2Wires_agree_except (D.gates.drop 1) v.val
    (u2Step (List.ofFn x0) D.gates[0]) (u2Step (List.ofFn x1) D.gates[0])
    (by simp [u2Step]) hno_drop hstep_agree
  rw [← hmin.2.1 x0, ← hmin.2.1 x1]
  unfold u2Eval
  rcases h : D.out with c | ⟨w, fl⟩
  · rfl
  · simp only [refEval]
    have hw : w ≠ v.val := fun heq => hout fl (by rw [h, heq])
    rw [hsplit, u2Wires_cons, u2Wires_cons, hfinal w hw]

/-! ## Section 3: Pet9 Subgraph DP Verification and Final Theorem -/

private inductive BTree | l (v : ℕ) | n (a b : BTree)

private def BTree.get : BTree → ℕ → ℕ → ℕ
  | .l v, _, _ => v
  | .n a b, d + 1, idx => if idx.testBit d then b.get d idx else a.get d idx
  | .n a _, 0, _ => a.get 0 0

private def dpSub0 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 0)) (.n (.l 0) (.l 1))) (.n (.n (.l 0) (.l 0)) (.n (.l 1) (.l 2)))) (.n (.n (.n (.l 0) (.l 0)) (.n (.l 0) (.l 1))) (.n (.n (.l 1) (.l 1)) (.n (.l 2) (.l 4))))) (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 0) (.l 2))) (.n (.n (.l 0) (.l 1)) (.n (.l 1) (.l 4)))) (.n (.n (.n (.l 1) (.l 2)) (.n (.l 1) (.l 4))) (.n (.n (.l 2) (.l 4)) (.n (.l 4) (.l 7))))))
private def dpSub1 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 0) (.l 2))) (.n (.n (.l 0) (.l 1)) (.n (.l 1) (.l 4)))) (.n (.n (.n (.l 0) (.l 1)) (.n (.l 0) (.l 2))) (.n (.n (.l 1) (.l 3)) (.n (.l 2) (.l 5))))) (.n (.n (.n (.n (.l 0) (.l 2)) (.n (.l 0) (.l 3))) (.n (.n (.l 0) (.l 2)) (.n (.l 1) (.l 5)))) (.n (.n (.n (.l 1) (.l 4)) (.n (.l 1) (.l 5))) (.n (.n (.l 2) (.l 5)) (.n (.l 4) (.l 7))))))
private def dpSub2 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 0)) (.n (.l 1) (.l 2))) (.n (.n (.l 0) (.l 0)) (.n (.l 2) (.l 3)))) (.n (.n (.n (.l 0) (.l 0)) (.n (.l 1) (.l 2))) (.n (.n (.l 1) (.l 1)) (.n (.l 4) (.l 5))))) (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 1) (.l 4))) (.n (.n (.l 0) (.l 1)) (.n (.l 2) (.l 5)))) (.n (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 5))) (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 7))))))
private def dpSub3 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 1) (.l 4))) (.n (.n (.l 0) (.l 1)) (.n (.l 2) (.l 5)))) (.n (.n (.n (.l 0) (.l 1)) (.n (.l 1) (.l 4))) (.n (.n (.l 1) (.l 3)) (.n (.l 4) (.l 7))))) (.n (.n (.n (.n (.l 0) (.l 2)) (.n (.l 1) (.l 5))) (.n (.n (.l 0) (.l 2)) (.n (.l 2) (.l 5)))) (.n (.n (.n (.l 1) (.l 4)) (.n (.l 3) (.l 7))) (.n (.n (.l 2) (.l 5)) (.n (.l 5) (.l 8))))))
private def dpSub4 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 0)) (.n (.l 0) (.l 1))) (.n (.n (.l 1) (.l 1)) (.n (.l 2) (.l 4)))) (.n (.n (.n (.l 0) (.l 0)) (.n (.l 0) (.l 1))) (.n (.n (.l 2) (.l 2)) (.n (.l 3) (.l 5))))) (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 0) (.l 2))) (.n (.n (.l 1) (.l 3)) (.n (.l 2) (.l 5)))) (.n (.n (.n (.l 1) (.l 2)) (.n (.l 1) (.l 4))) (.n (.n (.l 4) (.l 5)) (.n (.l 5) (.l 7))))))
private def dpSub5 : BTree := (.n (.n (.n (.n (.n (.l 1) (.l 2)) (.n (.l 1) (.l 4))) (.n (.n (.l 2) (.l 4)) (.n (.l 4) (.l 7)))) (.n (.n (.n (.l 1) (.l 2)) (.n (.l 1) (.l 4))) (.n (.n (.l 4) (.l 5)) (.n (.l 5) (.l 7))))) (.n (.n (.n (.n (.l 1) (.l 4)) (.n (.l 1) (.l 5))) (.n (.n (.l 2) (.l 5)) (.n (.l 4) (.l 7)))) (.n (.n (.n (.l 3) (.l 5)) (.n (.l 3) (.l 7))) (.n (.n (.l 5) (.l 8)) (.n (.l 7) (.l 9))))))
private def dpSub6 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 0)) (.n (.l 1) (.l 2))) (.n (.n (.l 1) (.l 1)) (.n (.l 4) (.l 5)))) (.n (.n (.n (.l 0) (.l 0)) (.n (.l 1) (.l 2))) (.n (.n (.l 2) (.l 2)) (.n (.l 5) (.l 5))))) (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 1) (.l 4))) (.n (.n (.l 1) (.l 3)) (.n (.l 4) (.l 7)))) (.n (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 5))) (.n (.n (.l 4) (.l 5)) (.n (.l 7) (.l 8))))))
private def dpSub7 : BTree := (.n (.n (.n (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 5))) (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 7)))) (.n (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 5))) (.n (.n (.l 4) (.l 5)) (.n (.l 7) (.l 8))))) (.n (.n (.n (.n (.l 1) (.l 4)) (.n (.l 3) (.l 7))) (.n (.n (.l 2) (.l 5)) (.n (.l 5) (.l 8)))) (.n (.n (.n (.l 3) (.l 5)) (.n (.l 5) (.l 8))) (.n (.n (.l 5) (.l 8)) (.n (.l 8) (.l 11))))))
private def dpSub8 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 0)) (.n (.l 0) (.l 1))) (.n (.n (.l 0) (.l 0)) (.n (.l 1) (.l 2)))) (.n (.n (.n (.l 1) (.l 1)) (.n (.l 1) (.l 3))) (.n (.n (.l 2) (.l 2)) (.n (.l 4) (.l 5))))) (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 0) (.l 2))) (.n (.n (.l 0) (.l 1)) (.n (.l 1) (.l 4)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 5))) (.n (.n (.l 3) (.l 5)) (.n (.l 5) (.l 7))))))
private def dpSub9 : BTree := (.n (.n (.n (.n (.n (.l 1) (.l 2)) (.n (.l 1) (.l 4))) (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 5)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 5))) (.n (.n (.l 4) (.l 5)) (.n (.l 5) (.l 8))))) (.n (.n (.n (.n (.l 1) (.l 4)) (.n (.l 1) (.l 5))) (.n (.n (.l 1) (.l 4)) (.n (.l 3) (.l 7)))) (.n (.n (.n (.l 4) (.l 7)) (.n (.l 4) (.l 7))) (.n (.n (.l 5) (.l 7)) (.n (.l 7) (.l 9))))))
private def dpSub10 : BTree := (.n (.n (.n (.n (.n (.l 1) (.l 1)) (.n (.l 2) (.l 4))) (.n (.n (.l 1) (.l 1)) (.n (.l 4) (.l 5)))) (.n (.n (.n (.l 2) (.l 2)) (.n (.l 4) (.l 5))) (.n (.n (.l 4) (.l 4)) (.n (.l 7) (.l 7))))) (.n (.n (.n (.n (.l 1) (.l 3)) (.n (.l 2) (.l 5))) (.n (.n (.l 1) (.l 3)) (.n (.l 4) (.l 7)))) (.n (.n (.n (.l 4) (.l 5)) (.n (.l 5) (.l 8))) (.n (.n (.l 5) (.l 7)) (.n (.l 7) (.l 9))))))
private def dpSub11 : BTree := (.n (.n (.n (.n (.n (.l 2) (.l 4)) (.n (.l 4) (.l 7))) (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 7)))) (.n (.n (.n (.l 3) (.l 5)) (.n (.l 5) (.l 7))) (.n (.n (.l 5) (.l 7)) (.n (.l 7) (.l 9))))) (.n (.n (.n (.n (.l 2) (.l 5)) (.n (.l 4) (.l 7))) (.n (.n (.l 2) (.l 5)) (.n (.l 5) (.l 8)))) (.n (.n (.n (.l 5) (.l 7)) (.n (.l 7) (.l 9))) (.n (.n (.l 5) (.l 8)) (.n (.l 8) (.l 11))))))
private def dpSub12 : BTree := (.n (.n (.n (.n (.n (.l 0) (.l 0)) (.n (.l 0) (.l 1))) (.n (.n (.l 1) (.l 1)) (.n (.l 2) (.l 4)))) (.n (.n (.n (.l 1) (.l 1)) (.n (.l 1) (.l 3))) (.n (.n (.l 4) (.l 4)) (.n (.l 5) (.l 7))))) (.n (.n (.n (.n (.l 0) (.l 1)) (.n (.l 0) (.l 2))) (.n (.n (.l 1) (.l 3)) (.n (.l 2) (.l 5)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 5))) (.n (.n (.l 5) (.l 7)) (.n (.l 5) (.l 8))))))
private def dpSub13 : BTree := (.n (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 2) (.l 5))) (.n (.n (.l 4) (.l 5)) (.n (.l 5) (.l 7)))) (.n (.n (.n (.l 4) (.l 5)) (.n (.l 4) (.l 7))) (.n (.n (.l 7) (.l 7)) (.n (.l 7) (.l 9))))) (.n (.n (.n (.n (.l 2) (.l 5)) (.n (.l 2) (.l 5))) (.n (.n (.l 4) (.l 7)) (.n (.l 5) (.l 8)))) (.n (.n (.n (.l 5) (.l 7)) (.n (.l 5) (.l 8))) (.n (.n (.l 7) (.l 9)) (.n (.l 8) (.l 11))))))
private def dpSub14 : BTree := (.n (.n (.n (.n (.n (.l 1) (.l 1)) (.n (.l 2) (.l 4))) (.n (.n (.l 3) (.l 3)) (.n (.l 5) (.l 7)))) (.n (.n (.n (.l 2) (.l 2)) (.n (.l 4) (.l 5))) (.n (.n (.l 5) (.l 5)) (.n (.l 7) (.l 8))))) (.n (.n (.n (.n (.l 1) (.l 3)) (.n (.l 2) (.l 5))) (.n (.n (.l 3) (.l 5)) (.n (.l 5) (.l 8)))) (.n (.n (.n (.l 4) (.l 5)) (.n (.l 5) (.l 8))) (.n (.n (.l 7) (.l 8)) (.n (.l 8) (.l 11))))))
private def dpSub15 : BTree := (.n (.n (.n (.n (.n (.l 4) (.l 5)) (.n (.l 5) (.l 7))) (.n (.n (.l 5) (.l 7)) (.n (.l 8) (.l 9)))) (.n (.n (.n (.l 5) (.l 5)) (.n (.l 7) (.l 8))) (.n (.n (.l 7) (.l 8)) (.n (.l 9) (.l 11))))) (.n (.n (.n (.n (.l 4) (.l 7)) (.n (.l 5) (.l 8))) (.n (.n (.l 5) (.l 8)) (.n (.l 8) (.l 11)))) (.n (.n (.n (.l 7) (.l 8)) (.n (.l 8) (.l 11))) (.n (.n (.l 8) (.l 11)) (.n (.l 11) (.l 13))))))
private def dpTree : BTree := (.n (.n (.n (.n dpSub0 dpSub1) (.n dpSub2 dpSub3)) (.n (.n dpSub4 dpSub5) (.n dpSub6 dpSub7))) (.n (.n (.n dpSub8 dpSub9) (.n dpSub10 dpSub11)) (.n (.n dpSub12 dpSub13) (.n dpSub14 dpSub15))))

private def dpVal (H : ℕ) : ℕ := dpTree.get 9 H

private def nbrMask : ℕ → ℕ
  | 0 => 50 | 1 => 69 | 2 => 138 | 3 => 276 | 4 => 9
  | 5 => 385 | 6 => 258 | 7 => 36 | 8 => 104 | _ => 0

private def delBit (m v : ℕ) : ℕ := m &&& (511 ^^^ (1 <<< v))

private def canonH (H : ℕ) : ℕ :=
  (List.range 9).foldl (fun acc v =>
    if H.testBit v && ((H &&& nbrMask v) != 0) then acc ||| (1 <<< v) else acc) 0

private def pop9 (m : ℕ) : ℕ :=
  (List.range 9).countP (fun v => m.testBit v)

private def restrictHA (H v : ℕ) (val : Bool) : ℕ × ℕ :=
  if !val then
    (canonH (delBit H v), 0)
  else
    let A1 := if H.testBit v then H &&& nbrMask v else 0
    (canonH (delBit H v &&& (511 ^^^ A1)), A1)

private def dpValHA (H A : ℕ) : ℕ :=
  let c := canonH H
  if c = 0 then pop9 A - 1 else pop9 A + dpVal c

private def petEdges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]

private def petFun (H A : ℕ) (x : Fin 9 → Bool) : Bool :=
  (petEdges.any fun e => H.testBit e.1.val && H.testBit e.2.val && x e.1 && x e.2) ||
    ((List.finRange 9).any fun v => A.testBit v.val && x v)

/-! ### Finite Bitmask Lemmas (verified on `Fin 512` / `Fin 9` by `decide`) -/

private def allPow2 : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, base, f => f base
  | d + 1, base, f => allPow2 d base f && allPow2 d (base + (1 <<< d)) f

private lemma allPow2_true : ∀ d base f, allPow2 d base f = true →
    ∀ i, i < (1 <<< d) → f (base + i) = true
  | 0, base, f, h, i, hi => by
    have : i = 0 := by omega
    subst this; simpa [allPow2] using h
  | d + 1, base, f, h, i, hi => by
    simp only [allPow2, Bool.and_eq_true] at h
    have hshift : 1 <<< (d + 1) = (1 <<< d) + (1 <<< d) := by
      simp [Nat.shiftLeft_eq]; omega
    by_cases hlt : i < (1 <<< d)
    · exact allPow2_true d base f h.1 i hlt
    · have h2 := allPow2_true d (base + (1 <<< d)) f h.2 (i - (1 <<< d)) (by omega)
      have heq : base + (1 <<< d) + (i - (1 <<< d)) = base + i := by omega
      rwa [heq] at h2

private lemma all512_true (f : ℕ → Bool) (h : allPow2 9 0 f = true) (m : ℕ) (hm : m < 512) :
    f m = true := by
  have h1 : 1 <<< 9 = 512 := by decide
  simpa using allPow2_true 9 0 f h m (by omega)

private lemma petEdges_iff_nbr (u v : Fin 9) :
    (petEdges.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)) =
      (nbrMask u.val).testBit v.val := by
  revert u v; decide

private lemma nbrMask_irrefl (u : Fin 9) : (nbrMask u.val).testBit u.val = false := by
  revert u; decide

private lemma canonH_lt (H : Fin 512) : canonH H.val < 512 := by
  have h : allPow2 9 0 (fun m => decide (canonH m < 512)) = true := by decide
  simpa using all512_true _ h H.val H.isLt

private lemma canonH_idem (H : Fin 512) : canonH (canonH H.val) = canonH H.val := by
  have h : allPow2 9 0 (fun m => decide (canonH (canonH m) = canonH m)) = true := by decide
  simpa using all512_true _ h H.val H.isLt

private lemma canonH_testBit (H : Fin 512) (v : Fin 9) :
    (canonH H.val).testBit v.val =
      (H.val.testBit v.val && (List.finRange 9).any fun w => H.val.testBit w.val && (nbrMask v.val).testBit w.val) := by
  have h : allPow2 9 0 (fun m => (List.finRange 9).all fun v =>
      (canonH m).testBit v.val == (m.testBit v.val && (List.finRange 9).any fun w => m.testBit w.val && (nbrMask v.val).testBit w.val)) = true := by
    decide
  have h1 := all512_true _ h H.val H.isLt
  simpa using List.all_eq_true.mp h1 v (List.mem_finRange v)

private lemma mask511_xor_testBit (v w : Fin 9) :
    (511 ^^^ (1 <<< v.val)).testBit w.val = (w != v) := by
  revert v w; decide

private lemma mask511_testBit (w : Fin 9) : (511 : ℕ).testBit w.val = true := by
  revert w; decide

private lemma delBit_lt (m : Fin 512) (v : Fin 9) : delBit m.val v.val < 512 := by
  exact Nat.lt_of_le_of_lt Nat.and_le_left m.isLt

private lemma delBit_testBit (m : Fin 512) (v w : Fin 9) :
    (delBit m.val v.val).testBit w.val = (m.val.testBit w.val && (w != v)) := by
  unfold delBit
  rw [Nat.testBit_and, mask511_xor_testBit]

private lemma delBit_pop9 (m : Fin 512) (v : Fin 9) :
    m.val.testBit v.val = true → pop9 (delBit m.val v.val) + 1 = pop9 m.val := by
  intro hv
  have h : allPow2 9 0 (fun x => (List.finRange 9).all fun w =>
      !x.testBit w.val || decide (pop9 (delBit x w.val) + 1 = pop9 x)) = true := by decide
  have h1 := List.all_eq_true.mp (all512_true _ h m.val m.isLt) v (List.mem_finRange v)
  simpa [hv] using h1

private lemma pop9_zero_iff (m : Fin 512) : pop9 m.val = 0 ↔ m.val = 0 := by
  have h : allPow2 9 0 (fun x => decide (pop9 x = 0 ↔ x = 0)) = true := by decide
  simpa using all512_true _ h m.val m.isLt

private lemma exists_bit_decide (m : Fin 512) :
    m.val ≠ 0 → (List.finRange 9).any (fun v => m.val.testBit v.val) = true := by
  intro hne
  have h : allPow2 9 0 (fun x => decide (x = 0) || (List.finRange 9).any fun v => x.testBit v.val) = true := by decide
  have h1 := all512_true _ h m.val m.isLt
  simpa [hne] using h1

private lemma exists_other_bit_decide (m : Fin 512) (v : Fin 9) :
    2 ≤ pop9 m.val → (List.finRange 9).any (fun w => (w != v) && m.val.testBit w.val) = true := by
  intro h2
  have h : allPow2 9 0 (fun x => (List.finRange 9).all fun u =>
      decide (pop9 x < 2) || (List.finRange 9).any fun w => (w != u) && x.testBit w.val) = true := by decide
  have h1 := List.all_eq_true.mp (all512_true _ h m.val m.isLt) v (List.mem_finRange v)
  have hlt : ¬ pop9 m.val < 2 := by omega
  simpa [hlt] using h1

private lemma pop9_eq_card (m : ℕ) (hm : m < 512) :
    pop9 m = (Finset.univ.filter fun v : Fin 9 => m.testBit v.val = true).card := by
  have h : allPow2 9 0 (fun k => decide (pop9 k =
      ((List.finRange 9).filter fun v : Fin 9 => k.testBit v.val).length)) = true := by decide
  have h1 : pop9 m = ((List.finRange 9).filter fun v : Fin 9 => m.testBit v.val).length := by
    simpa using all512_true _ h m hm
  rw [h1]
  have hnodup : ((List.finRange 9).filter fun v : Fin 9 => m.testBit v.val).Nodup :=
    (List.nodup_finRange 9).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1; ext v; simp

private lemma restrictHA_true_bits (H : Fin 512) (v w : Fin 9) :
    (restrictHA H.val v.val true).2.testBit w.val =
      (H.val.testBit v.val && H.val.testBit w.val && (nbrMask v.val).testBit w.val) := by
  simp only [restrictHA, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases h : H.val.testBit v.val
  · simp
  · simp [Nat.testBit_and]

private lemma remH_lt (H : Fin 512) (v : Fin 9) :
    delBit H.val v.val &&& (511 ^^^ (restrictHA H.val v.val true).2) < 512 := by
  have h1 : delBit H.val v.val < 512 := delBit_lt H v
  exact Nat.lt_of_le_of_lt Nat.and_le_left h1

private lemma restrictHA_props (H : Fin 512) (v : Fin 9) (val : Bool) :
    let r := restrictHA H.val v.val val
    r.1 < 512 ∧ r.2 < 512 ∧ canonH r.1 = r.1 ∧ (r.1 &&& r.2) = 0 ∧
    (H.val.testBit v.val = true → pop9 r.1 < pop9 H.val) ∧
    (canonH H.val = H.val → H.val.testBit v.val = true → val = true → r.2 ≠ 0) := by
  cases val
  · simp only [restrictHA, Bool.not_false, ↓reduceIte]
    have hdl : delBit H.val v.val < 512 := delBit_lt H v
    have hcl : canonH (delBit H.val v.val) < 512 := canonH_lt ⟨_, hdl⟩
    refine ⟨hcl, by omega, canonH_idem ⟨_, hdl⟩, by simp, ?_, fun _ _ h => by simp at h⟩
    intro hv
    have hle : pop9 (canonH (delBit H.val v.val)) ≤ pop9 (delBit H.val v.val) := by
      rw [pop9_eq_card _ hcl, pop9_eq_card _ hdl]
      apply Finset.card_le_card
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [canonH_testBit ⟨_, hdl⟩ w, Bool.and_eq_true] at hw
      exact hw.1
    have hdp := delBit_pop9 H v hv
    omega
  · set A1 := (restrictHA H.val v.val true).2
    set rem := delBit H.val v.val &&& (511 ^^^ A1)
    have hdl : delBit H.val v.val < 512 := delBit_lt H v
    have hrl : rem < 512 := remH_lt H v
    have hcl : canonH rem < 512 := canonH_lt ⟨rem, hrl⟩
    have hH1_eq : (restrictHA H.val v.val true).1 = canonH rem := by
      simp [restrictHA, A1, rem]
    have hA1_lt : A1 < 512 := by
      simp only [A1, restrictHA, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases H.val.testBit v.val
      · simp
      · simp only [↓reduceIte]
        exact Nat.lt_of_le_of_lt Nat.and_le_left H.isLt
    have hdisj : (canonH rem &&& A1) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hi : i < 9
      · let w : Fin 9 := ⟨i, hi⟩
        cases hc : (canonH rem).testBit w.val
        · rfl
        · rw [canonH_testBit ⟨rem, hrl⟩ w, Bool.and_eq_true] at hc
          have hrw : rem.testBit w.val = true := hc.1
          simp only [rem, Nat.testBit_and, Nat.testBit_xor, mask511_testBit w, Bool.and_eq_true] at hrw
          have hAf : A1.testBit i = false := by
            have := hrw.2; cases h : A1.testBit w.val <;> simp_all [w]
          simp [hAf]
      · have h2pow : 512 ≤ 2 ^ i := by
          have : (2 : ℕ) ^ 9 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
          simpa using this
        have hzero : (canonH rem).testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcl h2pow)
        simp [hzero]
    dsimp only
    rw [hH1_eq]
    refine ⟨hcl, hA1_lt, canonH_idem ⟨rem, hrl⟩, hdisj, ?_, ?_⟩
    · intro hv
      have hle : pop9 (canonH rem) ≤ pop9 (delBit H.val v.val) := by
        rw [pop9_eq_card _ hcl, pop9_eq_card _ hdl]
        apply Finset.card_le_card
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [canonH_testBit ⟨rem, hrl⟩ w, Bool.and_eq_true] at hw
        have hrw := hw.1
        simp only [rem, Nat.testBit_and, Bool.and_eq_true] at hrw
        exact hrw.1
      have hdp := delBit_pop9 H v hv
      omega
    · intro hcan hv _
      have hcv : (canonH H.val).testBit v.val = true := by rw [hcan]; exact hv
      rw [canonH_testBit H v, Bool.and_eq_true, List.any_eq_true] at hcv
      rcases hcv.2 with ⟨w, _, hwn⟩
      simp only [Bool.and_eq_true] at hwn
      have hbit : A1.testBit w.val = true := by
        change (restrictHA H.val v.val true).2.testBit w.val = true
        rw [restrictHA_true_bits H v w]
        simp [hv, hwn.1, hwn.2]
      intro h0
      dsimp only [A1] at hbit
      rw [h0] at hbit; simp at hbit

private lemma restrictHA_true_H1_bit (H : Fin 512) (v a b : Fin 9) :
    (nbrMask a.val).testBit b.val = true →
    H.val.testBit a.val = true → H.val.testBit b.val = true →
    a ≠ v → b ≠ v →
    (restrictHA H.val v.val true).2.testBit a.val = false →
    (restrictHA H.val v.val true).2.testBit b.val = false →
    (restrictHA H.val v.val true).1.testBit a.val = true ∧
      (restrictHA H.val v.val true).1.testBit b.val = true := by
  intro hnbr ha hb hav hbv haA hbA
  have hnbr_sym : (nbrMask b.val).testBit a.val = true := by
    have : ∀ x y : Fin 9, (nbrMask x.val).testBit y.val = (nbrMask y.val).testBit x.val := by decide
    rw [this]; exact hnbr
  set A1 := (restrictHA H.val v.val true).2
  set rem := delBit H.val v.val &&& (511 ^^^ A1)
  have hrem_lt : rem < 512 := remH_lt H v
  have hH1_eq : (restrictHA H.val v.val true).1 = canonH rem := by
    simp [restrictHA, A1, rem]
  have hrem_a : rem.testBit a.val = true := by
    change (delBit H.val v.val &&& (511 ^^^ A1)).testBit a.val = true
    rw [Nat.testBit_and, Nat.testBit_xor, delBit_testBit H v a, mask511_testBit a, ha, haA]
    simp [hav]
  have hrem_b : rem.testBit b.val = true := by
    change (delBit H.val v.val &&& (511 ^^^ A1)).testBit b.val = true
    rw [Nat.testBit_and, Nat.testBit_xor, delBit_testBit H v b, mask511_testBit b, hb, hbA]
    simp [hbv]
  rw [hH1_eq]
  constructor
  · rw [canonH_testBit ⟨rem, hrem_lt⟩ a, Bool.and_eq_true]
    exact ⟨hrem_a, List.any_eq_true.mpr ⟨b, List.mem_finRange _, by simp [hrem_b, hnbr]⟩⟩
  · rw [canonH_testBit ⟨rem, hrem_lt⟩ b, Bool.and_eq_true]
    exact ⟨hrem_b, List.any_eq_true.mpr ⟨a, List.mem_finRange _, by simp [hrem_a, hnbr_sym]⟩⟩

private lemma restrictHA_true_H1_sub (H : Fin 512) (v w : Fin 9) :
    (restrictHA H.val v.val true).1.testBit w.val = true →
    H.val.testBit w.val = true ∧ w ≠ v := by
  intro hw
  set A1 := (restrictHA H.val v.val true).2
  set rem := delBit H.val v.val &&& (511 ^^^ A1)
  have hrem_lt : rem < 512 := remH_lt H v
  have hH1_eq : (restrictHA H.val v.val true).1 = canonH rem := by
    simp [restrictHA, A1, rem]
  rw [hH1_eq, canonH_testBit ⟨rem, hrem_lt⟩ w, Bool.and_eq_true] at hw
  have hrem_w : rem.testBit w.val = true := hw.1
  simp only [rem, Nat.testBit_and, delBit_testBit H v w, Bool.and_eq_true, bne_iff_ne] at hrem_w
  exact hrem_w.1

private lemma disj_delBit (H A : Fin 512) (v : Fin 9) :
    (H.val &&& A.val) = 0 → (H.val &&& delBit A.val v.val) = 0 := by
  intro h
  apply Nat.eq_of_testBit_eq
  intro i
  have hi : (H.val &&& A.val).testBit i = false := by rw [h]; simp
  simp only [delBit, Nat.testBit_and, Nat.zero_testBit] at hi ⊢
  cases h1 : H.val.testBit i <;> cases h2 : A.val.testBit i <;> simp_all

private lemma disj_not_both (H A : Fin 512) (v : Fin 9) :
    (H.val &&& A.val) = 0 → H.val.testBit v.val = true → A.val.testBit v.val = false := by
  intro h hH
  have hi : (H.val &&& A.val).testBit v.val = false := by rw [h]; simp
  rw [Nat.testBit_and, hH, Bool.true_and] at hi
  exact hi

/-! ### `petFun` Semantic Lemmas -/

private lemma petFun_true_iff (H A : ℕ) (x : Fin 9 → Bool) :
    petFun H A x = true ↔
      (∃ e ∈ petEdges, H.testBit e.1.val = true ∧ H.testBit e.2.val = true ∧ x e.1 = true ∧ x e.2 = true) ∨
      (∃ v : Fin 9, A.testBit v.val = true ∧ x v = true) := by
  simp [petFun, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, and_assoc]

private lemma petFun_canon (H A : ℕ) (hH : H < 512) (x : Fin 9 → Bool) :
    petFun (canonH H) A x = petFun H A x := by
  rw [Bool.eq_iff_iff, petFun_true_iff, petFun_true_iff]
  constructor
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | hA)
    · left
      rw [canonH_testBit ⟨H, hH⟩ e.1] at h1
      rw [canonH_testBit ⟨H, hH⟩ e.2] at h2
      simp only [Bool.and_eq_true] at h1 h2
      exact ⟨e, he, h1.1, h2.1, hx1, hx2⟩
    · exact Or.inr hA
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | hA)
    · left
      have hnbr1 : (nbrMask e.1.val).testBit e.2.val = true := by
        rw [← petEdges_iff_nbr e.1 e.2, List.any_eq_true]
        exact ⟨e, he, by simp⟩
      have hnbr2 : (nbrMask e.2.val).testBit e.1.val = true := by
        rw [← petEdges_iff_nbr e.2 e.1, List.any_eq_true]
        exact ⟨e, he, by simp⟩
      refine ⟨e, he, ?_, ?_, hx1, hx2⟩
      · rw [canonH_testBit ⟨H, hH⟩ e.1, Bool.and_eq_true]
        exact ⟨h1, List.any_eq_true.mpr ⟨e.2, List.mem_finRange _, by simp [h2, hnbr1]⟩⟩
      · rw [canonH_testBit ⟨H, hH⟩ e.2, Bool.and_eq_true]
        exact ⟨h2, List.any_eq_true.mpr ⟨e.1, List.mem_finRange _, by simp [h1, hnbr2]⟩⟩
    · exact Or.inr hA

private lemma petFun_update_false (H A : ℕ) (hH : H < 512) (hA : A < 512) (v : Fin 9) (x : Fin 9 → Bool) :
    petFun H A (Function.update x v false) = petFun (canonH (delBit H v.val)) (delBit A v.val) x := by
  rw [petFun_canon (delBit H v.val) (delBit A v.val) (delBit_lt ⟨H, hH⟩ v) x]
  rw [Bool.eq_iff_iff, petFun_true_iff, petFun_true_iff]
  constructor
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | ⟨w, hw, hxw⟩)
    · left
      have hne1 : e.1 ≠ v := by intro h; subst h; simp at hx1
      have hne2 : e.2 ≠ v := by intro h; subst h; simp at hx2
      rw [Function.update_of_ne hne1] at hx1
      rw [Function.update_of_ne hne2] at hx2
      refine ⟨e, he, ?_, ?_, hx1, hx2⟩
      · rw [delBit_testBit ⟨H, hH⟩ v e.1]; simp [h1, hne1]
      · rw [delBit_testBit ⟨H, hH⟩ v e.2]; simp [h2, hne2]
    · right
      have hne : w ≠ v := by intro h; subst h; simp at hxw
      rw [Function.update_of_ne hne] at hxw
      exact ⟨w, by rw [delBit_testBit ⟨A, hA⟩ v w]; simp [hw, hne], hxw⟩
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | ⟨w, hw, hxw⟩)
    · left
      rw [delBit_testBit ⟨H, hH⟩ v e.1, Bool.and_eq_true, bne_iff_ne] at h1
      rw [delBit_testBit ⟨H, hH⟩ v e.2, Bool.and_eq_true, bne_iff_ne] at h2
      refine ⟨e, he, h1.1, h2.1, ?_, ?_⟩
      · rw [Function.update_of_ne h1.2]; exact hx1
      · rw [Function.update_of_ne h2.2]; exact hx2
    · right
      rw [delBit_testBit ⟨A, hA⟩ v w, Bool.and_eq_true, bne_iff_ne] at hw
      exact ⟨w, hw.1, by rw [Function.update_of_ne hw.2]; exact hxw⟩

private lemma petFun_update_true_A0 (H : ℕ) (hH : H < 512) (v : Fin 9) (x : Fin 9 → Bool) :
    petFun H 0 (Function.update x v true) =
      petFun (restrictHA H v.val true).1 (restrictHA H v.val true).2 x := by
  rw [Bool.eq_iff_iff, petFun_true_iff, petFun_true_iff]
  constructor
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | ⟨w, hw, _⟩)
    · have hnbr12 : (nbrMask e.1.val).testBit e.2.val = true := by
        rw [← petEdges_iff_nbr e.1 e.2, List.any_eq_true]; exact ⟨e, he, by simp⟩
      have hnbr21 : (nbrMask e.2.val).testBit e.1.val = true := by
        rw [← petEdges_iff_nbr e.2 e.1, List.any_eq_true]; exact ⟨e, he, by simp⟩
      by_cases h1v : e.1 = v
      · subst h1v
        have h2ne : e.2 ≠ e.1 := fun h => by rw [h, nbrMask_irrefl] at hnbr12; simp at hnbr12
        rw [Function.update_of_ne h2ne] at hx2
        right
        refine ⟨e.2, ?_, hx2⟩
        rw [restrictHA_true_bits ⟨H, hH⟩ e.1 e.2]
        simp [h1, h2, hnbr12]
      · by_cases h2v : e.2 = v
        · subst h2v
          rw [Function.update_of_ne h1v] at hx1
          right
          refine ⟨e.1, ?_, hx1⟩
          rw [restrictHA_true_bits ⟨H, hH⟩ e.2 e.1]
          simp [h1, h2, hnbr21]
        · rw [Function.update_of_ne h1v] at hx1
          rw [Function.update_of_ne h2v] at hx2
          by_cases ha1 : (restrictHA H v.val true).2.testBit e.1.val = true
          · exact Or.inr ⟨e.1, ha1, hx1⟩
          · by_cases ha2 : (restrictHA H v.val true).2.testBit e.2.val = true
            · exact Or.inr ⟨e.2, ha2, hx2⟩
            · have ha1f : (restrictHA H v.val true).2.testBit e.1.val = false := by
                cases h : (restrictHA H v.val true).2.testBit e.1.val <;> simp_all
              have ha2f : (restrictHA H v.val true).2.testBit e.2.val = false := by
                cases h : (restrictHA H v.val true).2.testBit e.2.val <;> simp_all
              have hboth := restrictHA_true_H1_bit ⟨H, hH⟩ v e.1 e.2 hnbr12 h1 h2 h1v h2v ha1f ha2f
              exact Or.inl ⟨e, he, hboth.1, hboth.2, hx1, hx2⟩
    · simp at hw
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | ⟨w, hw, hxw⟩)
    · have hs1 := restrictHA_true_H1_sub ⟨H, hH⟩ v e.1 h1
      have hs2 := restrictHA_true_H1_sub ⟨H, hH⟩ v e.2 h2
      left
      refine ⟨e, he, hs1.1, hs2.1, ?_, ?_⟩
      · rw [Function.update_of_ne hs1.2]; exact hx1
      · rw [Function.update_of_ne hs2.2]; exact hx2
    · rw [restrictHA_true_bits ⟨H, hH⟩ v w, Bool.and_eq_true, Bool.and_eq_true] at hw
      rcases hw with ⟨⟨hHv, hHw⟩, hnbr⟩
      rw [← petEdges_iff_nbr v w, List.any_eq_true] at hnbr
      rcases hnbr with ⟨e, he, hmatch⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmatch
      left
      rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hne : e.2 ≠ e.1 := fun h => by
          have h1 : (petEdges.any fun e' => (e'.1 == e.1 && e'.2 == e.1) || (e'.1 == e.1 && e'.2 == e.1)) = true :=
            List.any_eq_true.mpr ⟨e, he, by simp [h]⟩
          rw [petEdges_iff_nbr, nbrMask_irrefl] at h1; simp at h1
        exact ⟨e, he, hHv, hHw, by simp, by rw [Function.update_of_ne hne]; exact hxw⟩
      · have hne : e.1 ≠ e.2 := fun h => by
          have h1 : (petEdges.any fun e' => (e'.1 == e.2 && e'.2 == e.2) || (e'.1 == e.2 && e'.2 == e.2)) = true :=
            List.any_eq_true.mpr ⟨e, he, by simp [h]⟩
          rw [petEdges_iff_nbr, nbrMask_irrefl] at h1; simp at h1
        exact ⟨e, he, hHw, hHv, by rw [Function.update_of_ne hne]; exact hxw, by simp⟩

private lemma petFun_update_restrictHA (H : ℕ) (hH : H < 512) (v : Fin 9) (val : Bool) (x : Fin 9 → Bool) :
    petFun H 0 (Function.update x v val) =
      petFun (restrictHA H v.val val).1 (restrictHA H v.val val).2 x := by
  cases val
  · simpa [restrictHA, delBit] using petFun_update_false H 0 hH (by omega) v x
  · exact petFun_update_true_A0 H hH v x

private lemma petFun_essential (H A : ℕ) (hH : H < 512) (hA : A < 512)
    (hcanon : canonH H = H) (hdisj : (H &&& A) = 0) (v : Fin 9)
    (hmem : H.testBit v.val = true ∨ A.testBit v.val = true) :
    ∃ x : Fin 9 → Bool, petFun H A (Function.update x v false) ≠ petFun H A (Function.update x v true) := by
  rcases hmem with hHv | hAv
  · have hcv : (canonH H).testBit v.val = true := by rw [hcanon]; exact hHv
    rw [canonH_testBit ⟨H, hH⟩ v, Bool.and_eq_true, List.any_eq_true] at hcv
    rcases hcv.2 with ⟨w, _, hwn⟩
    simp only [Bool.and_eq_true] at hwn
    rcases hwn with ⟨hHw, hnbr⟩
    have hne : w ≠ v := fun h => by rw [h, nbrMask_irrefl] at hnbr; simp at hnbr
    let x : Fin 9 → Bool := fun i => decide (i = w)
    refine ⟨x, ?_⟩
    have h0 : petFun H A (Function.update x v false) = false := by
      cases hval : petFun H A (Function.update x v false)
      · rfl
      · rw [petFun_true_iff] at hval
        rcases hval with ⟨e, he, _, _, hx1, hx2⟩ | ⟨z, hAz, hxz⟩
        · have he1 : e.1 = w := by
            by_cases h1v : e.1 = v
            · subst h1v; simp at hx1
            · rw [Function.update_of_ne h1v] at hx1; simpa [x] using hx1
          have he2 : e.2 = w := by
            by_cases h2v : e.2 = v
            · subst h2v; simp at hx2
            · rw [Function.update_of_ne h2v] at hx2; simpa [x] using hx2
          have := nbrMask_irrefl w
          rw [← petEdges_iff_nbr w w] at this
          have ht : (petEdges.any fun e => (e.1 == w && e.2 == w) || (e.1 == w && e.2 == w)) = true :=
            List.any_eq_true.mpr ⟨e, he, by simp [he1, he2]⟩
          rw [ht] at this; simp at this
        · have hzw : z = w := by
            by_cases hzv : z = v
            · subst hzv; simp at hxz
            · rw [Function.update_of_ne hzv] at hxz; simpa [x] using hxz
          subst hzw
          have := disj_not_both ⟨H, hH⟩ ⟨A, hA⟩ z hdisj hHw
          rw [this] at hAz; simp at hAz
    have h1 : petFun H A (Function.update x v true) = true := by
      rw [petFun_true_iff]; left
      rw [← petEdges_iff_nbr v w, List.any_eq_true] at hnbr
      rcases hnbr with ⟨e, he, hmatch⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmatch
      rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨e, he, hHv, hHw, by simp, by rw [Function.update_of_ne hne]; simp [x]⟩
      · exact ⟨e, he, hHw, hHv, by rw [Function.update_of_ne hne]; simp [x], by simp⟩
    rw [h0, h1]; decide
  · refine ⟨fun _ => false, ?_⟩
    have h0 : petFun H A (Function.update (fun _ => false) v false) = false := by
      cases hval : petFun H A (Function.update (fun _ => false) v false)
      · rfl
      · rw [petFun_true_iff] at hval
        rcases hval with ⟨e, _, _, _, hx1, _⟩ | ⟨z, _, hxz⟩
        · by_cases h : e.1 = v <;> simp [h] at hx1
        · by_cases h : z = v <;> simp [h] at hxz
    have h1 : petFun H A (Function.update (fun _ => false) v true) = true := by
      rw [petFun_true_iff]; right
      exact ⟨v, hAv, by simp⟩
    rw [h0, h1]; decide

private lemma petFun_nonconst (H A : ℕ) (hH : H < 512) (hA : A < 512)
    (hcanon : canonH H = H) (hdisj : (H &&& A) = 0) (hne : H ≠ 0 ∨ A ≠ 0) :
    ∃ x y : Fin 9 → Bool, petFun H A x ≠ petFun H A y := by
  have hv : ∃ v : Fin 9, H.testBit v.val = true ∨ A.testBit v.val = true := by
    rcases hne with hHne | hAne
    · obtain ⟨v, _, hv⟩ := List.any_eq_true.mp (exists_bit_decide ⟨H, hH⟩ hHne)
      exact ⟨v, Or.inl hv⟩
    · obtain ⟨v, _, hv⟩ := List.any_eq_true.mp (exists_bit_decide ⟨A, hA⟩ hAne)
      exact ⟨v, Or.inr hv⟩
  rcases hv with ⟨v, hmem⟩
  obtain ⟨x, hx⟩ := petFun_essential H A hH hA hcanon hdisj v hmem
  exact ⟨Function.update x v false, Function.update x v true, hx⟩

private lemma petFun_indep_of_not_mem (H : ℕ) (v : Fin 9) (hnot : H.testBit v.val = false)
    (x : Fin 9 → Bool) :
    petFun H 0 (Function.update x v false) = petFun H 0 x := by
  rw [Bool.eq_iff_iff, petFun_true_iff, petFun_true_iff]
  constructor
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | ⟨w, hw, _⟩)
    · have hne1 : e.1 ≠ v := fun h => by rw [h, hnot] at h1; simp at h1
      have hne2 : e.2 ≠ v := fun h => by rw [h, hnot] at h2; simp at h2
      rw [Function.update_of_ne hne1] at hx1
      rw [Function.update_of_ne hne2] at hx2
      exact Or.inl ⟨e, he, h1, h2, hx1, hx2⟩
    · simp at hw
  · rintro (⟨e, he, h1, h2, hx1, hx2⟩ | ⟨w, hw, _⟩)
    · have hne1 : e.1 ≠ v := fun h => by rw [h, hnot] at h1; simp at h1
      have hne2 : e.2 ≠ v := fun h => by rw [h, hnot] at h2; simp at h2
      exact Or.inl ⟨e, he, h1, h2, by rw [Function.update_of_ne hne1]; exact hx1,
        by rw [Function.update_of_ne hne2]; exact hx2⟩
    · simp at hw

private lemma not_out_input_of_other_essential {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hev : ∀ x, u2Eval D x = f x) (v w : Fin 9) (hne : w ≠ v)
    (hess : ∃ x : Fin 9 → Bool, f (Function.update x w false) ≠ f (Function.update x w true)) :
    ∀ fl, D.out ≠ Sum.inr (v.val, fl) := by
  intro fl hout
  obtain ⟨x, hx⟩ := hess
  apply hx
  rw [← hev, ← hev]
  unfold u2Eval
  rw [hout]
  simp only [refEval]
  have h1 : (u2Wires D.gates (List.ofFn (Function.update x w false))).getD v.val false =
      (Function.update x w false) v := u2Val_input D.gates _ v.val v.isLt
  have h2 : (u2Wires D.gates (List.ofFn (Function.update x w true))).getD v.val false =
      (Function.update x w true) v := u2Val_input D.gates _ v.val v.isLt
  rw [h1, h2, Function.update_of_ne hne.symm, Function.update_of_ne hne.symm]

private lemma min_has_gate_reader_of_essential {f : (Fin 9 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (v : Fin 9)
    (hess : ∃ x : Fin 9 → Bool, f (Function.update x v false) ≠ f (Function.update x v true))
    (hout : ∀ fl, D.out ≠ Sum.inr (v.val, fl)) :
    ∃ j, ∃ (_ : j < D.gates.length), D.gates[j].a = v.val ∨ D.gates[j].b = v.val := by
  have hslot : v.val ∈ u2Slots D := essential_mem_u2Slots hmin.2.1 v (by
    obtain ⟨x, hx⟩ := hess
    refine ⟨Function.update x v false, Function.update x v true, ?_, hx⟩
    intro i hi; simp [Function.update_of_ne hi])
  unfold u2Slots at hslot
  rw [List.mem_append] at hslot
  rcases hslot with ho | hg
  · rcases h : D.out with c | ⟨w, fl⟩
    · rw [h] at ho; simp at ho
    · rw [h] at ho; simp only [List.mem_singleton] at ho
      exact (hout fl (by rw [h, ho])).elim
  · rw [List.mem_flatMap] at hg
    rcases hg with ⟨g, hgmem, hgin⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgin
    exact ⟨j, hj, hgin.imp Eq.symm Eq.symm⟩

private lemma min_gate_input_mem_H (H : ℕ) (D : U2Circuit) (hmin : IsMinU2 (petFun H 0) D)
    (j : ℕ) (hj : j < D.gates.length) (v : Fin 9)
    (hread : D.gates[j].a = v.val ∨ D.gates[j].b = v.val) :
    H.testBit v.val = true := by
  cases h : H.testBit v.val
  · exfalso
    obtain ⟨s', hs'le, hs'⟩ := elim_ge_1 hmin v false j hj hread
    rcases hs' with ⟨D', hwf', hlen', hev'⟩
    have hminle := hmin.2.2 D' hwf' (fun x => (hev' x).trans (petFun_indep_of_not_mem H v h x))
    omega
  · rfl

/-! ### `A`-Peeling Lemma -/

private lemma peelA_bound (H : ℕ) (hH : H < 512) (hcanon : canonH H = H)
    (b : ℕ) (hb : H ≠ 0 → ∀ s', HasU2Size (petFun H 0) s' → b ≤ s') :
    ∀ k A, A < 512 → (H &&& A) = 0 → pop9 A = k →
      ∀ s, HasU2Size (petFun H A) s →
        (if H = 0 then k - 1 else k + b) ≤ s := by
  intro k
  induction k with
  | zero =>
    intro A hA _ hk s hs
    have hA0 : A = 0 := (pop9_zero_iff ⟨A, hA⟩).mp hk
    subst hA0
    by_cases hH0 : H = 0
    · simp [hH0]
    · simp only [hH0, ↓reduceIte, Nat.zero_add]
      exact hb hH0 s hs
  | succ k ih =>
    intro A hA hdisj hk s hs
    obtain ⟨D, hmin, hDs⟩ := exists_minU2 hs
    by_cases hH0 : H = 0
    · subst hH0
      simp only [↓reduceIte]
      let S : Finset (Fin 9) := Finset.univ.filter fun v : Fin 9 => A.testBit v.val = true
      have hScard : S.card = k + 1 := by rw [← pop9_eq_card A hA, hk]
      have hS : ∀ v ∈ S, ∃ x y : Fin 9 → Bool, (∀ i, i ≠ v → x i = y i) ∧ petFun 0 A x ≠ petFun 0 A y := by
        intro v hv
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨x, hx⟩ := petFun_essential 0 A (by omega) hA rfl (by simp) v (Or.inr hv)
        exact ⟨Function.update x v false, Function.update x v true, fun i hi => by simp [Function.update_of_ne hi], hx⟩
      have hslot := slot_lower_bound hmin S hS
      omega
    · simp only [hH0, ↓reduceIte]
      have hAne : A ≠ 0 := fun h => by rw [h] at hk; simp [pop9] at hk
      obtain ⟨v, _, hAv⟩ := List.any_eq_true.mp (exists_bit_decide ⟨A, hA⟩ hAne)
      obtain ⟨u, _, hHu⟩ := List.any_eq_true.mp (exists_bit_decide ⟨H, hH⟩ hH0)
      have huv : u ≠ v := fun h => by
        subst h
        have := disj_not_both ⟨H, hH⟩ ⟨A, hA⟩ u hdisj hHu
        rw [this] at hAv; simp at hAv
      have hess_v := petFun_essential H A hH hA hcanon hdisj v (Or.inr hAv)
      have hess_u := petFun_essential H A hH hA hcanon hdisj u (Or.inl hHu)
      have hout := not_out_input_of_other_essential hmin.2.1 v u huv hess_u
      obtain ⟨j, hj, hread⟩ := min_has_gate_reader_of_essential hmin v hess_v hout
      obtain ⟨s', hs'le, hs'⟩ := elim_ge_1 hmin v false j hj hread
      have hdel_eq : (fun x => petFun H A (Function.update x v false)) =
          petFun H (delBit A v.val) := by
        funext x
        rw [petFun_update_false H A hH hA v x]
        have hHv_f : H.testBit v.val = false := by
          cases h : H.testBit v.val
          · rfl
          · have := disj_not_both ⟨H, hH⟩ ⟨A, hA⟩ v hdisj h
            rw [this] at hAv; simp at hAv
        have hdelH : canonH (delBit H v.val) = H := by
          have hdec : allPow2 9 0 (fun m => (List.finRange 9).all fun w =>
              decide (canonH m ≠ m) || m.testBit w.val || decide (canonH (delBit m w.val) = m)) = true := by decide
          have h1 := List.all_eq_true.mp (all512_true _ hdec H hH) v (List.mem_finRange v)
          simpa [hcanon, hHv_f] using h1
        rw [hdelH]
      rw [hdel_eq] at hs'
      have hpop' : pop9 (delBit A v.val) = k := by
        have hdp := delBit_pop9 ⟨A, hA⟩ v hAv
        dsimp only at hdp; omega
      have hih := ih (delBit A v.val) (delBit_lt ⟨A, hA⟩ v) (disj_delBit ⟨H, hH⟩ ⟨A, hA⟩ v hdisj) hpop' s' hs'
      simp only [hH0, ↓reduceIte] at hih
      omega

/-! ### Decidable Recurrence Checker `checkAll` -/

private def vOk (H t v : ℕ) (pv : Bool) (u : ℕ) (pu : Bool) : Bool :=
  let r0p := restrictHA H v false
  let r1p := restrictHA H v true
  let r0 := dpValHA r0p.1 r0p.2
  let r1 := dpValHA r1p.1 r1p.2
  let nc0 := r0p.1 != 0
  let rup := restrictHA H u pu
  let can1 := !(rup.1.testBit v) && !(rup.2.testBit v)
  let ok0 := !can1 ||
    (if !pv then decide (t ≤ (if nc0 then 2 else 1) + r0) || decide (t ≤ 1 + r1)
     else decide (t ≤ 1 + r0) || decide (t ≤ 2 + r1))
  let ok1 :=
    if !pv then decide (t ≤ (if nc0 then 4 else 2) + r0) || decide (t ≤ 2 + r1)
    else decide (t ≤ 2 + r0) || decide (t ≤ 4 + r1)
  let ok2 := decide (t ≤ (if nc0 then 3 else 2) + r0) || decide (t ≤ 3 + r1)
  ok0 && ok1 && ok2

private def checkPair (H t a b : ℕ) : Bool :=
  ([false, true]).all fun pa =>
    ([false, true]).all fun pb =>
      vOk H t a pa b pb || vOk H t b pb a pa

private def checkState (H : ℕ) : Bool :=
  let t := dpVal H
  if pop9 H < 3 then
    decide (t ≤ pop9 H - 1)
  else
    decide (t ≤ pop9 H - 1) ||
    ((List.range 9).any fun v =>
      H.testBit v &&
      let r0p := restrictHA H v false
      let r1p := restrictHA H v true
      let b0 := (if r0p.1 != 0 then 2 else 1) + dpValHA r0p.1 r0p.2
      let b1 := 2 + dpValHA r1p.1 r1p.2
      decide (t ≤ b0) && decide (t ≤ b1)) ||
    ((List.range 9).all fun a =>
      if !H.testBit a then true
      else (List.range 9).all fun b =>
        if !(decide (a < b) && H.testBit b) then true
        else checkPair H t a b)

private def checkAll : Bool :=
  allPow2 9 0 fun H =>
    if canonH H == H then checkState H else true

private lemma checkAll_true : checkAll = true := by decide

private lemma dpVal_511 : dpVal 511 = 13 := by decide

/-! ### Soundness of `checkAll` via Strong Induction on `pop9 H` -/

private lemma restrictHA_bound {H : ℕ} (hH : H < 512)
    (ih : ∀ H', H' < 512 → canonH H' = H' → pop9 H' < pop9 H →
      ∀ s', HasU2Size (petFun H' 0) s' → dpVal H' ≤ s')
    (v : Fin 9) (hv : H.testBit v.val = true) (val : Bool)
    {s' : ℕ} (hs' : HasU2Size (fun x => petFun H 0 (Function.update x v val)) s') :
    dpValHA (restrictHA H v.val val).1 (restrictHA H v.val val).2 ≤ s' := by
  have hrp := restrictHA_props ⟨H, hH⟩ v val
  rcases hrp with ⟨hr1_lt, hr2_lt, hr1_can, hr_disj, hr_pop, _⟩
  have heq : (fun x => petFun H 0 (Function.update x v val)) =
      petFun (restrictHA H v.val val).1 (restrictHA H v.val val).2 := by
    funext x; exact petFun_update_restrictHA H hH v val x
  rw [heq] at hs'
  have hpeel := peelA_bound (restrictHA H v.val val).1 hr1_lt hr1_can
    (dpVal (restrictHA H v.val val).1)
    (fun _ s0 hs0 => ih _ hr1_lt hr1_can (hr_pop hv) s0 hs0)
    (pop9 (restrictHA H v.val val).2) (restrictHA H v.val val).2 hr2_lt hr_disj rfl s' hs'
  unfold dpValHA
  rw [hr1_can]
  exact hpeel

private lemma first_gate_var_bound {H : ℕ} (hH : H < 512) (hcanon : canonH H = H)
    (hpop : 3 ≤ pop9 H)
    (ih : ∀ H', H' < 512 → canonH H' = H' → pop9 H' < pop9 H →
      ∀ s', HasU2Size (petFun H' 0) s' → dpVal H' ≤ s')
    {D : U2Circuit} (hmin : IsMinU2 (petFun H 0) D) (h0 : 0 < D.gates.length)
    (v u : Fin 9) (pv pu : Bool) (hvu : v ≠ u)
    (hvH : H.testBit v.val = true)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = pv) ∨ (D.gates[0].b = v.val ∧ D.gates[0].pb = pv))
    (hg0 : ∀ x : Fin 9 → Bool, u2Val D.gates x 9 = ((u2Val D.gates x v.val != pv) && (u2Val D.gates x u.val != pu)))
    (t : ℕ) (hvok : vOk H t v.val pv u.val pu = true) :
    t ≤ D.gates.length := by
  have hr0_any : D.gates[0].a = v.val ∨ D.gates[0].b = v.val :=
    hr0.imp And.left And.left
  have hrp0 := restrictHA_props ⟨H, hH⟩ v false
  have hrp1 := restrictHA_props ⟨H, hH⟩ v true
  have hnc1 : ∃ x y : Fin 9 → Bool,
      petFun H 0 (Function.update x v true) ≠ petFun H 0 (Function.update y v true) := by
    have hA1ne : (restrictHA H v.val true).2 ≠ 0 := hrp1.2.2.2.2.2 hcanon hvH rfl
    obtain ⟨x, y, hxy⟩ := petFun_nonconst _ _ hrp1.1 hrp1.2.1 hrp1.2.2.1 hrp1.2.2.2.1 (Or.inr hA1ne)
    exact ⟨x, y, by rw [petFun_update_restrictHA H hH v true x, petFun_update_restrictHA H hH v true y]; exact hxy⟩
  have hnc0_of : (restrictHA H v.val false).1 ≠ 0 →
      ∃ x y : Fin 9 → Bool,
        petFun H 0 (Function.update x v false) ≠ petFun H 0 (Function.update y v false) := by
    intro hne
    obtain ⟨x, y, hxy⟩ := petFun_nonconst _ _ hrp0.1 hrp0.2.1 hrp0.2.2.1 hrp0.2.2.2.1 (Or.inl hne)
    exact ⟨x, y, by rw [petFun_update_restrictHA H hH v false x, petFun_update_restrictHA H hH v false y]; exact hxy⟩
  have hbound : ∀ val : Bool, ∀ k : ℕ,
      (∃ s', s' + k ≤ D.gates.length ∧ HasU2Size (fun x => petFun H 0 (Function.update x v val)) s') →
      k + dpValHA (restrictHA H v.val val).1 (restrictHA H v.val val).2 ≤ D.gates.length := by
    rintro val k ⟨s', hs'le, hs'⟩
    have := restrictHA_bound hH ih v hvH val hs'
    omega
  unfold vOk at hvok
  simp only [Bool.and_eq_true] at hvok
  rcases hvok with ⟨⟨hok0, hok1⟩, hok2⟩
  -- Case split on whether v has a second reader j1 > 0
  by_cases h2nd : ∃ j1, ∃ (_ : j1 < D.gates.length), 0 < j1 ∧ (D.gates[j1].a = v.val ∨ D.gates[j1].b = v.val)
  · rcases h2nd with ⟨j1, hj1, hj1_pos, hr1_any⟩
    have hpol : ((D.gates[j1].a = v.val ∧ D.gates[j1].pa = pv) ∨ (D.gates[j1].b = v.val ∧ D.gates[j1].pb = pv)) ∨
        ((D.gates[j1].a = v.val ∧ D.gates[j1].pa = !pv) ∨ (D.gates[j1].b = v.val ∧ D.gates[j1].pb = !pv)) := by
      rcases hr1_any with ha | hb
      · cases hpa : D.gates[j1].pa <;> cases pv <;> simp [ha]
      · cases hpb : D.gates[j1].pb <;> cases pv <;> simp [hb]
    rcases hpol with hsame | hopp
    · -- Mode 1: same polarity pv
      have h2_0 := hbound false 2 (elim_ge_2_two hmin v false 0 j1 h0 hj1 (by omega) hr0_any hr1_any)
      have h2_1 := hbound true 2 (elim_ge_2_two hmin v true 0 j1 h0 hj1 (by omega) hr0_any hr1_any)
      cases pv
      · simp only [Bool.not_false, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hok1
        rcases hok1 with h0b | h1b
        · by_cases hne0 : (restrictHA H v.val false).1 ≠ 0
          · have hne0b : ((restrictHA H v.val false).1 != 0) = true := bne_iff_ne.mpr hne0
            simp only [hne0b, ↓reduceIte] at h0b
            have h4 := hbound false 4 (elim_ge_4_same hmin h0 v false hr0 j1 hj1 hj1_pos hsame (hnc0_of hne0))
            omega
          · push Not at hne0
            have hne0b : ((restrictHA H v.val false).1 != 0) = false := by simp [hne0]
            simp only [hne0b, Bool.false_eq_true, ↓reduceIte] at h0b
            omega
        · omega
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hok1
        rcases hok1 with h0b | h1b
        · omega
        · have h4 := hbound true 4 (elim_ge_4_same hmin h0 v true hr0 j1 hj1 hj1_pos hsame hnc1)
          omega
    · -- Mode 2: opposite polarity !pv
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hok2
      rcases hok2 with h0b | h1b
      · by_cases hne0 : (restrictHA H v.val false).1 ≠ 0
        · have hne0b : ((restrictHA H v.val false).1 != 0) = true := bne_iff_ne.mpr hne0
          simp only [hne0b, ↓reduceIte] at h0b
          have h3 := hbound false 3 (elim_ge_3_opp hmin h0 v pv hr0 j1 hj1 hj1_pos hopp false (hnc0_of hne0))
          omega
        · push Not at hne0
          have hne0b : ((restrictHA H v.val false).1 != 0) = false := by simp [hne0]
          simp only [hne0b, Bool.false_eq_true, ↓reduceIte] at h0b
          have h2 := hbound false 2 (elim_ge_2_two hmin v false 0 j1 h0 hj1 (by omega) hr0_any hr1_any)
          omega
      · have h3 := hbound true 3 (elim_ge_3_opp hmin h0 v pv hr0 j1 hj1 hj1_pos hopp true hnc1)
        omega
  · -- Mode 0: v has fan-out 1 (only gate 0 reads v)
    push Not at h2nd
    -- Prove D.out ≠ Sum.inr (v, fl) since pop9 H ≥ 3 gives another essential variable w ≠ v
    obtain ⟨w, _, hwm⟩ := List.any_eq_true.mp (exists_other_bit_decide ⟨H, hH⟩ v (by dsimp only; omega))
    simp only [Bool.and_eq_true, bne_iff_ne] at hwm
    have hess_w := petFun_essential H 0 hH (by omega) hcanon (by simp) w (Or.inl hwm.2)
    have hout := not_out_input_of_other_essential hmin.2.1 v w hwm.1 hess_w
    have hsf := single_fanout_first_gate hmin h0 v u pv pu hvu hg0 hout h2nd
    -- Show can1 = true!
    have hru := restrictHA_props ⟨H, hH⟩ u pu
    have hcan1 : (!((restrictHA H u.val pu).1.testBit v.val) &&
        !((restrictHA H u.val pu).2.testBit v.val)) = true := by
      have hv1 : (restrictHA H u.val pu).1.testBit v.val = false := by
        cases h : (restrictHA H u.val pu).1.testBit v.val
        · rfl
        · exfalso
          obtain ⟨x, hx⟩ := petFun_essential _ _ hru.1 hru.2.1 hru.2.2.1 hru.2.2.2.1 v (Or.inl h)
          apply hx
          rw [← petFun_update_restrictHA H hH u pu (Function.update x v false),
              ← petFun_update_restrictHA H hH u pu (Function.update x v true),
              Function.update_comm hvu, Function.update_comm hvu]
          exact hsf x
      have hv2 : (restrictHA H u.val pu).2.testBit v.val = false := by
        cases h : (restrictHA H u.val pu).2.testBit v.val
        · rfl
        · exfalso
          obtain ⟨x, hx⟩ := petFun_essential _ _ hru.1 hru.2.1 hru.2.2.1 hru.2.2.2.1 v (Or.inr h)
          apply hx
          rw [← petFun_update_restrictHA H hH u pu (Function.update x v false),
              ← petFun_update_restrictHA H hH u pu (Function.update x v true),
              Function.update_comm hvu, Function.update_comm hvu]
          exact hsf x
      simp [hv1, hv2]
    rw [hcan1] at hok0
    simp only [Bool.not_true, Bool.false_or] at hok0
    have h1_0 := hbound false 1 (elim_ge_1 hmin v false 0 h0 hr0_any)
    have h1_1 := hbound true 1 (elim_ge_1 hmin v true 0 h0 hr0_any)
    cases pv
    · simp only [Bool.not_false, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hok0
      rcases hok0 with h0b | h1b
      · by_cases hne0 : (restrictHA H v.val false).1 ≠ 0
        · have hne0b : ((restrictHA H v.val false).1 != 0) = true := bne_iff_ne.mpr hne0
          simp only [hne0b, ↓reduceIte] at h0b
          have h2 := hbound false 2 (elim_ge_2_ctrl hmin v false (hnc0_of hne0) 0 h0 hr0)
          omega
        · push Not at hne0
          have hne0b : ((restrictHA H v.val false).1 != 0) = false := by simp [hne0]
          simp only [hne0b, Bool.false_eq_true, ↓reduceIte] at h0b
          omega
      · omega
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hok0
      rcases hok0 with h0b | h1b
      · omega
      · have h2 := hbound true 2 (elim_ge_2_ctrl hmin v true hnc1 0 h0 hr0)
        omega

private lemma dp_sound :
    ∀ k H, H < 512 → canonH H = H → pop9 H = k →
      ∀ s, HasU2Size (petFun H 0) s → dpVal H ≤ s := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih_k =>
    intro H hH hcanon hpop s hs
    have ih : ∀ H', H' < 512 → canonH H' = H' → pop9 H' < pop9 H →
        ∀ s', HasU2Size (petFun H' 0) s' → dpVal H' ≤ s' :=
      fun H' hH' hc' hp' s' hs' => ih_k (pop9 H') (by omega) H' hH' hc' rfl s' hs'
    have hchk : checkState H = true := by
      have h := all512_true _ checkAll_true H hH
      simpa [hcanon] using h
    obtain ⟨D, hmin, hDs⟩ := exists_minU2 hs
    -- Slot lower bound holds for all canonical H
    have hslot_H : pop9 H - 1 ≤ D.gates.length := by
      let S : Finset (Fin 9) := Finset.univ.filter fun v : Fin 9 => H.testBit v.val = true
      have hScard : S.card = pop9 H := (pop9_eq_card H hH).symm
      have hS : ∀ v ∈ S, ∃ x y : Fin 9 → Bool, (∀ i, i ≠ v → x i = y i) ∧ petFun H 0 x ≠ petFun H 0 y := by
        intro v hv
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨x, hx⟩ := petFun_essential H 0 hH (by omega) hcanon (by simp) v (Or.inl hv)
        exact ⟨Function.update x v false, Function.update x v true, fun i hi => by simp [Function.update_of_ne hi], hx⟩
      have := slot_lower_bound hmin S hS
      omega
    unfold checkState at hchk
    by_cases hsmall : pop9 H < 3
    · simp only [hsmall, ↓reduceIte, decide_eq_true_eq] at hchk
      omega
    · simp only [hsmall, ↓reduceIte, Bool.or_eq_true] at hchk
      rcases hchk with (hsl | huniv) | hfg
      · simp only [decide_eq_true_eq] at hsl; omega
      · -- Universal single-variable bound
        rw [List.any_eq_true] at huniv
        rcases huniv with ⟨v_nat, hv_rng, hvb⟩
        rw [List.mem_range] at hv_rng
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hvb
        rcases hvb with ⟨hvH, hb0, hb1⟩
        let v : Fin 9 := ⟨v_nat, hv_rng⟩
        obtain ⟨w, _, hwm⟩ := List.any_eq_true.mp (exists_other_bit_decide ⟨H, hH⟩ v (by dsimp only; omega))
        simp only [Bool.and_eq_true, bne_iff_ne] at hwm
        have hess_v := petFun_essential H 0 hH (by omega) hcanon (by simp) v (Or.inl hvH)
        have hess_w := petFun_essential H 0 hH (by omega) hcanon (by simp) w (Or.inl hwm.2)
        have hout := not_out_input_of_other_essential hmin.2.1 v w hwm.1 hess_w
        obtain ⟨j, hj, hread⟩ := min_has_gate_reader_of_essential hmin v hess_v hout
        have hpol : ∃ p : Bool,
            (D.gates[j].a = v.val ∧ D.gates[j].pa = p) ∨ (D.gates[j].b = v.val ∧ D.gates[j].pb = p) := by
          rcases hread with ha | hb
          · exact ⟨D.gates[j].pa, Or.inl ⟨ha, rfl⟩⟩
          · exact ⟨D.gates[j].pb, Or.inr ⟨hb, rfl⟩⟩
        rcases hpol with ⟨p, hrp⟩
        cases p
        · -- Reader has polarity false
          by_cases hne0 : (restrictHA H v_nat false).1 ≠ 0
          · have hne0b : ((restrictHA H v_nat false).1 != 0) = true := bne_iff_ne.mpr hne0
            simp only [hne0b, ↓reduceIte] at hb0
            have hr0p := restrictHA_props ⟨H, hH⟩ v false
            have hnc0 : ∃ x y : Fin 9 → Bool,
                petFun H 0 (Function.update x v false) ≠ petFun H 0 (Function.update y v false) := by
              obtain ⟨x, y, hxy⟩ := petFun_nonconst _ _ hr0p.1 hr0p.2.1 hr0p.2.2.1 hr0p.2.2.2.1 (Or.inl hne0)
              exact ⟨x, y, by rw [petFun_update_restrictHA H hH v false x, petFun_update_restrictHA H hH v false y]; exact hxy⟩
            obtain ⟨s', hs'le, hs'⟩ := elim_ge_2_ctrl hmin v false hnc0 j hj hrp
            have hrb := restrictHA_bound hH ih v hvH false hs'
            dsimp only [v] at hrb
            omega
          · push Not at hne0
            have hne0b : ((restrictHA H v_nat false).1 != 0) = false := by simp [hne0]
            simp only [hne0b, Bool.false_eq_true, ↓reduceIte] at hb0
            obtain ⟨s', hs'le, hs'⟩ := elim_ge_1 hmin v false j hj hread
            have hrb := restrictHA_bound hH ih v hvH false hs'
            dsimp only [v] at hrb
            omega
        · -- Reader has polarity true
          have hr1p := restrictHA_props ⟨H, hH⟩ v true
          have hA1ne : (restrictHA H v.val true).2 ≠ 0 := hr1p.2.2.2.2.2 hcanon hvH rfl
          have hnc1 : ∃ x y : Fin 9 → Bool,
              petFun H 0 (Function.update x v true) ≠ petFun H 0 (Function.update y v true) := by
            obtain ⟨x, y, hxy⟩ := petFun_nonconst _ _ hr1p.1 hr1p.2.1 hr1p.2.2.1 hr1p.2.2.2.1 (Or.inr hA1ne)
            exact ⟨x, y, by rw [petFun_update_restrictHA H hH v true x, petFun_update_restrictHA H hH v true y]; exact hxy⟩
          obtain ⟨s', hs'le, hs'⟩ := elim_ge_2_ctrl hmin v true hnc1 j hj hrp
          have hrb := restrictHA_bound hH ih v hvH true hs'
          dsimp only [v] at hrb
          omega
      · -- First-gate case split
        have h0 : 0 < D.gates.length := by omega
        have ha_lt : D.gates[0].a < 9 := (hmin.1.1 0 h0).1
        have hb_lt : D.gates[0].b < 9 := (hmin.1.1 0 h0).2
        have hab_ne : D.gates[0].a ≠ D.gates[0].b := min_no_self hmin 0 h0
        let a : Fin 9 := ⟨D.gates[0].a, ha_lt⟩
        let b : Fin 9 := ⟨D.gates[0].b, hb_lt⟩
        have haH : H.testBit a.val = true := min_gate_input_mem_H H D hmin 0 h0 a (Or.inl rfl)
        have hbH : H.testBit b.val = true := min_gate_input_mem_H H D hmin 0 h0 b (Or.inr rfl)
        have hg0_ab : ∀ x : Fin 9 → Bool,
            u2Val D.gates x 9 = ((u2Val D.gates x a.val != D.gates[0].pa) &&
              (u2Val D.gates x b.val != D.gates[0].pb)) := by
          intro x; simpa [a, b] using u2Val_gate D.gates x 0 h0 ha_lt hb_lt
        have hg0_ba : ∀ x : Fin 9 → Bool,
            u2Val D.gates x 9 = ((u2Val D.gates x b.val != D.gates[0].pb) &&
              (u2Val D.gates x a.val != D.gates[0].pa)) := by
          intro x; rw [hg0_ab x, Bool.and_comm]
        have hpair : checkPair H (dpVal H) (min a.val b.val) (max a.val b.val) = true := by
          have h1 := List.all_eq_true.mp hfg (min a.val b.val) (List.mem_range.mpr (by omega))
          have hminH : H.testBit (min a.val b.val) = true := by
            rcases le_total a.val b.val with hle | hle
            · rwa [Nat.min_eq_left hle]
            · rwa [Nat.min_eq_right hle]
          have hmaxH : H.testBit (max a.val b.val) = true := by
            rcases le_total a.val b.val with hle | hle
            · rwa [Nat.max_eq_right hle]
            · rwa [Nat.max_eq_left hle]
          simp only [hminH, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
          have h2 := List.all_eq_true.mp h1 (max a.val b.val) (List.mem_range.mpr (by omega))
          have hlt : min a.val b.val < max a.val b.val := by dsimp only [a, b]; omega
          simpa [hlt, hmaxH] using h2
        have hdisj_ok : vOk H (dpVal H) a.val D.gates[0].pa b.val D.gates[0].pb = true ∨
            vOk H (dpVal H) b.val D.gates[0].pb a.val D.gates[0].pa = true := by
          rcases lt_or_gt_of_ne hab_ne with hlt | hgt
          · rw [Nat.min_eq_left (Nat.le_of_lt hlt), Nat.max_eq_right (Nat.le_of_lt hlt)] at hpair
            have h1 := List.all_eq_true.mp hpair D.gates[0].pa (by cases D.gates[0].pa <;> simp)
            have h2 := List.all_eq_true.mp h1 D.gates[0].pb (by cases D.gates[0].pb <;> simp)
            simpa [Bool.or_eq_true] using h2
          · rw [Nat.min_eq_right (Nat.le_of_lt hgt), Nat.max_eq_left (Nat.le_of_lt hgt)] at hpair
            have h1 := List.all_eq_true.mp hpair D.gates[0].pb (by cases D.gates[0].pb <;> simp)
            have h2 := List.all_eq_true.mp h1 D.gates[0].pa (by cases D.gates[0].pa <;> simp)
            exact (Bool.or_eq_true _ _ |>.mp h2).symm
        rcases hdisj_ok with ha_ok | hb_ok
        · have hle := first_gate_var_bound hH hcanon (by omega) ih hmin h0 a b
            D.gates[0].pa D.gates[0].pb (fun h => hab_ne (congrArg Fin.val h)) haH
            (Or.inl ⟨rfl, rfl⟩) hg0_ab (dpVal H) ha_ok
          omega
        · have hle := first_gate_var_bound hH hcanon (by omega) ih hmin h0 b a
            D.gates[0].pb D.gates[0].pa (fun h => hab_ne (congrArg Fin.val h).symm) hbH
            (Or.inr ⟨rfl, rfl⟩) hg0_ba (dpVal H) hb_ok
          omega

private lemma petFun_511_eq (x : Fin 9 → Bool) :
    petFun 511 0 x =
      (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) ||
       x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) ||
       x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) ||
       x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) ||
       x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) ||
       x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9)) := by
  have h511 : ∀ n : ℕ, n < 9 → (511 : ℕ).testBit n = true := fun n hn => mask511_testBit ⟨n, hn⟩
  simp [petFun, petEdges, List.finRange, h511, Bool.or_assoc]


private lemma petFun_511_any (x : Fin 9 → Bool) :
    petFun 511 0 x =
      [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))),
       ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))),
       ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))),
       ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))),
       ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))),
       ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any
        fun (x4 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x x4.1 && x x4.2 := by
  have h511 : ∀ n : ℕ, n < 9 → (511 : ℕ).testBit n = true := fun n hn => mask511_testBit ⟨n, hn⟩
  simp [petFun, petEdges, List.finRange, h511]

private lemma countP_notNot_add_not (gs : List Gate) :
    List.countP PEqualNP.MetaComplexity.SingleLevel.notNot gs +
      (gs.filter fun g => decide (g.op = GateOp.not)).length = gs.length := by
  induction gs with
  | nil => simp
  | cons g rest ih =>
    cases h : g.op <;> simp [PEqualNP.MetaComplexity.SingleLevel.notNot, h] <;> omega

private lemma countP_notNot_eq (C : Circuit) :
    List.countP PEqualNP.MetaComplexity.SingleLevel.notNot C.gates =
      C.size - PEqualNP.NotBracket.notCount C := by
  have h := countP_notNot_add_not C.gates
  change List.countP PEqualNP.MetaComplexity.SingleLevel.notNot C.gates =
    C.gates.length - (C.gates.filter fun g => decide (g.op = GateOp.not)).length
  omega

end PEqualNP.Outside.L_meta_5971_aux

theorem PEqualNP.Outside.L_meta_5971 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x4 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x3 x4.1 && x3 x4.2) → (13 : ℕ) ≤ List.countP PEqualNP.MetaComplexity.SingleLevel.notNot x1.gates := by
  intro C hfan heval
  obtain ⟨hwf, hlen, hu2⟩ := PEqualNP.Outside.L_meta_5971_aux.toU2_spec C hfan
  have hs : PEqualNP.Outside.L_meta_5971_aux.HasU2Size
      (PEqualNP.Outside.L_meta_5971_aux.petFun 511 0)
      (C.size - PEqualNP.NotBracket.notCount C) := by
    refine ⟨PEqualNP.Outside.L_meta_5971_aux.toU2 C, hwf, hlen, fun x => ?_⟩
    rw [hu2 x, heval x, ← PEqualNP.Outside.L_meta_5971_aux.petFun_511_any x]
  have hdp := PEqualNP.Outside.L_meta_5971_aux.dp_sound 9 511 (by omega) (by decide) (by decide)
    (C.size - PEqualNP.NotBracket.notCount C) hs
  rw [PEqualNP.Outside.L_meta_5971_aux.dpVal_511, ← PEqualNP.Outside.L_meta_5971_aux.countP_notNot_eq C] at hdp
  exact hdp
