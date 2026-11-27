import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18896_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_evalStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl evalStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_evalStep_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl evalStep w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (evalStep w g).length := by simp [evalStep]; omega
    rw [ih (evalStep w g) hk']
    dsimp only [evalStep]
    exact List.getD_append w [g.op.eval _] false k hk

theorem evalStep_getD_lt (w : List Bool) (g : Gate) (k : ℕ) (hk : k < w.length) :
    (evalStep w g).getD k false = w.getD k false :=
  List.getD_append w [g.op.eval _] false k hk

theorem compact_aux (m : ℕ) :
    ∀ (gs : List Gate) (topW : List Bool) (wmap : List (Option ℕ)) (dGates : List Gate),
      wmap.length = topW.length →
      (∀ k, (wmap.getD k none).isSome = topW.getD k false) →
      (∀ k idx, wmap.getD k none = some idx → idx < m + dGates.length) →
      IsAO2 m ⟨dGates, 0⟩ →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.and, []⟩).inputs, i < topW.length + j) →
      ∃ (wmap' : List (Option ℕ)) (dGates' : List Gate),
        dGates'.length ≤ dGates.length +
          (gs.filter (fun g => g.inputs.all (fun i => (gs.foldl evalStep topW).getD i false))).length ∧
        IsAO2 m ⟨dGates', 0⟩ ∧
        wmap'.length = topW.length + gs.length ∧
        (∀ k idx, wmap'.getD k none = some idx → idx < m + dGates'.length) ∧
        (∀ (x : Fin m → Bool) (cW : List Bool),
          cW.length = topW.length →
          (∀ k, (wmap.getD k none).elim false (fun idx => (dGates.foldl evalStep (List.ofFn x)).getD idx false) =
                cW.getD k false) →
          ∀ k, (wmap'.getD k none).elim false (fun idx => (dGates'.foldl evalStep (List.ofFn x)).getD idx false) =
               (gs.foldl evalStep cW).getD k false) := by
  intro gs
  induction gs with
  | nil =>
    intro topW wmap dGates hlen _ hbd hao _ _
    refine ⟨wmap, dGates, by simp, hao, by simp [hlen], hbd, ?_⟩
    intro x cW _ hmatch k
    exact hmatch k
  | cons g gs ih =>
    intro topW wmap dGates hlen htop hbd hao hgates hrb
    rcases hgates g (List.mem_cons_self ..) with ⟨hg_op, hg_len⟩
    have hg_rb : ∀ i ∈ g.inputs, i < topW.length := by
      have h0 := hrb 0 (by simp)
      simpa using h0
    rcases List.length_eq_two.mp hg_len with ⟨a, b, hins⟩
    have ha : a < topW.length := hg_rb a (by simp [hins])
    have hb : b < topW.length := hg_rb b (by simp [hins])
    have htop_eq : (gs.foldl evalStep (evalStep topW g)).getD a false = topW.getD a false ∧
                   (gs.foldl evalStep (evalStep topW g)).getD b false = topW.getD b false := by
      constructor
      · rw [foldl_evalStep_getD_lt gs (evalStep topW g) a (by simp [evalStep]; omega)]
        exact evalStep_getD_lt topW g a ha
      · rw [foldl_evalStep_getD_lt gs (evalStep topW g) b (by simp [evalStep]; omega)]
        exact evalStep_getD_lt topW g b hb
    have hfilt_g : g.inputs.all (fun i => ((g :: gs).foldl evalStep topW).getD i false) =
        (topW.getD a false && topW.getD b false) := by
      simp only [List.foldl_cons, hins, List.all_cons, List.all_nil, Bool.and_true, htop_eq.1, htop_eq.2]
    have hgs_gates : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
      fun g' hg' => hgates g' (List.mem_cons_of_mem g hg')
    have hgs_rb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.and, []⟩).inputs, i < (evalStep topW g).length + j := by
      intro j hj i hi
      have h1 := hrb (j + 1) (by simp; omega) i
      simp only [List.getD_cons_succ] at h1
      have h2 := h1 hi
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    have hget_last : ∀ {α : Type} (l : List α) (v d : α), (l ++ [v]).getD l.length d = v := by
      intro α l v d
      simp [List.getD_eq_getElem?_getD]
    have hget_gt : ∀ {α : Type} (l : List α) (d : α) (k : ℕ), l.length ≤ k → l.getD k d = d := by
      intro α l d k hk
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
    cases hma : wmap.getD a none with
    | some ia =>
      have hta : topW.getD a false = true := by rw [← htop a, hma]; rfl
      have hia : ia < m + dGates.length := hbd a ia hma
      cases hmb : wmap.getD b none with
      | some ib =>
        have htb : topW.getD b false = true := by rw [← htop b, hmb]; rfl
        have hib : ib < m + dGates.length := hbd b ib hmb
        let g' : Gate := ⟨g.op, [ia, ib]⟩
        let dGates1 := dGates ++ [g']
        let wmap1 := wmap ++ [some (m + dGates.length)]
        have htop_val : g.op.eval (g.inputs.map fun i => topW.getD i false) = true := by
          rw [hins]; simp only [List.map_cons, List.map_nil, hta, htb]
          rcases hg_op with h | h <;> rw [h] <;> rfl
        have hlen1 : wmap1.length = (evalStep topW g).length := by
          simp [wmap1, evalStep, hlen]
        have htop1 : ∀ k, (wmap1.getD k none).isSome = (evalStep topW g).getD k false := by
          intro k
          by_cases hk : k < topW.length
          · rw [List.getD_append wmap _ none k (by omega), evalStep_getD_lt topW g k hk]
            exact htop k
          · by_cases heq : k = topW.length
            · subst heq
              have h1 : wmap1.getD topW.length none = some (m + dGates.length) := by
                rw [← hlen]; exact hget_last wmap _ none
              have h2 : (evalStep topW g).getD topW.length false = true := by
                dsimp only [evalStep]; rw [hget_last topW _ false]; exact htop_val
              rw [h1, h2]; rfl
            · rw [hget_gt wmap1 none k (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep topW g) false k (by simp [evalStep]; omega)]
              rfl
        have hbd1 : ∀ k idx, wmap1.getD k none = some idx → idx < m + dGates1.length := by
          intro k idx hki
          by_cases hk : k < wmap.length
          · rw [List.getD_append wmap _ none k hk] at hki
            have := hbd k idx hki
            simp [dGates1]; omega
          · by_cases heq : k = wmap.length
            · subst heq
              rw [hget_last wmap _ none] at hki
              injection hki with heq2
              subst heq2
              simp [dGates1]
            · rw [hget_gt wmap1 none k (by simp [wmap1]; omega)] at hki
              exact absurd hki (by simp)
        have hao1 : IsAO2 m ⟨dGates1, 0⟩ := by
          rcases hao with ⟨hAO, hRB, hLen⟩
          refine ⟨?_, ?_, ?_⟩
          · intro q hq
            simp only [dGates1, List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · exact hAO q hq
            · exact hg_op
          · intro j hj i hi
            change j < (dGates ++ [g']).length at hj
            by_cases hjlt : j < dGates.length
            · have hga : gateAt ⟨dGates1, 0⟩ j = gateAt ⟨dGates, 0⟩ j := by
                simp only [gateAt, dGates1, List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]
              rw [hga] at hi
              exact hRB j hjlt i hi
            · have hjeq : j = dGates.length := by simp at hj; omega
              subst hjeq
              have hga : gateAt ⟨dGates1, 0⟩ dGates.length = g' := by
                simp only [gateAt, dGates1]; exact hget_last dGates g' _
              rw [hga] at hi
              simp only [g', List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> assumption
          · intro q hq
            simp only [dGates1, List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · exact hLen q hq
            · rfl
        obtain ⟨wmap', dGates', hsz', hao', hlen', hbd', heval'⟩ :=
          ih (evalStep topW g) wmap1 dGates1 hlen1 htop1 hbd1 hao1 hgs_gates hgs_rb
        refine ⟨wmap', dGates', ?_, hao', ?_, hbd', ?_⟩
        · simp only [List.filter_cons, hfilt_g, hta, htb, Bool.and_true, ↓reduceIte, List.length_cons]
          simp only [dGates1, List.length_append, List.length_singleton] at hsz'
          simp only [List.foldl_cons] at hsz' ⊢
          omega
        · simp only [evalStep, List.length_append, List.length_singleton] at hlen'
          simp only [List.length_cons]; omega
        · intro x cW hcWlen hmatch k
          simp only [List.foldl_cons]
          apply heval' x (evalStep cW g) (by simp [evalStep, hcWlen])
          intro j
          have hdW1 : dGates1.foldl evalStep (List.ofFn x) =
              evalStep (dGates.foldl evalStep (List.ofFn x)) g' := by
            simp [dGates1]
          rw [hdW1]
          have hdLen : (dGates.foldl evalStep (List.ofFn x)).length = m + dGates.length := by
            rw [foldl_evalStep_length, List.length_ofFn]
          by_cases hj : j < cW.length
          · rw [List.getD_append wmap _ none j (by omega), evalStep_getD_lt cW g j hj]
            cases hmj : wmap.getD j none with
            | none =>
              have := hmatch j; rw [hmj] at this; exact this
            | some idx =>
              have hidx : idx < m + dGates.length := hbd j idx hmj
              simp only [Option.elim_some]
              rw [evalStep_getD_lt _ g' idx (by omega)]
              have := hmatch j; rw [hmj] at this; exact this
          · by_cases heq : j = cW.length
            · subst heq
              have h1 : wmap1.getD cW.length none = some (m + dGates.length) := by
                rw [show cW.length = wmap.length by omega]; exact hget_last wmap _ none
              rw [h1]
              simp only [Option.elim_some]
              rw [show m + dGates.length = (dGates.foldl evalStep (List.ofFn x)).length by omega]
              dsimp only [evalStep]
              rw [hget_last _ _ false, hget_last _ _ false]
              simp only [g', hins, List.map_cons, List.map_nil]
              have ha_eq : (dGates.foldl evalStep (List.ofFn x)).getD ia false = cW.getD a false := by
                have := hmatch a; rw [hma] at this; exact this
              have hb_eq : (dGates.foldl evalStep (List.ofFn x)).getD ib false = cW.getD b false := by
                have := hmatch b; rw [hmb] at this; exact this
              rw [ha_eq, hb_eq]
            · rw [hget_gt wmap1 none j (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep cW g) false j (by simp [evalStep]; omega)]
              rfl
      | none =>
        have htb : topW.getD b false = false := by
          cases h : topW.getD b false
          · rfl
          · have := htop b; rw [hmb, h] at this; exact absurd this (by decide)
        let newOpt : Option ℕ := match g.op with | GateOp.or => some ia | _ => none
        let wmap1 := wmap ++ [newOpt]
        have htop_val : newOpt.isSome = g.op.eval (g.inputs.map fun i => topW.getD i false) := by
          rw [hins]; simp only [List.map_cons, List.map_nil, hta, htb]
          dsimp only [newOpt]
          rcases hg_op with h | h <;> rw [h] <;> rfl
        have hlen1 : wmap1.length = (evalStep topW g).length := by simp [wmap1, evalStep, hlen]
        have htop1 : ∀ k, (wmap1.getD k none).isSome = (evalStep topW g).getD k false := by
          intro k
          by_cases hk : k < topW.length
          · rw [List.getD_append wmap _ none k (by omega), evalStep_getD_lt topW g k hk]
            exact htop k
          · by_cases heq : k = topW.length
            · subst heq
              rw [show topW.length = wmap.length by omega, hget_last wmap _ none]
              dsimp only [evalStep]; rw [show wmap.length = topW.length by omega, hget_last topW _ false]
              exact htop_val
            · rw [hget_gt wmap1 none k (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep topW g) false k (by simp [evalStep]; omega)]
              rfl
        have hbd1 : ∀ k idx, wmap1.getD k none = some idx → idx < m + dGates.length := by
          intro k idx hki
          by_cases hk : k < wmap.length
          · rw [List.getD_append wmap _ none k hk] at hki; exact hbd k idx hki
          · by_cases heq : k = wmap.length
            · subst heq
              rw [hget_last wmap _ none] at hki
              dsimp only [newOpt] at hki
              rcases hg_op with h | h
              · rw [h] at hki; exact absurd hki (by simp)
              · rw [h] at hki; injection hki with h2; subst h2; exact hia
            · rw [hget_gt wmap1 none k (by simp [wmap1]; omega)] at hki
              exact absurd hki (by simp)
        obtain ⟨wmap', dGates', hsz', hao', hlen', hbd', heval'⟩ :=
          ih (evalStep topW g) wmap1 dGates hlen1 htop1 hbd1 hao hgs_gates hgs_rb
        refine ⟨wmap', dGates', ?_, hao', ?_, hbd', ?_⟩
        · simp only [List.filter_cons, hfilt_g, hta, htb, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          simp only [List.foldl_cons] at hsz' ⊢; exact hsz'
        · simp only [evalStep, List.length_append, List.length_singleton] at hlen'
          simp only [List.length_cons]; omega
        · intro x cW hcWlen hmatch k
          simp only [List.foldl_cons]
          apply heval' x (evalStep cW g) (by simp [evalStep, hcWlen])
          intro j
          by_cases hj : j < cW.length
          · rw [List.getD_append wmap _ none j (by omega), evalStep_getD_lt cW g j hj]
            exact hmatch j
          · by_cases heq : j = cW.length
            · subst heq
              rw [show cW.length = wmap.length by omega, hget_last wmap _ none]
              dsimp only [evalStep]
              rw [show wmap.length = cW.length by omega, hget_last cW _ false]
              rw [hins]; simp only [List.map_cons, List.map_nil]
              have ha_eq : (dGates.foldl evalStep (List.ofFn x)).getD ia false = cW.getD a false := by
                have := hmatch a; rw [hma] at this; exact this
              have hb_eq : cW.getD b false = false := by
                have := hmatch b; rw [hmb] at this; exact this.symm
              rw [hb_eq]
              dsimp only [newOpt]
              rcases hg_op with h | h
              · rw [h]; simp [GateOp.eval]
              · rw [h]; simp [GateOp.eval]; exact ha_eq
            · rw [hget_gt wmap1 none j (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep cW g) false j (by simp [evalStep]; omega)]
              rfl
    | none =>
      have hta : topW.getD a false = false := by
        cases h : topW.getD a false
        · rfl
        · have := htop a; rw [hma, h] at this; exact absurd this (by decide)
      cases hmb : wmap.getD b none with
      | some ib =>
        have htb : topW.getD b false = true := by rw [← htop b, hmb]; rfl
        have hib : ib < m + dGates.length := hbd b ib hmb
        let newOpt : Option ℕ := match g.op with | GateOp.or => some ib | _ => none
        let wmap1 := wmap ++ [newOpt]
        have htop_val : newOpt.isSome = g.op.eval (g.inputs.map fun i => topW.getD i false) := by
          rw [hins]; simp only [List.map_cons, List.map_nil, hta, htb]
          dsimp only [newOpt]
          rcases hg_op with h | h <;> rw [h] <;> rfl
        have hlen1 : wmap1.length = (evalStep topW g).length := by simp [wmap1, evalStep, hlen]
        have htop1 : ∀ k, (wmap1.getD k none).isSome = (evalStep topW g).getD k false := by
          intro k
          by_cases hk : k < topW.length
          · rw [List.getD_append wmap _ none k (by omega), evalStep_getD_lt topW g k hk]
            exact htop k
          · by_cases heq : k = topW.length
            · subst heq
              rw [show topW.length = wmap.length by omega, hget_last wmap _ none]
              dsimp only [evalStep]; rw [show wmap.length = topW.length by omega, hget_last topW _ false]
              exact htop_val
            · rw [hget_gt wmap1 none k (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep topW g) false k (by simp [evalStep]; omega)]
              rfl
        have hbd1 : ∀ k idx, wmap1.getD k none = some idx → idx < m + dGates.length := by
          intro k idx hki
          by_cases hk : k < wmap.length
          · rw [List.getD_append wmap _ none k hk] at hki; exact hbd k idx hki
          · by_cases heq : k = wmap.length
            · subst heq
              rw [hget_last wmap _ none] at hki
              dsimp only [newOpt] at hki
              rcases hg_op with h | h
              · rw [h] at hki; exact absurd hki (by simp)
              · rw [h] at hki; injection hki with h2; subst h2; exact hib
            · rw [hget_gt wmap1 none k (by simp [wmap1]; omega)] at hki
              exact absurd hki (by simp)
        obtain ⟨wmap', dGates', hsz', hao', hlen', hbd', heval'⟩ :=
          ih (evalStep topW g) wmap1 dGates hlen1 htop1 hbd1 hao hgs_gates hgs_rb
        refine ⟨wmap', dGates', ?_, hao', ?_, hbd', ?_⟩
        · simp only [List.filter_cons, hfilt_g, hta, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          simp only [List.foldl_cons] at hsz' ⊢; exact hsz'
        · simp only [evalStep, List.length_append, List.length_singleton] at hlen'
          simp only [List.length_cons]; omega
        · intro x cW hcWlen hmatch k
          simp only [List.foldl_cons]
          apply heval' x (evalStep cW g) (by simp [evalStep, hcWlen])
          intro j
          by_cases hj : j < cW.length
          · rw [List.getD_append wmap _ none j (by omega), evalStep_getD_lt cW g j hj]
            exact hmatch j
          · by_cases heq : j = cW.length
            · subst heq
              rw [show cW.length = wmap.length by omega, hget_last wmap _ none]
              dsimp only [evalStep]
              rw [show wmap.length = cW.length by omega, hget_last cW _ false]
              rw [hins]; simp only [List.map_cons, List.map_nil]
              have ha_eq : cW.getD a false = false := by
                have := hmatch a; rw [hma] at this; exact this.symm
              have hb_eq : (dGates.foldl evalStep (List.ofFn x)).getD ib false = cW.getD b false := by
                have := hmatch b; rw [hmb] at this; exact this
              rw [ha_eq]
              dsimp only [newOpt]
              rcases hg_op with h | h
              · rw [h]; simp [GateOp.eval]
              · rw [h]; simp [GateOp.eval]; exact hb_eq
            · rw [hget_gt wmap1 none j (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep cW g) false j (by simp [evalStep]; omega)]
              rfl
      | none =>
        have htb : topW.getD b false = false := by
          cases h : topW.getD b false
          · rfl
          · have := htop b; rw [hmb, h] at this; exact absurd this (by decide)
        let wmap1 := wmap ++ [none]
        have htop_val : (none : Option ℕ).isSome = g.op.eval (g.inputs.map fun i => topW.getD i false) := by
          rw [hins]; simp only [List.map_cons, List.map_nil, hta, htb]
          rcases hg_op with h | h <;> rw [h] <;> rfl
        have hlen1 : wmap1.length = (evalStep topW g).length := by simp [wmap1, evalStep, hlen]
        have htop1 : ∀ k, (wmap1.getD k none).isSome = (evalStep topW g).getD k false := by
          intro k
          by_cases hk : k < topW.length
          · rw [List.getD_append wmap _ none k (by omega), evalStep_getD_lt topW g k hk]
            exact htop k
          · by_cases heq : k = topW.length
            · subst heq
              rw [show topW.length = wmap.length by omega, hget_last wmap _ none]
              dsimp only [evalStep]; rw [show wmap.length = topW.length by omega, hget_last topW _ false]
              exact htop_val
            · rw [hget_gt wmap1 none k (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep topW g) false k (by simp [evalStep]; omega)]
              rfl
        have hbd1 : ∀ k idx, wmap1.getD k none = some idx → idx < m + dGates.length := by
          intro k idx hki
          by_cases hk : k < wmap.length
          · rw [List.getD_append wmap _ none k hk] at hki; exact hbd k idx hki
          · by_cases heq : k = wmap.length
            · subst heq; rw [hget_last wmap _ none] at hki; exact absurd hki (by simp)
            · rw [hget_gt wmap1 none k (by simp [wmap1]; omega)] at hki; exact absurd hki (by simp)
        obtain ⟨wmap', dGates', hsz', hao', hlen', hbd', heval'⟩ :=
          ih (evalStep topW g) wmap1 dGates hlen1 htop1 hbd1 hao hgs_gates hgs_rb
        refine ⟨wmap', dGates', ?_, hao', ?_, hbd', ?_⟩
        · simp only [List.filter_cons, hfilt_g, hta, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          simp only [List.foldl_cons] at hsz' ⊢; exact hsz'
        · simp only [evalStep, List.length_append, List.length_singleton] at hlen'
          simp only [List.length_cons]; omega
        · intro x cW hcWlen hmatch k
          simp only [List.foldl_cons]
          apply heval' x (evalStep cW g) (by simp [evalStep, hcWlen])
          intro j
          by_cases hj : j < cW.length
          · rw [List.getD_append wmap _ none j (by omega), evalStep_getD_lt cW g j hj]
            exact hmatch j
          · by_cases heq : j = cW.length
            · subst heq
              rw [show cW.length = wmap.length by omega, hget_last wmap _ none]
              dsimp only [evalStep]
              rw [show wmap.length = cW.length by omega, hget_last cW _ false]
              rw [hins]; simp only [List.map_cons, List.map_nil]
              have ha_eq : cW.getD a false = false := by
                have := hmatch a; rw [hma] at this; exact this.symm
              have hb_eq : cW.getD b false = false := by
                have := hmatch b; rw [hmb] at this; exact this.symm
              rw [ha_eq, hb_eq]
              rcases hg_op with h | h <;> rw [h] <;> rfl
            · rw [hget_gt wmap1 none j (by simp [wmap1, hlen]; omega),
                  hget_gt (evalStep cW g) false j (by simp [evalStep]; omega)]
              rfl

theorem main_proof :
    ∀ (n m : ℕ) (C : Circuit) (p : Fin n → Option (Fin m)), IsAO2 n C →
      let top := C.wires (List.ofFn (fun i => (p i).isSome))
      ∃ D : Circuit, IsAO2 m D ∧
        D.size ≤ (C.gates.filter (fun g => g.inputs.all (fun i => top.getD i false))).length ∧
        ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => (p i).elim false x)) := by
  intro n m C p hao
  rcases hao with ⟨hAO, hRB, hLen⟩
  let top0 : List Bool := List.ofFn (fun i : Fin n => (p i).isSome)
  let wmap0 : List (Option ℕ) := List.ofFn (fun i : Fin n => (p i).map Fin.val)
  have hlen0 : wmap0.length = top0.length := by simp [wmap0, top0]
  have htop0 : ∀ k, (wmap0.getD k none).isSome = top0.getD k false := by
    intro k
    by_cases hk : k < n
    · simp [wmap0, top0, List.getD_eq_getElem?_getD, hk]
    · have h1 : wmap0.length ≤ k := by simp [wmap0]; omega
      have h2 : top0.length ≤ k := by simp [top0]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]
  have hbd0 : ∀ k idx, wmap0.getD k none = some idx → idx < m + ([] : List Gate).length := by
    intro k idx hki
    by_cases hk : k < n
    · simp only [wmap0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, ↓reduceDIte, Option.getD_some] at hki
      cases hp : p ⟨k, hk⟩ with
      | none => rw [hp] at hki; exact absurd hki (by simp)
      | some q =>
        rw [hp] at hki; simp only [Option.map_some, Option.some.injEq] at hki
        subst hki; simp [q.isLt]
    · have h1 : wmap0.length ≤ k := by simp [wmap0]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, Option.getD_none] at hki
      exact absurd hki (by simp)
  have hao0 : IsAO2 m ⟨[], 0⟩ :=
    ⟨(by intro g hg; cases hg), (by intro j hj; simp at hj), (by intro g hg; cases hg)⟩
  have hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO g hg, hLen g hg⟩
  have hrb0 : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.and, []⟩).inputs, i < top0.length + j := by
    intro j hj i hi
    have h1 := hRB j hj i
    have hga : gateAt C j = C.gates.getD j ⟨GateOp.and, []⟩ := by
      simp only [gateAt, List.getD_eq_getElem?_getD]
      have hne : C.gates[j]? ≠ none := by simp [hj]
      cases h : C.gates[j]? with
      | none => exact absurd h hne
      | some _ => rfl
    rw [hga] at h1
    have h2 := h1 hi
    simp only [top0, List.length_ofFn]; exact h2
  obtain ⟨wmap', dGates', hsz', hao', _, hbd', heval'⟩ :=
    compact_aux m C.gates top0 wmap0 [] hlen0 htop0 hbd0 hao0 hgates hrb0
  let outIdx : ℕ := (wmap'.getD C.output none).getD (m + dGates'.length)
  have hsz_final : (Circuit.mk dGates' outIdx).size ≤
      (C.gates.filter (fun g => g.inputs.all (fun i => (C.wires top0).getD i false))).length := by
    have h0 : dGates'.length ≤ (C.gates.filter (fun g => g.inputs.all (fun i => (C.gates.foldl evalStep top0).getD i false))).length := by
      simpa only [List.length_nil, Nat.zero_add] using hsz'
    exact h0
  refine ⟨⟨dGates', outIdx⟩, hao', hsz_final, ?_⟩
  intro x
  have hmatch0 : ∀ k, (wmap0.getD k none).elim false (fun idx => (([] : List Gate).foldl evalStep (List.ofFn x)).getD idx false) =
      (List.ofFn (fun i : Fin n => (p i).elim false x)).getD k false := by
    intro k
    by_cases hk : k < n
    · simp only [wmap0, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, ↓reduceDIte, Option.getD_some]
      cases hp : p ⟨k, hk⟩ with
      | none => rfl
      | some q => simp [q.isLt]
    · have h1 : wmap0.length ≤ k := by simp [wmap0]; omega
      have h2 : (List.ofFn (fun i : Fin n => (p i).elim false x)).length ≤ k := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]
  have hfinal := heval' x (List.ofFn (fun i : Fin n => (p i).elim false x)) (by simp [top0]) hmatch0 C.output
  change (dGates'.foldl evalStep (List.ofFn x)).getD outIdx false =
         (C.gates.foldl evalStep (List.ofFn (fun i : Fin n => (p i).elim false x))).getD C.output false
  rw [← hfinal]
  dsimp only [outIdx]
  cases hwo : wmap'.getD C.output none with
  | none =>
    simp only [Option.getD_none, Option.elim_none]
    have hge : (dGates'.foldl evalStep (List.ofFn x)).length ≤ m + dGates'.length := by
      rw [foldl_evalStep_length, List.length_ofFn]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
  | some idx =>
    simp only [Option.getD_some, Option.elim_some]

end PEqualNP.Outside.L_meta_18896_aux

theorem PEqualNP.Outside.L_meta_18896 : (∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1 → Option (Fin x2)),   PEqualNP.TopForm.IsAO2 x1 x3 →     have x6 : List Bool := x3.wires (List.ofFn fun (x6 : Fin x1) => (x4 x6).isSome);     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x7 ∧ x7.size ≤ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.all fun (x9 : ℕ) => x6.getD x9 Bool.false) x3.gates).length ∧ ∀ (x8 : Fin x2 → Bool), x7.eval (List.ofFn x8) = x3.eval (List.ofFn fun (x9 : Fin x1) => (x4 x9).elim Bool.false x8))  := by
  exact PEqualNP.Outside.L_meta_18896_aux.main_proof
