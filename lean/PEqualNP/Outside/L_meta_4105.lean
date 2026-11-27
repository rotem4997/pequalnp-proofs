import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4105

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate erasure and wire redirection follow L_meta_534.
private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

private def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

private lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

private lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

private lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · rw [ite_eq_left hgt]; exact hm.2.2.2.2.2 u hgt
  · rw [ite_eq_right hgt]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

private lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

private lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

-- Part 3: No gate computes the same function as an earlier wire

private def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

private lemma no_duplicate_wire {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (i j : ℕ) (hij : i < n + j) (hj : j < C.gates.length) :
    ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false := by
  by_contra hsame
  push Not at hsame
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  let aliasGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire (n + j) i)⟩
  let D : Circuit := ⟨pre ++ post.map aliasGate, aliasWire (n + j) i C.output⟩
  have hfitD : FanInTwo D := by
    intro g hg
    rcases List.mem_append.mp hg with hpre | hpost
    · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
      have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨hg0C.1, by simp [aliasGate, hg0C.2]⟩
  have hfunD : circuitFun n D = circuitFun n C := by
    funext x
    have hxy := hsame x
    simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
    conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
    rw [List.foldl_append]
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + j := by
      simp [w0, foldl_stepWire_length, hpre_len]
    let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
    have hval_eq : w0.getD i false = bOld := by
      have hCi : (C.wires (List.ofFn x)).getD i false = w0.getD i false := by
        rw [wires_eq_foldl, hgs, List.foldl_append]
        exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
      have hCj : (C.wires (List.ofFn x)).getD (n + j) false = bOld := by
        rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
        rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
      rw [← hCi, ← hCj, hxy]
    have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
    have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
        ∀ u, vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
      intro vC vD hmv u
      unfold aliasWire
      by_cases hu : u = n + j
      · subst hu
        rw [ite_eq_left rfl, hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
      · rw [ite_eq_right hu, ← hw0_len]
        exact wiresMatch_getD_shiftDown hmv (by omega)
    have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
        ((post.map aliasGate).foldl stepWire w0) := by
      refine foldl_wiresMatch w0 bOld post (post.map aliasGate) (stepWire w0 gj) w0 hm0
        (by simp) ?_
      intro t htC htD vC vD hmv _
      simp only [List.getElem_map, aliasGate, List.map_map]
      congr 1
      refine List.map_congr_left fun u _ => ?_
      exact halias_get vC vD hmv u
    exact halias_get _ _ hmEnd C.output
  have hle := hmin.2 D hfitD hfunD
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  simp only [Circuit.size, D, List.length_append, List.length_map] at hle
  omega

-- Part 4: No gate computes a constant function

private def rewriteTrueGate (wOld : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => ⟨.and, (g.inputs.filter (fun u => u != wOld)).map (shiftDown wOld)⟩
  | .or =>
    if g.inputs.contains wOld then ⟨.and, []⟩
    else ⟨.or, g.inputs.map (shiftDown wOld)⟩
  | .not =>
    match g.inputs with
    | [] => ⟨.not, []⟩
    | u :: _ => if u = wOld then ⟨.or, []⟩ else ⟨.not, [shiftDown wOld u]⟩
  | op => ⟨op, g.inputs.map (shiftDown wOld)⟩

private lemma rewriteTrueGate_fit (wOld : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (rewriteTrueGate wOld g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (rewriteTrueGate wOld g).inputs.length ≤ 2 := by
  obtain ⟨hop, hlen⟩ := hg
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
  rcases hop with h | h | h
  · simp only [rewriteTrueGate, h, List.length_map]
    refine ⟨Or.inl rfl, (List.length_filter_le _ _).trans hlen⟩
  · simp only [rewriteTrueGate, h]
    split
    · exact ⟨Or.inl rfl, by simp⟩
    · exact ⟨Or.inr (Or.inl rfl), by simp [hlen]⟩
  · simp only [rewriteTrueGate, h]
    cases g.inputs with
    | nil => simp
    | cons u rest =>
      by_cases hu : u = wOld <;> simp [hu]

private lemma rewriteTrueGate_eval (w0 : List Bool) (vC vD : List Bool)
    (hm : wiresMatch w0 true vC vD) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (rewriteTrueGate w0.length g).op.eval
      ((rewriteTrueGate w0.length g).inputs.map fun i => vD.getD i false) =
    g.op.eval (g.inputs.map fun i => vC.getD i false) := by
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
  rcases hop with h | h | h
  · simp only [rewriteTrueGate, h, GateOp.eval, List.map_map, List.all_map]
    induction g.inputs with
    | nil => rfl
    | cons u us ih =>
      by_cases hu : u = w0.length
      · subst hu
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.all_cons, Function.comp_apply, id_eq, hm.2.2.1, Bool.true_and]
        exact ih
      · have hne : (u != w0.length) = true := bne_iff_ne.mpr hu
        simp only [List.filter_cons, hne, ↓reduceIte, List.all_cons, Function.comp_apply, id_eq]
        rw [wiresMatch_getD_shiftDown hm hu, ih]
  · simp only [rewriteTrueGate, h]
    by_cases hmem : g.inputs.contains w0.length = true
    · rw [ite_eq_left hmem]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨w0.length, List.contains_iff_mem.mp hmem, hm.2.2.1⟩, rfl⟩
    · rw [ite_eq_right hmem]
      simp only [GateOp.eval, List.map_map]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      have hne : u ≠ w0.length := fun heq => hmem (List.contains_iff_mem.mpr (heq ▸ hu))
      exact wiresMatch_getD_shiftDown hm hne
  · obtain ⟨op, inputs⟩ := g
    dsimp only at h ⊢
    subst h
    cases inputs with
    | nil => simp [rewriteTrueGate, GateOp.eval]
    | cons u rest =>
      by_cases hu : u = w0.length
      · subst hu
        simp only [rewriteTrueGate, GateOp.eval, ↓reduceIte, List.map_nil, List.any_nil,
          List.map_cons, List.headD_cons, hm.2.2.1, Bool.not_true]
      · simp only [rewriteTrueGate, GateOp.eval, hu, ↓reduceIte, List.map_cons, List.map_nil,
          List.headD_cons, wiresMatch_getD_shiftDown hm hu]

private lemma no_const_gate {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ x y : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false := by
  by_contra hconst
  push Not at hconst
  let x0 : Fin n → Bool := fun _ => false
  let b : Bool := (C.wires (List.ofFn x0)).getD (n + j) false
  have hall : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b :=
    fun x => hconst x x0
  have hout_ne : C.output ≠ n + j := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    simp only [circuitFun, Circuit.eval, heq, hall x, hall y]
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  cases hb : b with
  | false =>
    let big : ℕ := n + C.gates.length
    let aliasGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire (n + j) big)⟩
    let D : Circuit := ⟨pre ++ post.map aliasGate, shiftDown (n + j) C.output⟩
    have hfitD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hpre | hpost
      · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
        have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
        exact ⟨hg0C.1, by simp [aliasGate, hg0C.2]⟩
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
      rw [List.foldl_append]
      let w0 := pre.foldl stepWire (List.ofFn x)
      have hw0_len : w0.length = n + j := by
        simp [w0, foldl_stepWire_length, hpre_len]
      have hbf : gj.op.eval (gj.inputs.map fun k => w0.getD k false) = false := by
        have hCj : (C.wires (List.ofFn x)).getD (n + j) false =
            gj.op.eval (gj.inputs.map fun k => w0.getD k false) := by
          rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
          rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
        rw [← hCj, hall x, hb]
      have hm0 : wiresMatch w0 false (stepWire w0 gj) w0 := by
        unfold stepWire; rw [hbf]; exact wiresMatch_init w0 false
      have hlenC : C.gates.length = pre.length + 1 + post.length := by
        have := congrArg List.length hgs; simp at this; omega
      have hmEnd : wiresMatch w0 false (post.foldl stepWire (stepWire w0 gj))
          ((post.map aliasGate).foldl stepWire w0) := by
        refine foldl_wiresMatch w0 false post (post.map aliasGate) (stepWire w0 gj) w0 hm0
          (by simp) ?_
        intro t htC htD vC vD hmv hvlen
        simp only [List.getElem_map, aliasGate, List.map_map]
        congr 1
        refine List.map_congr_left fun u _ => ?_
        simp only [Function.comp_apply, aliasWire]
        by_cases hu : u = n + j
        · subst hu
          simp only [↓reduceIte]
          rw [getD_ge_length vD big (by omega), ← hw0_len, hmv.2.2.1]
        · simp only [hu, ↓reduceIte]
          rw [← hw0_len]
          exact wiresMatch_getD_shiftDown hmv (by omega)
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmEnd (by rw [hw0_len]; exact hout_ne)
    have hle := hmin.2 D hfitD hfunD
    have hlenC : C.gates.length = pre.length + 1 + post.length := by
      have := congrArg List.length hgs; simp at this; omega
    simp only [Circuit.size, D, List.length_append, List.length_map] at hle
    omega
  | true =>
    let D : Circuit := ⟨pre ++ post.map (rewriteTrueGate (n + j)), shiftDown (n + j) C.output⟩
    have hfitD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hpre | hpost
      · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
        have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
        exact rewriteTrueGate_fit (n + j) g0 hg0C
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
      rw [List.foldl_append]
      let w0 := pre.foldl stepWire (List.ofFn x)
      have hw0_len : w0.length = n + j := by
        simp [w0, foldl_stepWire_length, hpre_len]
      have hbt : gj.op.eval (gj.inputs.map fun k => w0.getD k false) = true := by
        have hCj : (C.wires (List.ofFn x)).getD (n + j) false =
            gj.op.eval (gj.inputs.map fun k => w0.getD k false) := by
          rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
          rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
        rw [← hCj, hall x, hb]
      have hm0 : wiresMatch w0 true (stepWire w0 gj) w0 := by
        unfold stepWire; rw [hbt]; exact wiresMatch_init w0 true
      have hmEnd : wiresMatch w0 true (post.foldl stepWire (stepWire w0 gj))
          ((post.map (rewriteTrueGate (n + j))).foldl stepWire w0) := by
        refine foldl_wiresMatch w0 true post (post.map (rewriteTrueGate (n + j)))
          (stepWire w0 gj) w0 hm0 (by simp) ?_
        intro t htC htD vC vD hmv _
        simp only [List.getElem_map]
        have hgC := hmin.1 (post[t]'htC)
          (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.getElem_mem htC)))
        simpa only [hw0_len] using rewriteTrueGate_eval w0 vC vD hmv (post[t]'htC) hgC.1
      simpa only [hw0_len] using wiresMatch_getD_shiftDown hmEnd (by rw [hw0_len]; exact hout_ne)
    have hle := hmin.2 D hfitD hfunD
    have hlenC : C.gates.length = pre.length + 1 + post.length := by
      have := congrArg List.length hgs; simp at this; omega
    simp only [Circuit.size, D, List.length_append, List.length_map] at hle
    omega

private def trim (g : Gate) : Gate :=
  ⟨g.op, g.inputs.take (bif g.op.eval [false] then 1 else 2)⟩

private lemma trim_eval (w : List Bool) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    stepWire w (trim g) = stepWire w g := by
  obtain ⟨op, ins⟩ := g
  change op = .and ∨ op = .or ∨ op = .not at hop
  change ins.length ≤ 2 at hl
  rcases hop with rfl | rfl | rfl
  · simp [stepWire, trim, GateOp.eval, List.take_of_length_le hl]
  · simp [stepWire, trim, GateOp.eval, List.take_of_length_le hl]
  · cases ins <;> simp [stepWire, trim, GateOp.eval]

private lemma trim_run (gs : List Gate) (w : List Bool)
    (hok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (gs.map trim).foldl stepWire w = gs.foldl stepWire w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have h := hok g List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons, trim_eval w g h.1 h.2]
    exact ih _ fun a ha => hok a (List.mem_cons_of_mem _ ha)

private def Good (k : ℕ) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a < k, g.inputs = [a]) ∨
  (g.op = .and ∨ g.op = .or) ∧ ∃ a < k, ∃ b < k, a ≠ b ∧ g.inputs = [a,b]

private lemma shape {X : Type*} (k : ℕ) (g : Gate) (read : X → ℕ → Bool)
    (outside : ∀ i, k ≤ i → ∀ x, read x i = false)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2)
    (unary : g.op = .not → g.inputs.length ≤ 1)
    (varies : ∀ c : Bool, ¬ ∀ x, g.op.eval (g.inputs.map (read x)) = c)
    (fresh : ∀ i, ¬ ∀ x, g.op.eval (g.inputs.map (read x)) = read x i) :
    Good k g := by
  obtain ⟨op, ins⟩ := g
  change op = .and ∨ op = .or ∨ op = .not at hop
  change ins.length ≤ 2 at hl
  change op = .not → ins.length ≤ 1 at unary
  change ∀ c : Bool, ¬ ∀ x, op.eval (ins.map (read x)) = c at varies
  change ∀ i, ¬ ∀ x, op.eval (ins.map (read x)) = read x i at fresh
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, ds⟩⟩⟩
  · exact False.elim (varies (op.eval []) (fun _ => rfl))
  · rcases hop with rfl | rfl | rfl
    · exact False.elim (fresh a (by simp [GateOp.eval]))
    · exact False.elim (fresh a (by simp [GateOp.eval]))
    · by_cases ha : a < k
      · exact Or.inl ⟨rfl, a, ha, rfl⟩
      · exact False.elim (varies true (by simp [GateOp.eval, outside a (by omega)]))
  · rcases hop with h | h | h
    · subst op
      by_cases ha : a < k
      · by_cases hb : b < k
        · by_cases hab : a = b
          · subst b
            exact False.elim (fresh a (by simp [GateOp.eval]))
          · exact Or.inr ⟨Or.inl rfl, a, ha, b, hb, hab, rfl⟩
        · exact False.elim (varies false (by simp [GateOp.eval, outside b (by omega)]))
      · exact False.elim (varies false (by simp [GateOp.eval, outside a (by omega)]))
    · subst op
      by_cases ha : a < k
      · by_cases hb : b < k
        · by_cases hab : a = b
          · subst b
            exact False.elim (fresh a (by simp [GateOp.eval]))
          · exact Or.inr ⟨Or.inr rfl, a, ha, b, hb, hab, rfl⟩
        · exact False.elim (fresh a (by simp [GateOp.eval, outside b (by omega)]))
      · exact False.elim (fresh b (by simp [GateOp.eval, outside a (by omega)]))
    · simpa using unary h
  · simp at hl

private lemma gate_shape {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y, circuitFun n C x ≠ circuitFun n C y)
    (pre : List Gate) (g : Gate) (post : List Gate) (hs : C.gates = pre ++ g :: post)
    (unary : g.op = .not → g.inputs.length ≤ 1) : Good (n + pre.length) g := by
  let k := n + pre.length
  let before (x : Fin n → Bool) := pre.foldl stepWire (List.ofFn x)
  let read (x : Fin n → Bool) (i : ℕ) := (before x).getD i false
  let signal (x : Fin n → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
  have hlen (x) : (before x).length = k := by simp [before, k, foldl_stepWire_length]
  have hout (i) (hi : k ≤ i) (x) : read x i = false :=
    getD_ge_length _ _ (by simpa only [hlen] using hi)
  have hat (x) : signal x k = g.op.eval (g.inputs.map (read x)) := by
    simp only [signal, wires_eq_foldl, hs, List.foldl_append, List.foldl_cons]
    change (post.foldl stepWire (stepWire (before x) g)).getD k false = _
    rw [foldl_stepWire_getD_lt post _ k (by simp [stepWire, hlen])]
    simp [stepWire, List.getD_eq_getElem?_getD, hlen, read]
  have hearlier (x) (i) (hi : i < k) : signal x i = read x i := by
    simp only [signal, wires_eq_foldl, hs, List.foldl_append]
    exact foldl_stepWire_getD_lt (g :: post) _ i (by simpa only [hlen] using hi : i < (before x).length)
  have hj : pre.length < C.gates.length := by simp [hs]
  have hg := hm.1 g (by simp [hs])
  have varies (c : Bool) (hc : ∀ x, g.op.eval (g.inputs.map (read x)) = c) : False := by
    obtain ⟨x,y,h⟩ := no_const_gate hm hnc _ hj
    exact h (((hat x).trans (hc x)).trans ((hat y).trans (hc y)).symm)
  apply shape k g read hout hg.1 hg.2 unary varies
  intro i he
  by_cases hi : i < k
  · obtain ⟨x,h⟩ := no_duplicate_wire hm i pre.length hi hj
    exact h (((hearlier x i hi).trans (he x).symm).trans (hat x).symm)
  · exact varies false fun x => (he x).trans (hout i (by omega) x)

end PEqualNP.Outside.L_meta_4105

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4105

theorem PEqualNP.Outside.L_meta_4105 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x5.gates = List.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => { op := x6.op, inputs := List.take (bif x6.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x6.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates ∧ x5.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ ∀ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x5.gates = x6 ++ x7 :: x8 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ x10 < x1 + x6.length, x7.inputs = [x10]) ∨ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x10 < x1 + x6.length, ∃ x11 < x1 + x6.length, x10 ≠ x11 ∧ x7.inputs = [x10, x11] := by
  intro n C hm hnc
  let D : Circuit := ⟨C.gates.map trim, C.output⟩
  have hs : D.size = C.size := by simp [D, Circuit.size]
  have he : circuitFun n D = circuitFun n C := by
    funext x
    exact congrArg (fun w : List Bool => w.getD C.output false)
      (trim_run C.gates (List.ofFn x) hm.1)
  have hfan : FanInTwo D := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm.1 a ha).1, (List.length_take_le' ..).trans (hm.1 a ha).2⟩
  have hmD : IsMinimalCircuit n D :=
    ⟨hfan, fun E hE heq => hs ▸ hm.2 E hE (heq.trans he)⟩
  refine ⟨D, rfl, hs, he, ?_⟩
  intro pre g post hsplit
  apply gate_shape hmD (he ▸ hnc) pre g post hsplit
  have hg : g ∈ D.gates := by simp [hsplit]
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  intro hnot
  change a.op = .not at hnot
  simp [trim, hnot, GateOp.eval]
