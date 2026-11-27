import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_176_aux

open PEqualNP.CircuitLowerBounds

/-- One evaluation step: append the value of gate `g` to the wires `w`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The wires after evaluating the gates `gs`, starting from `w`. -/
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (l1 l2 : List Gate) (w : List Bool) :
    run (l1 ++ l2) w = run l2 (run l1 w) := List.foldl_append

theorem run_cons (g : Gate) (l : List Gate) (w : List Bool) :
    run (g :: l) w = run l (step w g) := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false =
      if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false :=
  List.getD_eq_default _ _ h

theorem length_run (l : List Gate) (w : List Bool) :
    (run l w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp [run]
  | cons g l ih => rw [run_cons, ih]; simp [step]; omega

theorem getD_run_of_lt (l : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (run l w).getD i false = w.getD i false := by
  induction l generalizing w with
  | nil => rfl
  | cons g l ih =>
    rw [run_cons, ih _ (by simp [step]; omega), step, getD_snoc, if_pos h]

/-- The wires a gate's value actually depends on. -/
def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ eff g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rcases g with ⟨op, ins⟩
  cases op
  case not =>
    rcases ins with _ | ⟨a, t⟩
    · rfl
    · simp [GateOp.eval, h a (by simp [eff])]
  all_goals exact congrArg _ (List.map_congr_left (fun i hi => h i (by simpa [eff] using hi)))

/-- The gate `g` with its input wires renamed by `φ`. -/
def mapG (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

theorem step_mapG (φ : ℕ → ℕ) (E : Set ℕ) (g : Gate) (W W' : List Bool)
    (hg : ∀ i ∈ eff g, i ∉ E) (hinv : ∀ i, i ∉ E → W'.getD (φ i) false = W.getD i false) :
    step W' (mapG φ g) = W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := by
  simp only [step, mapG, List.map_map]
  rw [eval_congr g ((fun i => W'.getD i false) ∘ φ) (fun i => W.getD i false)
    (fun i hi => hinv i (hg i hi))]

/-- The renaming lemma: run the gates `l` from `W`, and their renamed copies from `W'`. -/
theorem seg (φ : ℕ → ℕ) (E : Set ℕ) : ∀ (l : List Gate) (W W' : List Bool),
    (∀ g ∈ l, ∀ i ∈ eff g, i ∉ E) →
    (∀ i, W.length ≤ i → φ i + W.length = i + W'.length) →
    (∀ i, i < W.length → φ i < W'.length ∨ W'.length + l.length ≤ φ i) →
    (∀ i, i ∉ E → W'.getD (φ i) false = W.getD i false) →
    ∀ i, i ∉ E → (run (l.map (mapG φ)) W').getD (φ i) false = (run l W).getD i false := by
  intro l
  induction l with
  | nil => intro W W' _ _ _ hinv; simpa [run] using hinv
  | cons g l ih =>
    intro W W' hE hoff hrng hinv
    rw [List.map_cons, run_cons, run_cons, step_mapG φ E g W W' (hE g (by simp)) hinv]
    set v := g.op.eval (g.inputs.map fun i => W.getD i false)
    have hstep : step W g = W ++ [v] := rfl
    rw [hstep]
    apply ih
    · exact fun g' hg' => hE g' (by simp [hg'])
    · intro i hi
      simp at hi ⊢
      have := hoff i (by omega)
      omega
    · intro i hi
      simp at hi ⊢
      by_cases h : i < W.length
      · rcases hrng i h with h' | h'
        · left; omega
        · right; simp at h'; omega
      · have := hoff i (by omega)
        left; omega
    · intro i hiE
      rw [getD_snoc, getD_snoc]
      by_cases h : i < W.length
      · rw [if_pos h]
        rcases hrng i h with h' | h'
        · rw [if_pos h', hinv i hiE]
        · simp at h'
          rw [if_neg (by omega), if_neg (by omega), ← hinv i hiE, getD_ge _ _ (by omega)]
      · rw [if_neg h]
        have := hoff i (by omega)
        by_cases h2 : i = W.length
        · rw [if_neg (by omega), if_pos (by omega), if_pos h2]
        · rw [if_neg (by omega), if_neg (by omega), if_neg h2]


theorem mapG_id_map (l : List Gate) : l.map (mapG id) = l := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.map_cons, ih]; cases g; simp [mapG]

/-- Removing one gate whose value is a copy of an earlier wire (on every input whose last bit
  is `false`), or that no later gate reads and is not the output, and setting the last input to
  `false`. -/
theorem drop (m : ℕ) (l1 l2 : List Gate) (G : Gate) (out q : ℕ) (E : Set ℕ)
    (hq : q < m + 1 + l1.length)
    (hEsub : ∀ i ∈ E, i = m + 1 + l1.length)
    (hE : ∀ g ∈ l2, ∀ i ∈ eff g, i ∉ E) (hout : out ∉ E)
    (hval : m + 1 + l1.length ∉ E → ∀ x : List Bool, x.length = m →
      G.op.eval (G.inputs.map fun i => (run l1 (x ++ [false])).getD i false) =
        (run l1 (x ++ [false])).getD q false) :
    ∃ D : Circuit, D.gates.length = l1.length + l2.length ∧
      (∀ g ∈ D.gates, ∃ g0 ∈ l1 ++ l2, g.op = g0.op ∧ g.inputs.length = g0.inputs.length) ∧
      ∀ x : List Bool, x.length = m →
        D.eval x = (Circuit.mk (l1 ++ G :: l2) out).eval (x ++ [false]) := by
  set p := m + 1 + l1.length with hp
  set B := p + l2.length + 1 with hB
  set φ1 : ℕ → ℕ := fun i => if i < m then i else if i = m then B else i - 1 with hφ1
  set φ2 : ℕ → ℕ := fun i => if i < p then φ1 i else if i = p then φ1 q else i - 2 with hφ2
  have r1 : ∀ i, i < p → φ1 i < m + l1.length ∨ m + l1.length + l2.length ≤ φ1 i := by
    intro i hi; simp only [hφ1]; split_ifs <;> omega
  refine ⟨⟨l1.map (mapG φ1) ++ l2.map (mapG φ2), φ2 out⟩, by simp, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g0, h0, rfl⟩ | ⟨g0, h0, rfl⟩
    · exact ⟨g0, by simp [h0], rfl, by simp [mapG]⟩
    · exact ⟨g0, by simp [h0], rfl, by simp [mapG]⟩
  · intro x hx
    have h1 := seg φ1 ∅ l1 (x ++ [false]) x (by simp)
      (by intro i hi; simp at hi ⊢; simp only [hφ1]; split_ifs <;> omega)
      (by intro i hi; simp at hi ⊢; simp only [hφ1]; split_ifs <;> omega)
      (by
        intro i _
        rw [getD_snoc]
        simp only [hφ1]
        split_ifs <;> first | rfl | (rw [getD_ge] <;> omega))
    simp only [Set.mem_empty_iff_false, not_false_eq_true, forall_const] at h1
    set W1 := run l1 (x ++ [false]) with hW1
    set W1' := run (l1.map (mapG φ1)) x with hW1'
    have lW1 : W1.length = p := by rw [hW1, length_run]; simp; omega
    have lW1' : W1'.length = m + l1.length := by rw [hW1', length_run]; simp; omega
    set v := G.op.eval (G.inputs.map fun i => W1.getD i false) with hv
    have hstep : step W1 G = W1 ++ [v] := rfl
    rw [Circuit.eval, Circuit.eval, wires_eq, wires_eq]
    simp only [List.map_append]
    rw [run_append, run_append, run_cons, hstep, ← hW1']
    apply seg φ2 E l2 (W1 ++ [v]) W1' hE
    · intro i hi; simp at hi; rw [lW1] at hi; simp only [hφ2]; split_ifs <;> simp <;> omega
    · intro i hi
      simp at hi
      rw [lW1'] 
      simp only [hφ2]
      split_ifs with h h'
      · exact r1 i h
      · exact r1 q hq
      · omega
    · intro i hiE
      rw [getD_snoc, lW1]
      simp only [hφ2]
      split_ifs with h h'
      · rw [h1]
      · subst h'
        rw [h1]
        exact (hval hiE x hx).symm
      · rw [getD_ge]; omega
    · exact hout

/-- A fan-in-two gate that reads a wire carrying `false`. -/
theorem Rf (H : Gate)
    (hop : H.op = GateOp.and ∨ H.op = GateOp.or ∨ H.op = GateOp.not)
    (hlen : H.inputs.length ≤ 2) (c z p' : ℕ) (hc : c ∈ eff H) (hz : z < p') :
    H.op = GateOp.not ∨ ∃ q < p', ∀ W : List Bool, W.length = p' →
      W.getD c false = false → W.getD z false = false →
        H.op.eval (H.inputs.map fun i => W.getD i false) = W.getD q false := by
  obtain ⟨op, ins⟩ := H
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl | rfl
  · right
    refine ⟨z, hz, fun W _ hWc hWz => ?_⟩
    rw [hWz]
    simp only [GateOp.eval]
    simpa using ⟨c, by simpa [eff] using hc, hWc⟩
  · right
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
    · simp [eff] at hc
    · simp [eff] at hc
      subst hc
      exact ⟨z, hz, fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · simp [eff] at hc
      rcases hc with rfl | rfl
      · refine ⟨if b < p' then b else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with hb
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W b (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
      · refine ⟨if a < p' then a else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with ha
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W a (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
    · simp at hlen
  · left; rfl

/-- A fan-in-two gate that reads a wire carrying `true`. -/
theorem Rt (H : Gate)
    (hop : H.op = GateOp.and ∨ H.op = GateOp.or ∨ H.op = GateOp.not)
    (hlen : H.inputs.length ≤ 2) (c z p' : ℕ) (hc : c ∈ eff H) (hc' : c < p') (hz : z < p') :
    ∃ q < p', ∀ W : List Bool, W.length = p' →
      W.getD c false = true → W.getD z false = false →
        H.op.eval (H.inputs.map fun i => W.getD i false) = W.getD q false := by
  obtain ⟨op, ins⟩ := H
  simp only at hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [eff] at hc
  · rcases hop with rfl | rfl | rfl <;> simp [eff] at hc <;> subst hc
    · exact ⟨c, hc', fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · exact ⟨c, hc', fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · exact ⟨z, hz, fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
  · rcases hop with rfl | rfl | rfl
    · simp [eff] at hc
      rcases hc with rfl | rfl
      · refine ⟨if b < p' then b else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with hb
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W b (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
      · refine ⟨if a < p' then a else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with ha
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W a (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
    · exact ⟨c, hc', fun W _ h1 h2 => by
        simp [eff] at hc
        rcases hc with rfl | rfl <;> (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · simp [eff] at hc
      subst hc
      exact ⟨z, hz, fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
  · simp at hlen

theorem ofFn_snoc {n : ℕ} (y : Fin n → Bool) (c : Bool) :
    List.ofFn (Fin.snoc y c : Fin (n + 1) → Bool) = List.ofFn y ++ [c] := by
  rw [List.ofFn_succ']; simp

/-- The circuit for the contracted function: one OR gate, then the gates of `C`. -/
def fwd (n : ℕ) (C : Circuit) : Circuit :=
  let ψ : ℕ → ℕ := fun i => if i < n then i else if i = n then n + 2 else i + 2
  ⟨⟨GateOp.or, [n, n + 1]⟩ :: C.gates.map (mapG ψ), ψ C.output⟩

theorem fwd_eval (n : ℕ) (C : Circuit) (y : List Bool) (hy : y.length = n) (a b : Bool) :
    (fwd n C).eval (y ++ [a, b]) = C.eval (y ++ [a || b]) := by
  set ψ : ℕ → ℕ := fun i => if i < n then i else if i = n then n + 2 else i + 2 with hψ
  have hs : step (y ++ [a, b]) ⟨GateOp.or, [n, n + 1]⟩ = (y ++ [a, b]) ++ [a || b] := by
    subst hy
    simp [step, GateOp.eval, List.getD_eq_getElem?_getD]
  rw [Circuit.eval, Circuit.eval, wires_eq, wires_eq]
  simp only [fwd]
  rw [run_cons, hs]
  apply seg ψ ∅ C.gates (y ++ [a || b]) (y ++ [a, b] ++ [a || b]) (by simp)
  · intro i hi; simp at hi ⊢; simp only [hψ]; split_ifs <;> omega
  · intro i hi; simp at hi ⊢; simp only [hψ]; split_ifs <;> omega
  · intro i _
    subst hy
    simp only [hψ]
    split_ifs with h1 h2
    · rw [getD_snoc, if_pos (by simp; omega), getD_snoc, if_pos h1]
      exact List.getD_append _ _ _ _ h1
    · subst h2; simp [List.getD_eq_getElem?_getD]
    · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
  · simp


/-- Contraction can be undone at the cost of one gate: a circuit of size `s + 1` for the
  contracted function gives a circuit of size `s` for `g`. -/
theorem conv (n s : ℕ) (g : (Fin (n + 1) → Bool) → Bool)
    (hdep : ∃ y : Fin n → Bool, g (Fin.snoc y false) ≠ g (Fin.snoc y true))
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ s + 1)
    (heval : ∀ x : Fin (n + 2) → Bool, C.eval (List.ofFn x) =
      g (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc)
        (x (Fin.last n).castSucc || x (Fin.last (n + 1))))) :
    PEqualNP.MetaComplexity.HasCircuitSize (n + 1) g s := by
  obtain ⟨y0, hy0⟩ := hdep
  have key : ∀ (yf : Fin n → Bool) (a b : Bool),
      C.eval (List.ofFn yf ++ [a, b]) = g (Fin.snoc yf (a || b)) := by
    intro yf a b
    have := heval (Fin.snoc (Fin.snoc yf a) b)
    rw [ofFn_snoc, ofFn_snoc] at this
    simpa using this
  have gx : ∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x ++ [false]) = g x := by
    intro x
    have hx : List.ofFn x = List.ofFn (Fin.init x) ++ [x (Fin.last n)] := by
      rw [← ofFn_snoc, Fin.snoc_init_self]
    have := key (Fin.init x) (x (Fin.last n)) false
    rw [Bool.or_false, Fin.snoc_init_self] at this
    rw [hx, List.append_assoc]
    exact this
  have finish : ∀ (l1 l2 : List Gate) (G : Gate), C.gates = l1 ++ G :: l2 →
      (∃ D : Circuit, D.gates.length = l1.length + l2.length ∧
        (∀ g ∈ D.gates, ∃ g0 ∈ l1 ++ l2, g.op = g0.op ∧ g.inputs.length = g0.inputs.length) ∧
        ∀ x : List Bool, x.length = n + 1 →
          D.eval x = (Circuit.mk (l1 ++ G :: l2) C.output).eval (x ++ [false])) →
      PEqualNP.MetaComplexity.HasCircuitSize (n + 1) g s := by
    rintro l1 l2 G hC ⟨D, hlen, hg, hD⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro gt hgt
      obtain ⟨g0, h0, hop, hl⟩ := hg gt hgt
      have := hfan g0 (by rw [hC]; simp only [List.mem_append, List.mem_cons] at h0 ⊢; tauto)
      exact ⟨hop ▸ this.1, hl ▸ this.2⟩
    · simp only [Circuit.size, hC, List.length_append, List.length_cons] at hsize ⊢; omega
    · intro x
      have hCm : Circuit.mk (l1 ++ G :: l2) C.output = C := by rw [← hC]
      rw [hD _ (by simp), hCm]
      exact gx x
  set m := n + 1 with hm
  have lW : ∀ (l : List Gate) (x : List Bool), (run l (x ++ [false])).length =
      x.length + 1 + l.length := by
    intro l x; rw [length_run]; simp
  have Wm : ∀ (l : List Gate) (x : List Bool), x.length = m →
      (run l (x ++ [false])).getD m false = false := by
    intro l x hx
    rw [getD_run_of_lt _ _ _ (by simp; omega), getD_snoc, if_neg (by omega), if_pos hx.symm]
  by_cases hread : ∃ G ∈ C.gates, m ∈ eff G
  · obtain ⟨G, hGmem, hGm⟩ := hread
    obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hGmem
    have hGf := hfan G hGmem
    have hop : G.op = GateOp.and ∨ G.op = GateOp.or ∨ G.op = GateOp.not := by simpa using hGf.1
    rcases Rf G hop hGf.2 m m (m + 1 + l1.length) hGm (by omega) with hnot | ⟨q, hq, hqv⟩
    · obtain ⟨t, ht⟩ : ∃ t, G.inputs = m :: t := by
        rcases hi : G.inputs with _ | ⟨a, t⟩
        · simp [eff, hnot, hi] at hGm
        · simp [eff, hnot, hi] at hGm
          exact ⟨t, by rw [hGm]⟩
      set p := m + 1 + l1.length with hp
      have Gtrue : ∀ x : List Bool, x.length = m →
          G.op.eval (G.inputs.map fun i => (run l1 (x ++ [false])).getD i false) = true := by
        intro x hx
        rw [hnot, ht]
        simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [Wm l1 x hx]
        rfl
      have Wp : ∀ x : List Bool, x.length = m → ∀ k : List Gate,
          (run (l1 ++ G :: k) (x ++ [false])).getD p false = true := by
        intro x hx k
        rw [run_append, run_cons, getD_run_of_lt _ _ _ (by simp [step, lW, hx]; omega), step,
          getD_snoc, if_neg (by rw [lW, hx]; omega), if_pos (by rw [lW, hx])]
        exact Gtrue x hx
      by_cases hout : C.output = p
      · exfalso
        apply hy0
        have hT : ∀ x : List Bool, x.length = m → C.eval (x ++ [false]) = true := by
          intro x hx
          rw [Circuit.eval, wires_eq, hsplit, hout]
          exact Wp x hx l2
        rw [← gx, ← gx, hT _ (by simp [hm]), hT _ (by simp [hm])]
      · by_cases hH : ∃ H ∈ l2, p ∈ eff H
        · obtain ⟨H, hHmem, hHp⟩ := hH
          obtain ⟨k1, k2, hk⟩ := List.append_of_mem hHmem
          have hC' : C.gates = (l1 ++ G :: k1) ++ H :: k2 := by rw [hsplit, hk]; simp
          have hHf := hfan H (by rw [hC']; simp)
          have hopH : H.op = GateOp.and ∨ H.op = GateOp.or ∨ H.op = GateOp.not := by
            simpa using hHf.1
          obtain ⟨q, hq, hqv⟩ := Rt H hopH hHf.2 p m (p + 1 + k1.length) hHp (by omega)
            (by omega)
          apply finish _ _ _ hC'
          refine drop m (l1 ++ G :: k1) k2 H C.output q ∅ (by simp; omega) (by simp) (by simp)
            (by simp) ?_
          intro _ x hx
          exact hqv _ (by rw [lW, hx]; simp; omega) (Wp x hx k1) (Wm _ x hx)
        · push_neg at hH
          apply finish l1 l2 G hsplit
          refine drop m l1 l2 G C.output m {p} (by omega) (by simp [hp]) ?_ (by simpa using hout) ?_
          · intro g' hg' i hi
            simp only [Set.mem_singleton_iff]
            rintro rfl
            exact hH g' hg' hi
          · intro h
            exact (h (Set.mem_singleton p)).elim
    · apply finish l1 l2 G hsplit
      refine drop m l1 l2 G C.output q ∅ hq (by simp) (by simp) (by simp) ?_
      intro _ x hx
      exact hqv _ (by rw [lW, hx]) (Wm l1 x hx) (Wm l1 x hx)
  · push_neg at hread
    exfalso
    by_cases hom : C.output = m
    · have hb : ∀ a b : Bool, C.eval (List.ofFn y0 ++ [a, b]) = b := by
        intro a b
        rw [Circuit.eval, wires_eq, hom, getD_run_of_lt _ _ _ (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, hm]
      have e1 := key y0 true false
      have e2 := key y0 false true
      rw [hb] at e1 e2
      simp only [Bool.true_or, Bool.false_or] at e1 e2
      rw [← e1] at e2
      exact absurd e2 (by decide)
    · have split : ∀ b : Bool, List.ofFn y0 ++ [false, b] = (List.ofFn y0 ++ [false]) ++ [b] := by
        intro b; simp
      have hs := seg id {m} C.gates (List.ofFn y0 ++ [false, false])
        (List.ofFn y0 ++ [false, true])
        (fun g' hg' i hi h => hread g' hg' (by rw [Set.mem_singleton_iff] at h; rw [← h]; exact hi))
        (by intro i _; simp)
        (by intro i hi; left; simpa using hi)
        (by
          intro i hi
          rw [Set.mem_singleton_iff] at hi
          show (List.ofFn y0 ++ [false, true]).getD i false =
            (List.ofFn y0 ++ [false, false]).getD i false
          have e : ∀ b : Bool, (List.ofFn y0 ++ [false, b]).getD i false =
              if i < (List.ofFn y0 ++ [false]).length then (List.ofFn y0 ++ [false]).getD i false
              else if i = (List.ofFn y0 ++ [false]).length then b else false := by
            intro b; rw [split b]; exact getD_snoc _ b i
          rw [e, e]
          by_cases h : i < (List.ofFn y0 ++ [false]).length
          · rw [if_pos h, if_pos h]
          · have : i ≠ (List.ofFn y0 ++ [false]).length := by simp; omega
            rw [if_neg h, if_neg h, if_neg this, if_neg this])
        C.output (by simpa using hom)
      rw [mapG_id_map] at hs
      have h1 := key y0 false true
      have h0 := key y0 false false
      rw [Circuit.eval, wires_eq] at h1 h0
      simp only [id] at hs
      rw [hs, h0] at h1
      exact hy0 (by simpa using h1)

end PEqualNP.Outside.L_meta_176_aux

open PEqualNP.Outside.L_meta_176_aux in
theorem PEqualNP.Outside.L_meta_176 : ∀ (n s : ℕ) (g : (Fin (n + 1) → Bool) → Bool), (∃ y : Fin n → Bool, g (Fin.snoc y false) ≠ g (Fin.snoc y true)) → (PEqualNP.MetaComplexity.HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => g (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc) (x (Fin.last n).castSucc || x (Fin.last (n + 1))))) (s + 1) ↔ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) g s) := by
  intro n s g hdep
  constructor
  · rintro ⟨C, hfan, hsize, heval⟩
    exact conv n s g hdep C hfan hsize heval
  · rintro ⟨C, hfan, hsize, heval⟩
    refine ⟨fwd n C, ?_, ?_, ?_⟩
    · intro gt hgt
      simp only [fwd, List.mem_cons, List.mem_map] at hgt
      rcases hgt with rfl | ⟨g0, h0, rfl⟩
      · simp
      · exact ⟨(hfan g0 h0).1, by simpa [mapG] using (hfan g0 h0).2⟩
    · simp only [fwd, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_cons, List.length_map] at hsize ⊢
      omega
    · intro x
      have hx : List.ofFn x = List.ofFn (fun i : Fin n => x i.castSucc.castSucc) ++
          [x (Fin.last n).castSucc, x (Fin.last (n + 1))] := by
        rw [List.ofFn_succ', List.ofFn_succ']
        simp
      rw [hx, fwd_eval n C _ (by simp), ← ofFn_snoc, heval]
