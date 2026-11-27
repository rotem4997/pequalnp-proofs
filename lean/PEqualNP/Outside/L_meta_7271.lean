import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7271
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def ren (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def rg (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren n m p)⟩

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

theorem evalT (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem evalb (b : Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = b → f' i = b) :
    op.eval (ins.map f) = b → op.eval (ins.map f') = b := by
  cases b
  · intro hf
    by_contra hc
    have hc' : op.eval (ins.map f') = true := by simpa using hc
    have h3 := evalT op hop ins f' f (fun i hi => by
      by_contra hn
      have h4 := h i (by simpa using hn)
      rw [h4] at hi
      exact absurd hi (by simp)) hc'
    rw [hf] at h3
    exact absurd h3 (by simp)
  · exact evalT op hop ins f f' h

theorem simb (b : Bool) (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U U' : List Bool, U.length = U'.length + 1 → n + m < U.length →
    (p < n + m ∨ U'.length + B.length < p) →
    (∀ i, U.getD i false = b → U'.getD (ren n m p i) false = b) →
    ∀ i, (wf B U).getD i false = b → (wf (B.map (rg n m p)) U').getD (ren n m p i) false = b := by
  induction B with
  | nil => intro U U' _ _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hbig hp h i
    rw [List.map_cons, wf_cons, wf_cons]
    refine ih (fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
      (by simp; omega) ?_ ?_ i
    · rcases hp with hp | hp
      · exact Or.inl hp
      · right
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
    · intro t ht
      have hv : g.op.eval (g.inputs.map fun i => U.getD i false) = b →
          (rg n m p g).op.eval ((rg n m p g).inputs.map fun i => U'.getD i false) = b := by
        intro hb
        show g.op.eval ((g.inputs.map (ren n m p)).map fun i => U'.getD i false) = b
        rw [List.map_map]
        exact evalb b g.op (hB g (List.mem_cons_self ..)) g.inputs _ _ (fun i hi => h i hi) hb
      rcases Nat.lt_trichotomy t U.length with htl | htl | htl
      · rw [getD_snoc_lt _ _ _ htl] at ht
        have h0 := h t ht
        by_cases htm : t = n + m
        · have e : ren n m p t = p := by unfold ren; rw [if_pos htm]
          rw [e] at h0 ⊢
          rcases hp with hp | hp
          · rw [getD_snoc_lt _ _ _ (by omega)]; exact h0
          · simp only [List.length_cons] at hp
            rw [getD_snoc_gt _ _ _ (by omega)]
            rw [List.getD_eq_default _ _ (by omega)] at h0
            exact h0
        · have h1 : ren n m p t < U'.length := by
            unfold ren
            rw [if_neg htm]
            split <;> omega
          rw [getD_snoc_lt _ _ _ h1]; exact h0
      · subst htl
        rw [getD_snoc_eq] at ht
        have e : ren n m p U.length = U'.length := by
          unfold ren
          rw [if_neg (by omega), if_pos hbig]
          omega
        rw [e, getD_snoc_eq]; exact hv ht
      · rw [getD_snoc_gt _ _ _ htl] at ht
        have e : U'.length < ren n m p t := by
          unfold ren
          rw [if_neg (by omega), if_pos (by omega)]
          omega
        rw [getD_snoc_gt _ _ _ e]; exact ht

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hml : m < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C m p
      = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hml]
  rfl

theorem erase_sim (n : ℕ) (C : Circuit) (m p : ℕ) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hml : m < C.gates.length) (hp : p < n + m ∨ p = n + C.gates.length) (x : List Bool)
    (hx : x.length = n) (b : Bool)
    (hb : (wf C.gates x).getD (n + m) false = b → (wf C.gates x).getD p false = b) (w : ℕ)
    (hw : (wf C.gates x).getD w false = b) :
    (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)) x).getD (ren n m p w) false = b := by
  have h2 : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hml, List.take_append_drop]
  have hWlen : (wf (C.gates.take m) x).length = n + m := by
    rw [wf_len, hx, List.length_take, Nat.min_eq_left (le_of_lt hml)]
  have e1 : wf C.gates x = wf (C.gates.drop (m + 1))
      (wf (C.gates.take m) x ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false)]) := by
    conv_lhs => rw [h2]
    rw [wf_append, wf_cons]
  have hfull : (wf C.gates x).length = n + C.gates.length := by rw [wf_len, hx]
  rw [wf_append]
  rw [e1] at hw hb
  have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := List.length_drop
  refine simb b n m p (C.gates.drop (m + 1))
    (fun g hg => (hm g (List.mem_of_mem_drop hg)).1) _ _ (by simp) (by simp; omega) ?_ ?_ w hw
  · rcases hp with hp | hp
    · exact Or.inl hp
    · right; rw [hWlen, hdl, hp]; omega
  · intro i hi
    unfold ren
    split
    · rename_i hinm
      subst hinm
      rw [wf_keep _ _ _ (by simp; omega)] at hb
      have h3 := hb hi
      rcases hp with hp | hp
      · rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)] at h3
        exact h3
      · rw [← e1, List.getD_eq_default _ _ (by rw [hfull, hp])] at h3
        rw [List.getD_eq_default _ _ (by rw [hWlen, hp]; omega)]
        exact h3
    · split
      · rw [getD_snoc_gt _ _ _ (by omega)] at hi
        rw [List.getD_eq_default _ _ (by omega)]
        exact hi
      · rw [getD_snoc_lt _ _ _ (by omega)] at hi
        exact hi

theorem gate_in (n : ℕ) (C : Circuit) (m p : ℕ) (hml : m < C.gates.length)
    (hop : C.gates[m].op = GateOp.and ∨ C.gates[m].op = GateOp.or) (hpin : p ∈ C.gates[m].inputs)
    (hp : p < n + m) (x : List Bool) (hx : x.length = n) :
    (wf C.gates x).getD (n + m) false = C.gates[m].op.eval [] →
    (wf C.gates x).getD p false = C.gates[m].op.eval [] := by
  subst hx
  rw [gate_val C.gates x m hml, wire_take C.gates x m p hp (le_of_lt hml)]
  rcases hop with h | h
  · rw [h]
    show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).all id = true → _ = true
    intro hall
    exact List.all_eq_true.1 hall _ (List.mem_map.2 ⟨p, hpin, rfl⟩)
  · rw [h]
    show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id = false → _ = false
    intro hany
    cases hq : (wf (C.gates.take m) x).getD p false
    · rfl
    · exfalso
      have h5 : (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id = true :=
        List.any_eq_true.2 ⟨true, List.mem_map.2 ⟨p, hpin, hq⟩, rfl⟩
      rw [h5] at hany
      exact absurd hany (by simp)

def normG (φ : ℕ → Gate → Gate) : ℕ → List Gate → List Gate
  | _, [] => []
  | L, g :: t => φ L g :: normG φ (L + 1) t

theorem normG_len (φ : ℕ → Gate → Gate) : ∀ (gs : List Gate) (L : ℕ),
    (normG φ L gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro L; rfl
  | cons g t ih => intro L; simp [normG, ih]

theorem normG_mem (φ : ℕ → Gate → Gate) : ∀ (gs : List Gate) (L j : ℕ)
    (hj : j < (normG φ L gs).length), ∃ g ∈ gs, (normG φ L gs)[j] = φ (L + j) g := by
  intro gs
  induction gs with
  | nil => intro L j hj; simp [normG] at hj
  | cons g t ih =>
    intro L j hj
    cases j with
    | zero => exact ⟨g, by simp, by simp [normG]⟩
    | succ j =>
      have hj' : j < (normG φ (L + 1) t).length := by simpa [normG] using hj
      obtain ⟨g', hg', he⟩ := ih (L + 1) j hj'
      refine ⟨g', by simp [hg'], ?_⟩
      simp only [normG, List.getElem_cons_succ]
      rw [he]
      congr 1
      omega

theorem normG_wf (φ : ℕ → Gate → Gate) (Q : List Bool → Prop) (R : Gate → Prop)
    (hQ : ∀ U v, Q U → Q (U ++ [v]))
    (hφ : ∀ U g, Q U → R g →
      (φ U.length g).op.eval ((φ U.length g).inputs.map fun i => U.getD i false)
        = g.op.eval (g.inputs.map fun i => U.getD i false)) :
    ∀ (gs : List Gate) (U : List Bool), Q U → (∀ g ∈ gs, R g) →
      wf (normG φ U.length gs) U = wf gs U := by
  intro gs
  induction gs with
  | nil => intro U _ _; rfl
  | cons g t ih =>
    intro U hU hR
    show wf (φ U.length g :: normG φ (U.length + 1) t) U = wf (g :: t) U
    rw [wf_cons, wf_cons, hφ U g hU (hR g (by simp))]
    have h := ih (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)]) (hQ _ _ hU)
      (fun g' hg' => hR g' (by simp [hg']))
    simpa using h

theorem wf_pad (d : ℕ) : ∀ U : List Bool,
    wf (List.replicate d (⟨GateOp.or, []⟩ : Gate)) U = U ++ List.replicate d false := by
  induction d with
  | zero => intro U; simp [wf]
  | succ d ih =>
    intro U
    rw [List.replicate_succ, wf_cons, ih]
    simp [GateOp.eval, List.replicate_succ]

theorem getD_pad (W : List Bool) (d w : ℕ) :
    (W ++ List.replicate d false).getD w false = W.getD w false := by
  by_cases h : w < W.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default W _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : W.length ≤ w),
      List.getElem?_replicate]
    split <;> rfl

def fwd (L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if ∀ i ∈ g.inputs, i < L then g else ⟨GateOp.or, []⟩
  | _ => ⟨g.op, g.inputs.filter fun i => decide (i < L)⟩

theorem fwd_and (L : ℕ) (g : Gate) (h : g.op = GateOp.and) :
    fwd L g = if ∀ i ∈ g.inputs, i < L then g else ⟨GateOp.or, []⟩ := by
  obtain ⟨op, ins⟩ := g
  simp only at h
  subst h
  rfl

theorem fwd_or (L : ℕ) (g : Gate) (h : g.op = GateOp.or) :
    fwd L g = ⟨GateOp.or, g.inputs.filter fun i => decide (i < L)⟩ := by
  obtain ⟨op, ins⟩ := g
  simp only at h
  subst h
  rfl

theorem any_filter (ins : List ℕ) (L : ℕ) (f : ℕ → Bool) (h : ∀ i, ¬ i < L → f i = false) :
    ((ins.filter fun i => decide (i < L)).map f).any id = (ins.map f).any id := by
  induction ins with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a < L
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, ih]
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, h a ha, ih]
      simp

theorem fwd_legal (L : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    ((fwd L g).op = GateOp.and ∨ (fwd L g).op = GateOp.or) ∧ (fwd L g).inputs.length ≤ 2 ∧
      ∀ i ∈ (fwd L g).inputs, i < L := by
  rcases hop with h | h
  · rw [fwd_and L g h]
    split
    · rename_i hall
      exact ⟨Or.inl h, hlen, hall⟩
    · exact ⟨Or.inr rfl, by simp, by simp⟩
  · rw [fwd_or L g h]
    exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) hlen,
      fun i hi => by simpa using (List.mem_filter.1 hi).2⟩

theorem fwd_eval (U : List Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (fwd U.length g).op.eval ((fwd U.length g).inputs.map fun i => U.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) := by
  rcases hop with h | h
  · rw [fwd_and _ g h]
    split
    · rfl
    · rename_i hall
      push_neg at hall
      obtain ⟨i, hi, hiL⟩ := hall
      rw [h]
      have h0 : (g.inputs.map fun i => U.getD i false).all id = false := by
        rw [List.all_eq_false]
        exact ⟨false, List.mem_map.2 ⟨i, hi, List.getD_eq_default _ _ (by omega)⟩, by simp⟩
      show ([] : List Bool).any id = (g.inputs.map fun i => U.getD i false).all id
      rw [h0]
      rfl
  · rw [fwd_or _ g h, h]
    show ((g.inputs.filter fun i => decide (i < U.length)).map fun i => U.getD i false).any id
      = (g.inputs.map fun i => U.getD i false).any id
    exact any_filter g.inputs U.length _ (fun i hi => List.getD_eq_default _ _ (by omega))

theorem snoc2 (U V : List Bool) (hl : U.length = V.length)
    (h : ∀ i, U.getD i false = true → V.getD i false = true) (u v : Bool) (huv : u = true → v = true) :
    ∀ i, (U ++ [u]).getD i false = true → (V ++ [v]).getD i false = true := by
  intro i hi
  rcases Nat.lt_trichotomy i U.length with h1 | h1 | h1
  · rw [getD_snoc_lt _ _ _ h1] at hi
    rw [getD_snoc_lt _ _ _ (by omega)]
    exact h i hi
  · subst h1
    rw [getD_snoc_eq] at hi
    rw [hl, getD_snoc_eq]
    exact huv hi
  · rw [getD_snoc_gt _ _ _ h1] at hi
    exact absurd hi (by simp)

theorem set_mono : ∀ (gs : List Gate) (m : ℕ) (U V : List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (wf (gs.set m ⟨GateOp.or, []⟩) U).getD i false = true → (wf gs V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro m U V _ _ h i hi; exact h i hi
  | cons g t ih =>
    intro m U V hleg hl h i hi
    have hleg' : ∀ g' ∈ t, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hleg g' (List.mem_cons_of_mem _ hg')
    cases m with
    | zero =>
      rw [List.set_cons_zero, wf_cons] at hi
      rw [wf_cons]
      exact mono2 t hleg' _ _ (by simp [hl])
        (snoc2 U V hl h _ _ (fun hf => absurd hf (by simp [GateOp.eval]))) i hi
    | succ m =>
      rw [List.set_cons_succ, wf_cons] at hi
      rw [wf_cons]
      exact ih m _ _ hleg' (by simp [hl])
        (snoc2 U V hl h _ _ (eval_mono g.op (hleg g (by simp)).1 g.inputs U V h)) i hi

end PEqualNP.Outside.L_meta_7271

open PEqualNP.Outside.L_meta_7271 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7271 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     x3 < x2.size →       have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates.set x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ x7.size < x2.size ∧ ∀ (x8 : List Bool), x8.length = x1 → x7.eval x8 = x6.eval x8 ∧ (x7.eval x8 = Bool.true → x2.eval x8 = Bool.true) := by
  intro n C m hC hmlt E6
  obtain ⟨hao, _, h2⟩ := hC
  have hml : m < C.gates.length := hmlt
  have hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨hao g hg, by rw [h2 g hg]⟩
  have hlen6 : (C.gates.set m (⟨GateOp.or, []⟩ : Gate)).length = C.gates.length := by simp
  have hml6 : m < (C.gates.set m (⟨GateOp.or, []⟩ : Gate)).length := by rw [hlen6]; exact hml
  have hleg6 : ∀ g ∈ C.gates.set m (⟨GateOp.or, []⟩ : Gate),
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hleg g h
    · rw [h]; exact ⟨Or.inr rfl, by simp⟩
  have hm6 : PEqualNP.MetaComplexity.Monotone2 ⟨C.gates.set m (⟨GateOp.or, []⟩ : Gate), C.output⟩ := by
    intro g hg
    have := hleg6 g hg
    refine ⟨?_, this.2⟩
    rcases this.1 with h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  have hg6 : (C.gates.set m (⟨GateOp.or, []⟩ : Gate))[m] = ⟨GateOp.or, []⟩ := by simp
  have hE6 : E6 = ⟨C.gates.set m (⟨GateOp.or, []⟩ : Gate), C.output⟩ := rfl
  clear_value E6
  subst hE6
  have hEg : ∀ g ∈ (C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
      ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length)),
      g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact (hleg6 g (List.mem_of_mem_take hg)).1
    · exact (hleg6 g0 (List.mem_of_mem_drop hg0)).1
  have hEl : ∀ g ∈ (C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
      ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length)),
      g.inputs.length ≤ 2 := by
    intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact (hleg6 g (List.mem_of_mem_take hg)).2
    · simpa [rg] using (hleg6 g0 (List.mem_of_mem_drop hg0)).2
  have hElen : ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
      ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length))).length + 1
      = C.gates.length := by
    simp
    omega
  refine ⟨⟨normG fwd n ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
      ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length))),
    ren n m (n + C.gates.length) C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨g0, hg0, he⟩ := normG_mem fwd _ n j hj
    rw [he]
    have fl := fwd_legal (n + j) g0 (hEg g0 hg0) (hEl g0 hg0)
    refine ⟨?_, fl.2.1⟩
    rcases fl.1 with h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  · intro j hj i hi
    have hj' : j < (normG fwd n ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
      ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length)))).length := hj
    rw [gateAt_eq _ j hj'] at hi
    obtain ⟨g0, hg0, he⟩ := normG_mem fwd _ n j hj'
    have hi' : i ∈ ((normG fwd n ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
      ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length))))[j]).inputs := hi
    rw [he] at hi'
    exact (fwd_legal (n + j) g0 (hEg g0 hg0) (hEl g0 hg0)).2.2 i hi'
  · show (normG fwd n _).length < C.gates.length
    rw [normG_len]
    omega
  · intro x hx
    have hD : (wf (normG fwd n ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
        ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length)))) x)
        = wf ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
        ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length))) x := by
      have h := normG_wf fwd (fun _ => True) (fun g => g.op = GateOp.and ∨ g.op = GateOp.or)
        (fun _ _ _ => trivial) (fun U g _ hr => fwd_eval U g hr) _ x trivial hEg
      rw [hx] at h
      exact h
    have hv : (wf (C.gates.set m (⟨GateOp.or, []⟩ : Gate)) x).getD (n + m) false = false := by
      have h := gate_val (C.gates.set m (⟨GateOp.or, []⟩ : Gate)) x m hml6
      rw [hx] at h
      rw [h, hg6]
      rfl
    have hp : (wf (C.gates.set m (⟨GateOp.or, []⟩ : Gate)) x).getD (n + C.gates.length) false = false :=
      List.getD_eq_default _ _ (by rw [wf_len, hlen6, hx])
    have hsim := erase_sim n ⟨C.gates.set m (⟨GateOp.or, []⟩ : Gate), C.output⟩ m (n + C.gates.length)
      hm6 hml6 (Or.inr (by show n + C.gates.length = n + (C.gates.set m _).length; rw [hlen6])) x hx _
      (fun h => by
        show (wf (C.gates.set m (⟨GateOp.or, []⟩ : Gate)) x).getD (n + C.gates.length) false = _
        rw [hp, ← h]
        exact hv.symm) C.output rfl
    have heq : (wf (normG fwd n ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).take m ++
        ((C.gates.set m (⟨GateOp.or, []⟩ : Gate)).drop (m + 1)).map (rg n m (n + C.gates.length)))) x).getD
        (ren n m (n + C.gates.length) C.output) false
        = (wf (C.gates.set m (⟨GateOp.or, []⟩ : Gate)) x).getD C.output false := by
      rw [hD]
      exact hsim
    refine ⟨heq, fun ht => ?_⟩
    have ht' : (wf (C.gates.set m (⟨GateOp.or, []⟩ : Gate)) x).getD C.output false = true := by
      rw [← heq]; exact ht
    exact set_mono C.gates m x x hleg rfl (fun _ h => h) C.output ht'
