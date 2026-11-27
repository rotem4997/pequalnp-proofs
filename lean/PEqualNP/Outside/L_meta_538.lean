import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace L538A

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

lemma getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

lemma foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

lemma eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

lemma getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

lemma getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

lemma deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

lemma del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

lemma del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

lemma del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

lemma del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma fanInTwo_del (G : List Gate) (o : ℕ) (t p r o' : ℕ) (h : FanInTwo ⟨G, o⟩) :
    FanInTwo ⟨del G t p r, o'⟩ := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [renG] using h2⟩

def src : Gate := ⟨GateOp.and, []⟩

def plus (C : Circuit) : Circuit := ⟨src :: C.gates, C.output⟩

lemma ofFn_snoc {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma plus_foldl (C : Circuit) {n : ℕ} (y : Fin n → Bool) :
    (plus C).gates.foldl step (List.ofFn y) = C.gates.foldl step (List.ofFn (Fin.snoc y true)) := by
  simp only [plus, List.foldl_cons, step, src, GateOp.eval, List.map_nil, List.all_nil, ofFn_snoc]

lemma plus_circuitFun (C : Circuit) (n : ℕ) :
    circuitFun n (plus C) = fun y => circuitFun (n + 1) C (Fin.snoc y true) := by
  funext y
  simp only [circuitFun, Circuit.eval, wires_eq, plus_foldl]
  rfl

lemma plus_fanInTwo (C : Circuit) (h : FanInTwo C) : FanInTwo (plus C) := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [plus, List.mem_cons] at hg
  rcases hg with rfl | hg
  · simp [src]
  · exact h g hg

lemma plus_size (C : Circuit) : (plus C).size = C.size + 1 := by
  simp [plus, Circuit.size]

lemma plus_getD_src (C : Circuit) {n : ℕ} (y : Fin n → Bool) :
    ((plus C).gates.foldl step (List.ofFn y)).getD n false = true := by
  rw [plus_foldl, ofFn_snoc, foldl_step_getD _ _ _ (by simp), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

lemma foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

lemma gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

lemma del_getElem_lt (G : List Gate) (t p r t' : ℕ) (h : t' < t) (ht : t < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r ht]; omega) = G[t']'(by omega) := by
  simp only [del]
  rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]

lemma del_getElem_ge (G : List Gate) (t p r t' : ℕ) (h : t ≤ t') (ht : t' + 1 < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r (by omega)]; omega) = renG p r (G[t' + 1]'ht) := by
  simp only [del]
  rw [List.getElem_append_right (by simp [List.length_take]; omega), List.getElem_map, List.getElem_drop]
  congr 2
  simp [List.length_take]
  omega

end L538A

namespace L538B

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

private lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

private lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

private lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

private lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this


end L538B


def L538_sh (jg j : ℕ) : ℕ := if j < jg then j else j + 1

def L538_sg (n p jg i : ℕ) : ℕ := if i = p then n + jg else if n + jg ≤ i then i + 1 else i

def L538_Ins (n p jg : ℕ) (C C' : Circuit) : Prop :=
  C.gates.length = C'.gates.length + 1 ∧ jg ≤ C'.gates.length ∧
  (∀ j < C'.gates.length, gateAt C (L538_sh jg j) =
    ⟨(gateAt C' j).op, (gateAt C' j).inputs.map (L538_sg n p jg)⟩) ∧
  C.output = L538_sg n p jg C'.output ∧
  (∀ j < jg, p ∉ (gateAt C' j).inputs)













lemma L538_del_gate_lt (C : Circuit) (jg r : ℕ) (n : ℕ) (hj : jg < C.gates.length) (j : ℕ) (h : j < jg) :
    gateAt ⟨L538A.del C.gates jg (n + jg) r, L538A.ren (n + jg) r C.output⟩ j = gateAt C j := by
  unfold gateAt
  simp only
  have h1 : j < (L538A.del C.gates jg (n + jg) r).length := by
    rw [L538A.del_length _ _ _ _ hj]; omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ (by omega),
    L538A.del_getElem_lt _ _ _ _ _ h hj]

lemma L538_del_gate_ge (C : Circuit) (jg r : ℕ) (n : ℕ) (hj : jg < C.gates.length) (j : ℕ) (h : jg ≤ j)
    (hj2 : j + 1 < C.gates.length) :
    gateAt ⟨L538A.del C.gates jg (n + jg) r, L538A.ren (n + jg) r C.output⟩ j =
      L538A.renG (n + jg) r (gateAt C (j + 1)) := by
  unfold gateAt
  simp only
  have h1 : j < (L538A.del C.gates jg (n + jg) r).length := by
    rw [L538A.del_length _ _ _ _ hj]; omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hj2,
    L538A.del_getElem_ge _ _ _ _ _ h hj2]

lemma L538_gate_val {n : ℕ} (C : Circuit) (jg : ℕ) (hj : jg < C.gates.length) (a b : ℕ)
    (hab : a < n + jg ∧ b < n + jg) (hg : gateAt C jg = ⟨GateOp.and, [a, b]⟩) (x : List Bool)
    (hx : x.length = n) :
    (C.wires x).getD (n + jg) false = ((C.wires x).getD a false && (C.wires x).getD b false) := by
  rw [L538A.wires_eq]
  have := L538A.gate_value C.gates x jg hj
  rw [hx] at this
  rw [this]
  have hg' : C.gates[jg] = ⟨GateOp.and, [a, b]⟩ := by
    unfold gateAt at hg; rw [List.getD_eq_getElem _ _ hj] at hg; exact hg
  rw [hg']
  simp [GateOp.eval, hab.1, hab.2]

lemma L538_wire_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  rw [L538A.wires_eq, L538A.foldl_step_getD _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma L538_wire_rec (C : Circuit) (X : List Bool) (i : ℕ) :
    (C.wires X).getD i false =
      if i < X.length then X.getD i false
      else if i - X.length < C.gates.length then
        (gateAt C (i - X.length)).op.eval ((gateAt C (i - X.length)).inputs.map
          (fun k => if k < i then (C.wires X).getD k false else false))
      else false := by
  rw [L538A.wires_eq]
  split_ifs with h1 h2
  · exact L538A.foldl_step_getD _ _ _ h1
  · have hi : i = X.length + (i - X.length) := by omega
    have := L538A.gate_value C.gates X (i - X.length) h2
    rw [← hi] at this
    rw [this]
    unfold gateAt
    rw [List.getD_eq_getElem _ _ h2]
  · apply L538A.getD_of_length_le
    rw [L538A.foldl_step_length]; omega

lemma L538_noread {n : ℕ} (C' : Circuit) (l : Fin n)
    (hl : ∀ j < C'.gates.length, l.val ∉ L538A.deps (gateAt C' j)) (ho : C'.output ≠ l.val)
    (x : Fin n → Bool) (b : Bool) :
    circuitFun n C' (Function.update x l b) = circuitFun n C' x := by
  have key : ∀ i, i ≠ l.val → (C'.wires (List.ofFn (Function.update x l b))).getD i false =
      (C'.wires (List.ofFn x)).getD i false := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rw [L538_wire_rec C' _ i, L538_wire_rec C' _ i]
      simp only [List.length_ofFn]
      split_ifs with h1 h2
      · rw [List.getD_eq_getElem _ _ (by simp; exact h1), List.getD_eq_getElem _ _ (by simp; exact h1),
          List.getElem_ofFn, List.getElem_ofFn]
        rw [Function.update_of_ne]
        intro h; apply hi; rw [← h]
      · apply L538A.eval_congr
        intro k hk
        split_ifs with h3
        · exact ih k h3 (fun h => hl _ h2 (h ▸ hk))
        · rfl
      · rfl
  exact key _ ho

lemma L538_ins_eval {n : ℕ} (C C' : Circuit) (l p : Fin n) (jg : ℕ) (hI : L538_Ins n p jg C C')
    (hg : gateAt C jg = ⟨GateOp.and, [l.val, p.val]⟩ ∨ gateAt C jg = ⟨GateOp.and, [p.val, l.val]⟩)
    (x : Fin n → Bool) :
    circuitFun n C x = circuitFun n C' (Function.update x p (x l && x p)) := by
  obtain ⟨hlen, hjg, hgate, hout, hpre⟩ := hI
  set W := C.wires (List.ofFn x) with hW
  set x' := Function.update x p (x l && x p) with hx'
  set W' := C'.wires (List.ofFn x') with hW'
  have hpn := p.isLt
  have hln := l.isLt
  have hgv : W.getD (n + jg) false = (x l && x p) := by
    rcases hg with hg | hg
    · rw [hW, L538_gate_val C jg (by omega) l.val p.val ⟨by omega, by omega⟩ hg _ (by simp),
        L538_wire_input, L538_wire_input]
    · rw [hW, L538_gate_val C jg (by omega) p.val l.val ⟨by omega, by omega⟩ hg _ (by simp),
        L538_wire_input, L538_wire_input, Bool.and_comm]
  have key : ∀ i, W.getD (L538_sg n p jg i) false = W'.getD i false := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hin : i < n
      · by_cases hip : i = p.val
        · subst hip
          simp only [L538_sg, if_true]
          rw [hgv, hW', L538_wire_input, hx', Function.update_self]
        · have hs : L538_sg n p jg i = i := by
            simp only [L538_sg, hip, if_false]; rw [if_neg (by omega)]
          rw [hs, hW, hW', L538_wire_input C x ⟨i, hin⟩, L538_wire_input C' x' ⟨i, hin⟩, hx',
            Function.update_of_ne (fun h => hip (by rw [← h]))]
      · by_cases hil : i - n < C'.gates.length
        · set j := i - n with hj
          have hs : L538_sg n p jg i = n + L538_sh jg j := by
            simp only [L538_sg, L538_sh]
            rw [if_neg (by omega)]
            split_ifs <;> omega
          rw [hs, hW, hW', L538_wire_rec C _ (n + L538_sh jg j), L538_wire_rec C' _ i]
          simp only [List.length_ofFn]
          have hshl : L538_sh jg j < C.gates.length := by
            simp only [L538_sh]; split_ifs <;> omega
          rw [if_neg (by omega), if_pos (by omega), if_neg hin, if_pos hil]
          simp only [Nat.add_sub_cancel_left]
          rw [hgate j hil]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro k hk
          simp only [Function.comp]
          by_cases hkp : k = p.val
          · subst hkp
            by_cases hjj : j < jg
            · exact absurd hk (hpre j hjj)
            · have e1 : L538_sg n p jg p.val = n + jg := by simp [L538_sg]
              rw [e1, if_pos (by simp only [L538_sh]; split_ifs <;> omega), if_pos (by omega)]
              rw [← e1]
              exact ih p.val (by omega)
          · by_cases hkg : n + jg ≤ k
            · have e1 : L538_sg n p jg k = k + 1 := by simp [L538_sg, hkp, hkg]
              rw [e1]
              by_cases hki : k < i
              · rw [if_pos (by simp only [L538_sh]; split_ifs <;> omega), if_pos hki, ← e1]
                exact ih k hki
              · rw [if_neg (by simp only [L538_sh]; split_ifs <;> omega), if_neg hki]
            · have e1 : L538_sg n p jg k = k := by simp [L538_sg, hkp, hkg]
              by_cases hki : k < i
              · rw [e1, if_pos (by simp only [L538_sh]; split_ifs <;> omega), if_pos hki]
                have := ih k hki
                rw [e1] at this
                exact this
              · rw [e1, if_neg (by simp only [L538_sh]; split_ifs <;> omega), if_neg hki]
        · have hs : L538_sg n p jg i = i + 1 := by
            simp only [L538_sg]
            rw [if_neg (by omega), if_pos (by omega)]
          rw [hs, hW, hW', L538_wire_rec C _ (i + 1), L538_wire_rec C' _ i]
          simp only [List.length_ofFn]
          rw [if_neg (by omega), if_neg (by omega), if_neg hin, if_neg hil]
  show W.getD C.output false = W'.getD C'.output false
  rw [hout]
  exact key _

lemma L538_ins_fan {n : ℕ} (C C' : Circuit) (p jg : ℕ) (hI : L538_Ins n p jg C C')
    (hg : (gateAt C jg).op = GateOp.and ∧ (gateAt C jg).inputs.length = 2) (h' : FanInTwo C') :
    FanInTwo C ∧ C.size = C'.size + 1 := by
  obtain ⟨hlen, hjg, hgate, hout, hpre⟩ := hI
  refine ⟨?_, hlen⟩
  intro g hg'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have hgj : C.gates[j] = gateAt C j := by
    unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
  rw [hgj]
  by_cases hjg' : j = jg
  · subst hjg'
    rw [hg.1, hg.2]
    exact ⟨Or.inl rfl, le_refl 2⟩
  · set j' := if j < jg then j else j - 1 with hj'
    have hj'l : j' < C'.gates.length := by simp only [hj']; split_ifs <;> omega
    have hsh : L538_sh jg j' = j := by simp only [hj', L538_sh]; split_ifs <;> omega
    rw [← hsh, hgate j' hj'l]
    have hm : gateAt C' j' ∈ C'.gates := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hj'l]; exact List.getElem_mem hj'l
    obtain ⟨h1, h2⟩ := h' _ hm
    exact ⟨h1, by simpa using h2⟩



lemma L538_dec {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (x : Fin n → Bool) :
    graphFun K ∅ x = true ↔ (x l = true ∧ x p = true) ∨
      ∃ u v, K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p ∧ x u = true ∧ x v = true := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    by_cases h1 : u = l
    · subst h1; have := (hl v).1 huv; subst this; exact Or.inl ⟨hu, hv⟩
    by_cases h2 : u = p
    · subst h2; have := (hp v).1 huv; subst this; exact Or.inl ⟨hv, hu⟩
    by_cases h3 : v = l
    · subst h3; have := (hl u).1 huv.symm; exact absurd this h2
    by_cases h4 : v = p
    · subst h4; have := (hp u).1 huv.symm; exact absurd this h1
    exact Or.inr ⟨u, v, huv, h1, h2, h3, h4, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, huv, _, _, _, _, hu, hv⟩)
    · exact ⟨l, p, (hl p).2 rfl, h1, h2⟩
    · exact ⟨u, v, huv, hu, hv⟩

lemma L538_dec' {n : ℕ} (K K' : SimpleGraph (Fin n)) [DecidableRel K'.Adj] (l p : Fin n)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (x : Fin n → Bool) :
    graphFun K' {p} x = true ↔ x p = true ∨
      ∃ u v, K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p ∧ x u = true ∧ x v = true := by
  simp only [graphFun, Finset.mem_singleton, exists_eq_left, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨u, v, huv, hu, hv⟩)
    · exact Or.inl h
    · obtain ⟨a, b, c, d, e⟩ := (hK' u v).1 huv
      exact Or.inr ⟨u, v, a, b, c, d, e, hu, hv⟩
  · rintro (h | ⟨u, v, a, b, c, d, e, hu, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, v, (hK' u v).2 ⟨a, b, c, d, e⟩, hu, hv⟩

lemma L538_rest_congr {n : ℕ} (K : SimpleGraph (Fin n)) (l p : Fin n) (x y : Fin n → Bool)
    (h : ∀ u, u ≠ l → u ≠ p → x u = y u) :
    (∃ u v, K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p ∧ x u = true ∧ x v = true) ↔
    (∃ u v, K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p ∧ y u = true ∧ y v = true) := by
  constructor
  · rintro ⟨u, v, a, b, c, d, e, hu, hv⟩
    exact ⟨u, v, a, b, c, d, e, by rw [← h u b c]; exact hu, by rw [← h v d e]; exact hv⟩
  · rintro ⟨u, v, a, b, c, d, e, hu, hv⟩
    exact ⟨u, v, a, b, c, d, e, by rw [h u b c]; exact hu, by rw [h v d e]; exact hv⟩

lemma L538_fun_rec {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (v w : Fin n) (hvw : (v = l ∧ w = p) ∨ (v = p ∧ w = l)) (x : Fin n → Bool) :
    graphFun K ∅ (Function.update (Function.update x w (x w && x v)) v true) = graphFun K ∅ x := by
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  rw [Bool.eq_iff_iff, L538_dec K l p hl hp, L538_dec K l p hl hp]
  have hc := L538_rest_congr K l p (Function.update (Function.update x w (x w && x v)) v true) x
    (by
      intro u h1 h2
      have hv : u ≠ v := by rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hw : u ≠ w := by rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      rw [Function.update_of_ne hv, Function.update_of_ne hw])
  rw [hc]
  rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Function.update_self, Function.update_of_ne hlp.symm, Bool.and_comm]
  · simp [Function.update_self, Function.update_of_ne hlp]

lemma L538_fun_l {n : ℕ} (K K' : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K'.Adj]
    (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (x : Fin n → Bool) :
    graphFun K ∅ (Function.update x l true) = graphFun K' {p} x := by
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  rw [Bool.eq_iff_iff, L538_dec K l p hl hp, L538_dec' K K' l p hK']
  have hc := L538_rest_congr K l p (Function.update x l true) x
    (by intro u h1 _; rw [Function.update_of_ne h1])
  rw [hc]
  simp [Function.update_self, Function.update_of_ne hlp.symm]

lemma L538_fun_ins {n : ℕ} (K K' : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K'.Adj]
    (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (x : Fin n → Bool) :
    graphFun K' {p} (Function.update x p (x l && x p)) = graphFun K ∅ x := by
  rw [Bool.eq_iff_iff, L538_dec K l p hl hp, L538_dec' K K' l p hK']
  have hc := L538_rest_congr K l p (Function.update x p (x l && x p)) x
    (by intro u _ h2; rw [Function.update_of_ne h2])
  rw [hc]
  simp [Function.update_self]

lemma L538_fun_dep_aux {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (v o : Fin n) (hvo : (v = l ∧ o = p) ∨ (v = p ∧ o = l)) :
    (∃ x, graphFun K ∅ (Function.update x v false) ≠ graphFun K ∅ (Function.update x v true)) ∧
    (∃ x x', graphFun K ∅ (Function.update x v true) ≠ graphFun K ∅ (Function.update x' v true)) := by
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  have key : ∀ x : Fin n → Bool, (∀ u, u ≠ l → u ≠ p → x u = false) →
      (graphFun K ∅ x = true ↔ x l = true ∧ x p = true) := by
    intro x hx
    rw [L538_dec K l p hl hp]
    constructor
    · rintro (h | ⟨u, _, _, h1, h2, _, _, hu, _⟩)
      · exact h
      · rw [hx u h1 h2] at hu; exact absurd hu (by simp)
    · exact Or.inl
  let e : Fin n → Bool := fun u => decide (u = o)
  have he : ∀ u, u ≠ l → u ≠ p → e u = false := by
    intro u h1 h2
    simp only [e, decide_eq_false_iff_not]
    rcases hvo with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> assumption
  have hz : ∀ (b : Bool) (y : Fin n → Bool), (∀ u, u ≠ l → u ≠ p → y u = false) →
      ∀ u, u ≠ l → u ≠ p → Function.update y v b u = false := by
    intro b y hy u h1 h2
    have : u ≠ v := by rcases hvo with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> assumption
    rw [Function.update_of_ne this]; exact hy u h1 h2
  have v1 : graphFun K ∅ (Function.update e v true) = true := by
    rw [key _ (hz true e he)]
    rcases hvo with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
    · simp [e, Function.update_self, Function.update_of_ne hlp.symm]
    · simp [e, Function.update_self, Function.update_of_ne hlp]
  have v0 : graphFun K ∅ (Function.update e v false) = false := by
    rw [Bool.eq_false_iff, ne_eq, key _ (hz false e he)]
    rcases hvo with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
    · simp [Function.update_self]
    · simp [Function.update_self]
  have hzero : ∀ u, u ≠ l → u ≠ p → (fun _ : Fin n => false) u = false := fun _ _ _ => rfl
  have w0 : graphFun K ∅ (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, key _ (hz true _ hzero)]
    rcases hvo with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
    · simp [Function.update_of_ne hlp.symm]
    · simp [Function.update_of_ne hlp]
  refine ⟨⟨e, by rw [v0, v1]; simp⟩, ⟨e, fun _ => false, by rw [v1, w0]; simp⟩⟩

lemma L538_fun_dep {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (v : Fin n) (hv : v = l ∨ v = p) :
    (∃ x, graphFun K ∅ (Function.update x v false) ≠ graphFun K ∅ (Function.update x v true)) ∧
    (∃ x x', graphFun K ∅ (Function.update x v true) ≠ graphFun K ∅ (Function.update x' v true)) := by
  rcases hv with h | h
  · exact L538_fun_dep_aux K l p hl hp v p (Or.inl ⟨h, rfl⟩)
  · exact L538_fun_dep_aux K l p hl hp v l (Or.inr ⟨h, rfl⟩)

lemma L538_out_ne {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (C : Circuit) (hC : circuitFun n C = graphFun K ∅) (v : Fin n) (hv : v = l ∨ v = p) :
    C.output ≠ v.val := by
  intro h
  obtain ⟨_, ⟨x, x', hx⟩⟩ := L538_fun_dep K l p hl hp v hv
  have e1 := congrFun hC (Function.update x v true)
  have e2 := congrFun hC (Function.update x' v true)
  simp only [circuitFun, Circuit.eval, h, L538_wire_input, Function.update_self] at e1 e2
  rw [← e1, ← e2] at hx
  exact hx rfl







lemma L538_gate_map_id (g : Gate) (f : ℕ → ℕ) (h : ∀ i ∈ g.inputs, f i = i) :
    g = ⟨g.op, g.inputs.map f⟩ := by
  obtain ⟨op, ins⟩ := g
  simp only [Gate.mk.injEq, true_and]
  conv_lhs => rw [← List.map_id ins]
  exact (List.map_congr_left h).symm

lemma L538_sg_ren (n p jg i : ℕ) (hp : p < n) (hi : i ≠ p) :
    L538_sg n p jg (L538A.ren (n + jg) p i) = i := by
  unfold L538A.ren L538_sg
  split_ifs <;> omega

lemma L538_del_ins {n : ℕ} (C : Circuit) (jg : ℕ) (hj : jg < C.gates.length) (p : Fin n)
    (hpr : ∀ j < C.gates.length, j ≠ jg → p.val ∉ (gateAt C j).inputs)
    (hout : C.output ≠ p.val)
    (hrb : ∀ j < jg, ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    L538_Ins n p jg C ⟨L538A.del C.gates jg (n + jg) p.val, L538A.ren (n + jg) p.val C.output⟩ := by
  have hpn := p.isLt
  have hdl : (L538A.del C.gates jg (n + jg) p.val).length = C.gates.length - 1 :=
    L538A.del_length _ _ _ _ hj
  refine ⟨by simp only; omega, by simp only; omega, ?_, ?_, ?_⟩
  · intro j hjl
    simp only at hjl
    by_cases hjj : j < jg
    · have hs : L538_sh jg j = j := by simp [L538_sh, hjj]
      rw [hs, L538_del_gate_lt C jg p.val n hj j hjj]
      apply L538_gate_map_id
      intro i hi
      have h1 := hrb j hjj i hi
      have h2 : i ≠ p.val := fun h => hpr j (by omega) (by omega) (h ▸ hi)
      simp only [L538_sg, h2, if_false]
      rw [if_neg (by omega)]
    · have hs : L538_sh jg j = j + 1 := by simp [L538_sh, hjj]
      rw [hs, L538_del_gate_ge C jg p.val n hj j (by omega) (by omega)]
      simp only [L538A.renG, List.map_map]
      apply L538_gate_map_id
      intro i hi
      exact L538_sg_ren n p.val jg i hpn (fun h => hpr (j + 1) (by omega) (by omega) (h ▸ hi))
  · exact (L538_sg_ren n p.val jg C.output hpn hout).symm
  · intro j hjj
    rw [L538_del_gate_lt C jg p.val n hj j hjj]
    exact hpr j (by omega) (by omega)

lemma L538_prepend {n : ℕ} (D : Circuit) (hD : FanInTwo D) (v w : Fin n) :
    ∃ D' : Circuit, FanInTwo D' ∧ D'.size = D.size + 1 ∧
      ∀ x, circuitFun n D' x = circuitFun n D (Function.update x w (x w && x v)) := by
  let D' : Circuit := ⟨⟨GateOp.and, [v.val, w.val]⟩ ::
    D.gates.map (fun g => ⟨g.op, g.inputs.map (L538_sg n w.val 0)⟩), L538_sg n w.val 0 D.output⟩
  have hI : L538_Ins n w.val 0 D' D := by
    refine ⟨by simp [D'], Nat.zero_le _, ?_, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    intro j hj
    have hs : L538_sh 0 j = j + 1 := by simp [L538_sh]
    rw [hs]
    unfold gateAt
    simp only [D', List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
    simp
  have hg0 : gateAt D' 0 = ⟨GateOp.and, [v.val, w.val]⟩ := by
    unfold gateAt; simp [D']
  obtain ⟨hfan, hsz⟩ := L538_ins_fan D' D w.val 0 hI (by rw [hg0]; simp) hD
  refine ⟨D', hfan, hsz, fun x => ?_⟩
  rw [L538_ins_eval D' D v w 0 hI (Or.inl hg0) x, Bool.and_comm]

lemma L538_elim {n : ℕ} (F : (Fin n → Bool) → Bool) (D : Circuit) (hD : FanInTwo D)
    (hDF : circuitFun n D = F) (v : Fin n)
    (hdep : ∃ x, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x', F (Function.update x v true) ≠ F (Function.update x' v true)) :
    ∃ D' : Circuit, FanInTwo D' ∧ D'.size + 1 ≤ D.size ∧
      circuitFun n D' = fun x => F (Function.update x v true) := by
  have hC : HasCircuitSize n F D.size :=
    ⟨D, hD, le_refl _, fun x => by rw [← hDF]; rfl⟩
  obtain ⟨h1, D', hD', hsz, hev⟩ := L538B.elim_one_var v true hC hdep hnc
  exact ⟨D', hD', by omega, funext fun x => hev x⟩

lemma L538_sg_inj (n p jg : ℕ) (hpn : p < n) : Function.Injective (L538_sg n p jg) := by
  intro a b h
  unfold L538_sg at h
  split_ifs at h <;> omega

lemma L538_sh_inj (jg : ℕ) : Function.Injective (L538_sh jg) := by
  intro a b h
  unfold L538_sh at h
  split_ifs at h <;> omega

lemma L538_sh_ne (jg j : ℕ) : L538_sh jg j ≠ jg := by
  unfold L538_sh; split_ifs <;> omega

lemma L538_sg_gate (n p jg j : ℕ) (hpn : p < n) : L538_sg n p jg (n + j) = n + L538_sh jg j := by
  unfold L538_sg L538_sh; split_ifs <;> omega

lemma L538_sg_isG (n p jg : ℕ) (hpn : p < n) (G : Finset ℕ) (i : ℕ) :
    (n ≤ L538_sg n p jg i ∧ L538_sg n p jg i - n ∈ G.image (L538_sh jg)) ↔ (n ≤ i ∧ i - n ∈ G) := by
  by_cases hip : i = p
  · subst hip
    simp only [L538_sg, if_true, Finset.mem_image]
    constructor
    · rintro ⟨_, j, _, hj⟩
      exact absurd (by omega : L538_sh jg j = jg) (L538_sh_ne jg j)
    · rintro ⟨h, _⟩; omega
  · have hn : n ≤ L538_sg n p jg i ↔ n ≤ i := by
      unfold L538_sg; split_ifs <;> omega
    rw [hn]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have e : L538_sg n p jg i = n + L538_sh jg (i - n) := by
        rw [← L538_sg_gate n p jg (i - n) hpn, Nat.add_sub_cancel' h1]
      rw [e, Nat.add_sub_cancel_left] at h2
      rw [Finset.mem_image] at h2
      obtain ⟨j, hj, hjj⟩ := h2
      rw [← L538_sh_inj jg hjj]; exact hj
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have e : L538_sg n p jg i = n + L538_sh jg (i - n) := by
        rw [← L538_sg_gate n p jg (i - n) hpn, Nat.add_sub_cancel' h1]
      rw [e, Nat.add_sub_cancel_left]
      exact Finset.mem_image_of_mem _ h2

lemma L538_reads_tr {n : ℕ} (C C' : Circuit) (p jg : ℕ) (hpn : p < n) (hI : L538_Ins n p jg C C')
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < C'.gates.length) (w : ℕ) :
    readsIn C (G.image (L538_sh jg)) (L538_sg n p jg w) = readsIn C' G w := by
  unfold readsIn
  rw [Finset.sum_image (fun a _ b _ h => L538_sh_inj jg h)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hI.2.2.1 j (hG j hj)]
  simp only
  exact List.count_map_of_injective _ _ (L538_sg_inj n p jg hpn) _

lemma L538_tree_tr {n : ℕ} (C C' : Circuit) (p jg : ℕ) (hpn : p < n) (hI : L538_Ins n p jg C C')
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < C'.gates.length) (L : Finset ℕ) (ρ : ℕ) :
    IsOrTree n C (G.image (L538_sh jg)) (L.image (L538_sg n p jg)) (L538_sg n p jg ρ) ↔
      IsOrTree n C' G L ρ := by
  have hinj := L538_sg_inj n p jg hpn
  have hgate := hI.2.2.1
  unfold IsOrTree
  apply and_congr
  · constructor
    · intro h j hj
      have := h (L538_sh jg j) (Finset.mem_image_of_mem _ hj)
      rw [hgate j (hG j hj)] at this
      simp only [List.length_map, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at this
      refine ⟨this.1, this.2.1, fun i hi => ?_⟩
      rcases this.2.2 i hi with h1 | h1
      · left; exact (hinj.mem_finset_image).1 h1
      · right; exact (L538_sg_isG n p jg hpn G i).1 h1
    · intro h j hj
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj
      rw [hgate j' (hG j' hj')]
      have := h j' hj'
      simp only [List.length_map, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      refine ⟨this.1, this.2.1, fun i hi => ?_⟩
      rcases this.2.2 i hi with h1 | h1
      · left; exact Finset.mem_image_of_mem _ h1
      · right; exact (L538_sg_isG n p jg hpn G i).2 h1
  apply and_congr
  · constructor
    · intro h w hw
      have := h (L538_sg n p jg w) (Finset.mem_image_of_mem _ hw)
      rw [L538_sg_isG n p jg hpn G w, L538_reads_tr C C' p jg hpn hI G hG w] at this
      refine ⟨this.1, ?_⟩
      rw [this.2]
      simp only [hinj.eq_iff]
    · intro h w hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
      rw [L538_sg_isG n p jg hpn G w', L538_reads_tr C C' p jg hpn hI G hG w']
      refine ⟨(h w' hw').1, ?_⟩
      rw [(h w' hw').2]
      simp only [hinj.eq_iff]
  apply and_congr
  · constructor
    · intro h j hj
      have := h (L538_sh jg j) (Finset.mem_image_of_mem _ hj)
      rw [← L538_sg_gate n p jg j hpn, L538_reads_tr C C' p jg hpn hI G hG] at this
      rw [this]
      simp only [hinj.eq_iff]
    · intro h j hj
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj
      rw [← L538_sg_gate n p jg j' hpn, L538_reads_tr C C' p jg hpn hI G hG, h j' hj']
      simp only [hinj.eq_iff]
  · have e1 : G.image (L538_sh jg) = ∅ ↔ G = ∅ := Finset.image_eq_empty
    have e2 : L.image (L538_sg n p jg) = {L538_sg n p jg ρ} ↔ L = {ρ} := by
      rw [← Finset.image_singleton (L538_sg n p jg) ρ]
      exact Finset.image_injective hinj |>.eq_iff
    have e3 : (∃ j ∈ G.image (L538_sh jg), L538_sg n p jg ρ = n + j) ↔ ∃ j ∈ G, ρ = n + j := by
      constructor
      · rintro ⟨j, hj, he⟩
        obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj
        rw [← L538_sg_gate n p jg j' hpn] at he
        exact ⟨j', hj', hinj he⟩
      · rintro ⟨j, hj, he⟩
        exact ⟨L538_sh jg j, Finset.mem_image_of_mem _ hj, by rw [he, L538_sg_gate n p jg j hpn]⟩
    by_cases hGe : G = ∅
    · have : G.image (L538_sh jg) = ∅ := e1.2 hGe
      rw [if_pos this, if_pos hGe, e2]
    · have : G.image (L538_sh jg) ≠ ∅ := fun h => hGe (e1.1 h)
      rw [if_neg this, if_neg hGe, e3]

lemma L538_fs_len (f : List Bool → Gate → Bool) (G : List Gate) (w : List Bool) :
    (G.foldl (fun w g => w ++ [f w g]) w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp; omega

lemma L538_fs_lt (f : List Bool → Gate → Bool) (G : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (G.foldl (fun w g => w ++ [f w g]) w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact L538A.getD_append_lt _ _ _ hi

lemma L538_fs_gate (f : List Bool → Gate → Bool) (G : List Gate) (w : List Bool) (t : ℕ)
    (ht : t < G.length) :
    (G.foldl (fun w g => w ++ [f w g]) w).getD (w.length + t) false =
      f ((G.take t).foldl (fun w g => w ++ [f w g]) w) G[t] := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl (fun w g => w ++ [f w g]) w).length = w.length + t := by
    rw [L538_fs_len, List.length_take, Nat.min_eq_left ht.le]
  rw [L538_fs_lt _ _ _ _ (by simp only [List.length_append, List.length_singleton, hlen]; omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hlen]

lemma L538_fs_take (f : List Bool → Gate → Bool) (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl (fun w g => w ++ [f w g]) w).length) :
    (G.foldl (fun w g => w ++ [f w g]) w).getD i false =
      ((G.take t).foldl (fun w g => w ++ [f w g]) w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact L538_fs_lt _ _ _ _ hi

lemma L538_flag_rec (n : ℕ) (C : Circuit) (d : NCCData n) (w : ℕ) :
    IsCentred n C d w ↔
      (if h : w < n then (⟨w, h⟩ : Fin n) ∈ d.cover
      else if w - n < C.gates.length then
        (d.role (w - n)).1 = Kind.z ∧ ∃ i ∈ (gateAt C (w - n)).inputs, i < w ∧ IsCentred n C d i
      else False) := by
  unfold IsCentred centreFlags
  set f : List Bool → Gate → Bool := fun w g => decide ((d.role (w.length - n)).1 = Kind.z) &&
      g.inputs.any (fun i => w.getD i false) with hf
  set init : List Bool := List.ofFn fun i : Fin n => decide (i ∈ d.cover) with hinit
  have hil : init.length = n := by simp [hinit]
  split_ifs with h1 h2
  · rw [L538_fs_lt f _ _ _ (by rw [hil]; exact h1), hinit,
      List.getD_eq_getElem _ _ (by simp; exact h1), List.getElem_ofFn]
    simp
  · have hgate := L538_fs_gate f C.gates init (w - n) h2
    rw [hil, show n + (w - n) = w by omega] at hgate
    rw [hgate]
    have hlen : ((C.gates.take (w - n)).foldl (fun w g => w ++ [f w g]) init).length = w := by
      rw [L538_fs_len, List.length_take, Nat.min_eq_left h2.le, hil]; omega
    have hg : C.gates[w - n] = gateAt C (w - n) := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ h2]
    have e2 : ∀ i, ((C.gates.take (w - n)).foldl (fun w g => w ++ [f w g]) init).getD i false =
        if i < w then (C.gates.foldl (fun w g => w ++ [f w g]) init).getD i false else false := by
      intro i
      split_ifs with hiw
      · rw [← L538_fs_take f C.gates init (w - n) i (by rw [hlen]; omega)]
      · rw [L538A.getD_of_length_le _ _ (by rw [hlen]; omega)]
    rw [hg]
    simp only [hf]
    rw [hlen]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    apply and_congr Iff.rfl
    apply exists_congr
    intro i
    apply and_congr_right
    intro _
    have e3 := e2 i
    simp only [hf] at e3
    rw [e3]
    split_ifs with hiw <;> simp [hiw]
  · simp only [iff_false]
    rw [L538A.getD_of_length_le _ _ (by rw [L538_fs_len, hil]; omega)]
    simp

lemma L538_sg_lt {n : ℕ} (C C' : Circuit) (p jg : ℕ) (hpn : p < n) (hI : L538_Ins n p jg C C')
    (j : ℕ) (i : ℕ) (hi : i ∈ (gateAt C' j).inputs) (hij : i < n + j) :
    L538_sg n p jg i < n + L538_sh jg j := by
  have hpre := hI.2.2.2.2
  unfold L538_sg L538_sh
  split_ifs with h1 h2 h3 h4 h5
  · subst h1; exact absurd hi (hpre j h2)
  · omega
  · omega
  · omega
  · omega
  · omega

lemma L538_flag_tr {n : ℕ} (C C' : Circuit) (p : Fin n) (lv jg : ℕ) (hI : L538_Ins n p.val jg C C')
    (d d' : NCCData n)
    (hcov : ∀ i : Fin n, i.val ≠ lv → i ≠ p → (i ∈ d.cover ↔ i ∈ d'.cover))
    (hpc : p ∉ d'.cover)
    (hrole : ∀ j < C'.gates.length, d.role (L538_sh jg j) = d'.role j)
    (hrjg : (d.role jg).1 ≠ Kind.z)
    (hnl : ∀ j < C'.gates.length, lv ∉ (gateAt C' j).inputs)
    (hrb : ReadsBack n C') :
    ∀ w, w ≠ lv → (IsCentred n C d (L538_sg n p.val jg w) ↔ IsCentred n C' d' w) := by
  have hpn := p.isLt
  obtain ⟨hlen, hjg, hgate, hout, hpre⟩ := hI
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rw [L538_flag_rec n C d, L538_flag_rec n C' d']
    by_cases hwn : w < n
    · by_cases hwp : w = p.val
      · subst hwp
        have e : L538_sg n p.val jg p.val = n + jg := by simp [L538_sg]
        rw [e, dif_neg (by omega), if_pos (by omega), dif_pos hwn]
        simp only [Nat.add_sub_cancel_left]
        constructor
        · rintro ⟨h, _⟩; exact absurd h hrjg
        · intro h; exact absurd h hpc
      · have e : L538_sg n p.val jg w = w := by
          simp only [L538_sg, hwp, if_false]; rw [if_neg (by omega)]
        rw [e, dif_pos hwn, dif_pos hwn]
        exact hcov ⟨w, hwn⟩ hw (fun h => hwp (by rw [← h]))
    · by_cases hwl : w - n < C'.gates.length
      · set j := w - n with hj
        have hwj : w = n + j := by omega
        have e : L538_sg n p.val jg w = n + L538_sh jg j := by
          rw [hwj]; exact L538_sg_gate n p.val jg j hpn
        have hshl : L538_sh jg j < C.gates.length := by
          simp only [L538_sh]; split_ifs <;> omega
        rw [e, dif_neg (by omega), if_pos (by omega), dif_neg hwn, if_pos hwl]
        simp only [Nat.add_sub_cancel_left]
        rw [hrole j hwl, hgate j hwl]
        simp only [List.mem_map]
        apply and_congr Iff.rfl
        constructor
        · rintro ⟨_, ⟨i', hi', rfl⟩, _, hc⟩
          have hlt : i' < w := by have := hrb j hwl i' hi'; omega
          exact ⟨i', hi', hlt, (ih i' hlt (fun h => hnl j hwl (h ▸ hi'))).1 hc⟩
        · rintro ⟨i', hi', hlt, hc⟩
          exact ⟨L538_sg n p.val jg i', ⟨i', hi', rfl⟩,
            L538_sg_lt C C' p.val jg hpn ⟨hlen, hjg, hgate, hout, hpre⟩ j i' hi' (by omega),
            (ih i' hlt (fun h => hnl j hwl (h ▸ hi'))).2 hc⟩
      · have e : L538_sg n p.val jg w = w + 1 := by
          simp only [L538_sg]; rw [if_neg (by omega), if_pos (by omega)]
        rw [e, dif_neg (by omega), if_neg (by omega), dif_neg hwn, if_neg hwl]

lemma L538_iso_notin {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (hT : IsMinCover G T)
    (a : Fin n) (ha : ∀ v, ¬ G.Adj a v) : a ∉ T := by
  intro haT
  have hc : G.IsVertexCover ((T.erase a : Finset (Fin n)) : Set (Fin n)) := by
    intro v w hvw
    rcases hT.1 hvw with h | h
    · left
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨h, fun e => ha w (e ▸ hvw)⟩
    · right
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨h, fun e => ha v (e ▸ hvw.symm)⟩
  have h1 := hT.2 _ hc
  have h2 := Finset.card_erase_lt_of_mem haT
  omega

lemma L538_cover_up {n : ℕ} (K K' : SimpleGraph (Fin n)) (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (S : Finset (Fin n)) (hS : K'.IsVertexCover (S : Set (Fin n))) :
    K.IsVertexCover ((insert l S : Finset (Fin n)) : Set (Fin n)) := by
  intro u v huv
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
  by_cases h1 : u = l
  · left; left; exact h1
  by_cases h2 : u = p
  · subst h2; have := (hp v).1 huv; right; left; exact this
  by_cases h3 : v = l
  · right; left; exact h3
  by_cases h4 : v = p
  · subst h4; have := (hp u).1 huv.symm; exact absurd this h1
  rcases hS ((hK' u v).2 ⟨huv, h1, h2, h3, h4⟩) with h | h
  · left; right; exact h
  · right; right; exact h

lemma L538_mincover_up {n : ℕ} (K K' : SimpleGraph (Fin n)) (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (T : Finset (Fin n)) (hT : IsMinCover K' T) (hlT : l ∉ T) :
    IsMinCover K (insert l T) := by
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  refine ⟨L538_cover_up K K' l p hl hp hK' T hT.1, fun T' hT' => ?_⟩
  set S := (T'.erase l).erase p with hSdef
  have hS : K'.IsVertexCover (S : Set (Fin n)) := by
    intro u v huv
    obtain ⟨h0, h1, h2, h3, h4⟩ := (hK' u v).1 huv
    simp only [hSdef, Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
    rcases hT' h0 with h | h
    · left; exact ⟨⟨h, h1⟩, h2⟩
    · right; exact ⟨⟨h, h3⟩, h4⟩
  have h1 := hT.2 S hS
  rw [Finset.card_insert_of_notMem hlT]
  have hlpT : l ∈ T' ∨ p ∈ T' := hT' ((hl p).2 rfl)
  have h2 : S.card + 1 ≤ T'.card := by
    rcases hlpT with h | h
    · have e1 := Finset.card_erase_of_mem h
      have e2 := Finset.card_erase_le (s := T'.erase l) (a := p)
      have e3 : 0 < T'.card := Finset.card_pos.2 ⟨l, h⟩
      rw [hSdef]; omega
    · have hp' : p ∈ T'.erase l := Finset.mem_erase.2 ⟨hlp.symm, h⟩
      have e1 := Finset.card_erase_of_mem hp'
      have e2 := Finset.card_erase_le (s := T') (a := l)
      have e3 : 0 < (T'.erase l).card := Finset.card_pos.2 ⟨p, hp'⟩
      rw [hSdef]; omega
  omega

lemma L538_unsh (jg j N : ℕ) (hj : j < N + 1) (hne : j ≠ jg) (hjg : jg ≤ N) :
    ∃ j' < N, L538_sh jg j' = j := by
  by_cases h : j < jg
  · exact ⟨j, by omega, by simp [L538_sh, h]⟩
  · exact ⟨j - 1, by omega, by simp only [L538_sh]; split_ifs <;> omega⟩

lemma L538_gatesOf_tr {n : ℕ} (C C' : Circuit) (p jg : ℕ) (hI : L538_Ins n p jg C C')
    (d d' : NCCData n)
    (hrole : ∀ j < C'.gates.length, d.role (L538_sh jg j) = d'.role j)
    (k : Kind) (tv : ℕ) (hjg : d.role jg ≠ (k, tv)) :
    gatesOf d C k tv = (gatesOf d' C' k tv).image (L538_sh jg) := by
  obtain ⟨hlen, hjgl, _, _, _⟩ := hI
  ext j
  simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hj, hr⟩
    have hne : j ≠ jg := fun h => hjg (h ▸ hr)
    obtain ⟨j', hj', rfl⟩ := L538_unsh jg j C'.gates.length (by omega) hne hjgl
    exact ⟨j', ⟨hj', by rw [← hrole j' hj']; exact hr⟩, rfl⟩
  · rintro ⟨j', ⟨hj', hr⟩, rfl⟩
    refine ⟨?_, by rw [hrole j' hj']; exact hr⟩
    simp only [L538_sh]; split_ifs <;> omega

lemma L538_topGates_tr {n : ℕ} (C C' : Circuit) (p jg : ℕ) (hI : L538_Ins n p jg C C')
    (d d' : NCCData n)
    (hrole : ∀ j < C'.gates.length, d.role (L538_sh jg j) = d'.role j)
    (hjg : (d.role jg).1 ≠ Kind.top) :
    topGates d C = (topGates d' C').image (L538_sh jg) := by
  obtain ⟨hlen, hjgl, _, _, _⟩ := hI
  ext j
  simp only [topGates, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hj, hr⟩
    have hne : j ≠ jg := fun h => hjg (h ▸ hr)
    obtain ⟨j', hj', rfl⟩ := L538_unsh jg j C'.gates.length (by omega) hne hjgl
    exact ⟨j', ⟨hj', by rw [← hrole j' hj']; exact hr⟩, rfl⟩
  · rintro ⟨j', ⟨hj', hr⟩, rfl⟩
    refine ⟨?_, by rw [hrole j' hj']; exact hr⟩
    simp only [L538_sh]; split_ifs <;> omega

lemma L538_up {n : ℕ} (K K' : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K'.Adj]
    (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (C C' : Circuit) (jg : ℕ) (hI : L538_Ins n p jg C C')
    (hg : gateAt C jg = ⟨GateOp.and, [l.val, p.val]⟩ ∨ gateAt C jg = ⟨GateOp.and, [p.val, l.val]⟩)
    (hnl : ∀ j < C'.gates.length, l.val ∉ (gateAt C' j).inputs)
    (d' : NCCData n) (hV : Valid n K' {p} C' d') :
    ∃ d : NCCData n, Valid n K ∅ C d := by
  classical
  obtain ⟨hrb', hmc', how', htie', hrole', hall', htop'⟩ := hV
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  have hpn := p.isLt
  have hln := l.isLt
  have hlpv : l.val ≠ p.val := fun h => hlp (Fin.ext h)
  have hlK' : ∀ v, ¬ K'.Adj l v := fun v h => ((hK' l v).1 h).2.1 rfl
  have hpK' : ∀ v, ¬ K'.Adj p v := fun v h => ((hK' p v).1 h).2.2.1 rfl
  have hl' : l ∉ d'.cover := L538_iso_notin K' _ hmc' l hlK'
  have hp' : p ∉ d'.cover := L538_iso_notin K' _ hmc' p hpK'
  have howK : ∀ u v, d'.owns u v = true → K'.Adj u v := fun u v h => (how'.1 u v h).1
  have hcovne : ∀ t ∈ d'.cover, t ≠ l ∧ t ≠ p := fun t ht =>
    ⟨fun h => hl' (h ▸ ht), fun h => hp' (h ▸ ht)⟩
  have htl : ∀ s, d'.tie s ≠ some l := by
    intro s h
    have := (how'.1 l s (htie' s l h).2).1
    exact hlK' s this
  have htie_l : d'.tie l = none := by
    cases h : d'.tie l with
    | none => rfl
    | some t => exact absurd (htie' l t h).1 hl'
  obtain ⟨hlen, hjgl, hgate, hout, hpre⟩ := hI
  have hI : L538_Ins n p jg C C' := ⟨hlen, hjgl, hgate, hout, hpre⟩
  let unsh : ℕ → ℕ := fun j => if j < jg then j else j - 1
  have hunsh : ∀ j, unsh (L538_sh jg j) = j := by
    intro j; simp only [unsh, L538_sh]; split_ifs <;> omega
  let sg := L538_sg n p.val jg
  let d : NCCData n :=
    { cover := insert l d'.cover
      owns := fun u v => d'.owns u v || (decide (u = l) && decide (v = p))
      tie := d'.tie
      role := fun j => if j = jg then (Kind.b, l.val) else d'.role (unsh j)
      bw := fun t => if t = l then n + jg else sg (d'.bw t)
      zroot := fun t => if t = l then l.val else sg (d'.zroot t)
      oroot := fun t => if t = l then p.val else sg (d'.oroot t)
      lam := fun t r => if t = l then p.val else sg (d'.lam t r) }
  have hrole : ∀ j < C'.gates.length, d.role (L538_sh jg j) = d'.role j := by
    intro j _
    show (if L538_sh jg j = jg then (Kind.b, l.val) else d'.role (unsh (L538_sh jg j))) = _
    rw [if_neg (L538_sh_ne jg j), hunsh]
  have hrjg : d.role jg = (Kind.b, l.val) := by
    show (if jg = jg then (Kind.b, l.val) else _) = _
    rw [if_pos rfl]
  have hsgv : ∀ v : Fin n, v ≠ p → sg v.val = v.val := by
    intro v hv
    show L538_sg n p.val jg v.val = v.val
    have := v.isLt
    simp only [L538_sg]
    rw [if_neg (fun h => hv (Fin.ext h)), if_neg (by omega)]
  have hgjl : jg < C.gates.length := by omega
  have hflag : ∀ w, w ≠ l.val → (IsCentred n C d (sg w) ↔ IsCentred n C' d' w) :=
    L538_flag_tr C C' p l.val jg hI d d'
      (by
        intro i hi _
        show i ∈ insert l d'.cover ↔ _
        rw [Finset.mem_insert]
        constructor
        · rintro (h | h)
          · exact absurd (congrArg Fin.val h) hi
          · exact h
        · exact Or.inr)
      hp' hrole (by rw [hrjg]; simp) hnl hrb'
  have hGl : ∀ k t, ∀ j ∈ gatesOf d' C' k t, j < C'.gates.length := by
    intro k t j hj
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hj
    exact hj.1
  refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    by_cases hjj : j = jg
    · subst hjj
      rcases hg with h | h <;> rw [h] at hi <;> simp at hi <;> rcases hi with rfl | rfl <;> omega
    · obtain ⟨j', hj', rfl⟩ := L538_unsh jg j C'.gates.length (by omega) hjj hjgl
      rw [hgate j' hj'] at hi
      simp only [List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      exact L538_sg_lt C C' p.val jg hpn hI j' i' hi' (hrb' j' hj' i' hi')
  · exact L538_mincover_up K K' l p hl hp hK' _ hmc' hl'
  · refine ⟨?_, ?_⟩
    · intro u v h
      show K.Adj u v ∧ u ∈ insert l d'.cover
      change (d'.owns u v || (decide (u = l) && decide (v = p))) = true at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨h1, h2⟩
      · exact ⟨((hK' u v).1 (howK u v h)).1, Finset.mem_insert_of_mem (how'.1 u v h).2⟩
      · rw [h1, h2]; exact ⟨(hl p).2 rfl, Finset.mem_insert_self _ _⟩
    · intro u v huv
      show (d'.owns u v || (decide (u = l) && decide (v = p))) ≠
        (d'.owns v u || (decide (v = l) && decide (u = p)))
      by_cases hk : K'.Adj u v
      · obtain ⟨_, h1, h2, h3, h4⟩ := (hK' u v).1 hk
        simp only [h1, h3, decide_false, Bool.false_and, Bool.or_false]
        exact how'.2 u v hk
      · have hcase : (u = l ∧ v = p) ∨ (u = p ∧ v = l) := by
          by_cases h1 : u = l
          · exact Or.inl ⟨h1, (hl v).1 (h1 ▸ huv)⟩
          by_cases h2 : u = p
          · exact Or.inr ⟨h2, (hp v).1 (h2 ▸ huv)⟩
          by_cases h3 : v = l
          · exact absurd ((hl u).1 (h3 ▸ huv.symm)) h2
          by_cases h4 : v = p
          · exact absurd ((hp u).1 (h4 ▸ huv.symm)) h1
          exact absurd ((hK' u v).2 ⟨huv, h1, h2, h3, h4⟩) hk
        have e1 : ∀ a b, (a = l ∨ a = p) → d'.owns a b = false := by
          intro a b ha
          cases h : d'.owns a b with
          | false => rfl
          | true =>
            rcases ha with rfl | rfl
            · exact absurd (howK _ b h) (hlK' b)
            · exact absurd (howK _ b h) (hpK' b)
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [e1 u v (Or.inl h1), e1 v u (Or.inr h2), h1, h2]
          simp [hlp, hlp.symm]
        · rw [e1 u v (Or.inr h1), e1 v u (Or.inl h2), h1, h2]
          simp [hlp, hlp.symm]
  · intro s t h
    obtain ⟨h1, h2⟩ := htie' s t h
    refine ⟨Finset.mem_insert_of_mem h1, ?_⟩
    show (d'.owns t s || _) = true
    rw [h2]; rfl
  · intro j hj
    by_cases hjj : j = jg
    · subst hjj
      right
      refine ⟨l, Finset.mem_insert_self _ _, by rw [hrjg], fun _ => ?_⟩
      show (if l = l then n + j else _) = _
      rw [if_pos rfl]
    · obtain ⟨j', hj', rfl⟩ := L538_unsh jg j C'.gates.length (by omega) hjj hjgl
      rw [hrole j' hj']
      rcases hrole' j' hj' with h | ⟨t, ht, h1, h2⟩
      · left; exact h
      · right
        refine ⟨t, Finset.mem_insert_of_mem ht, h1, fun hb => ?_⟩
        show (if t = l then n + jg else sg (d'.bw t)) = _
        rw [if_neg (hcovne t ht).1, h2 hb]
        exact L538_sg_gate n p.val jg j' hpn
  · intro t ht
    have hsglt : ∀ j < C'.gates.length, L538_sh jg j < C.gates.length := by
      intro j hj; simp only [L538_sh]; split_ifs <;> omega
    rcases Finset.mem_insert.1 ht with hteq | htc
    · rw [hteq]
      have hGz : ∀ k, (k = Kind.z ∨ k = Kind.o) → gatesOf d C k l.val = ∅ := by
        intro k hk
        rw [L538_gatesOf_tr C C' p.val jg hI d d' hrole k l.val (by
          rw [hrjg]; intro h; cases h; rcases hk with h | h <;> cases h)]
        rw [Finset.image_eq_empty]
        apply Finset.eq_empty_of_forall_notMem
        intro j hj
        simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hj
        rcases hrole' j hj.1 with h | ⟨t', ht', h1, _⟩
        · rw [hj.2] at h; rcases hk with rfl | rfl <;> cases h
        · rw [hj.2] at h1
          exact hl' ((Fin.ext h1 : l = t') ▸ ht')
      refine ⟨⟨jg, hgjl, ?_, hrjg, ?_, ?_⟩, ?_, ?_, ?_⟩
      · show (if l = l then n + jg else _) = n + jg
        rw [if_pos rfl]
      · rcases hg with h | h <;> rw [h]
      · show (gateAt C jg).inputs = [(if l = l then l.val else _), (if l = l then p.val else _)] ∨
          (gateAt C jg).inputs = [(if l = l then p.val else _), (if l = l then l.val else _)]
        rw [if_pos rfl, if_pos rfl]
        rcases hg with h | h <;> rw [h]
        · left; rfl
        · right; rfl
      · rw [hGz Kind.z (Or.inl rfl)]
        have hzl : zLeaves d l = {l.val} := by
          unfold zLeaves
          have : (d.cover.filter (fun s => d.tie s = some l)) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro s hs
            exact htl s (Finset.mem_filter.1 hs).2
          rw [this, Finset.image_empty]; rfl
        rw [hzl]
        show IsOrTree n C ∅ {l.val} (if l = l then l.val else _)
        rw [if_pos rfl]
        refine ⟨by simp, ?_, by simp, by simp⟩
        intro w hw
        rw [Finset.mem_singleton] at hw
        subst hw
        simp [readsIn]
      · rw [hGz Kind.o (Or.inr rfl)]
        have hol : oLeaves d l = {p.val} := by
          unfold oLeaves
          apply Finset.eq_singleton_iff_unique_mem.2
          constructor
          · apply Finset.mem_image.2
            refine ⟨p, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              show (d'.owns l p || (decide (l = l) && decide (p = p))) = true
              simp
            · show (if l = l then p.val else _) = p.val
              rw [if_pos rfl]
          · intro w hw
            obtain ⟨r, _, hr⟩ := Finset.mem_image.1 hw
            rw [← hr]
            show (if l = l then p.val else _) = p.val
            rw [if_pos rfl]
        rw [hol]
        show IsOrTree n C ∅ {p.val} (if l = l then p.val else _)
        rw [if_pos rfl]
        refine ⟨by simp, ?_, by simp, by simp⟩
        intro w hw
        rw [Finset.mem_singleton] at hw
        subst hw
        simp [readsIn]
      · intro r hr
        change (d'.owns l r || (decide (l = l) && decide (r = p))) = true at hr
        have hrp : r = p := by
          cases h : d'.owns l r with
          | true => exact absurd (howK l r h) (hlK' r)
          | false => rw [h] at hr; simpa using hr
        rw [hrp]
        unfold LamOK
        have hpc : p ∉ d.cover := by
          show p ∉ insert l d'.cover
          rw [Finset.mem_insert, not_or]
          exact ⟨fun h => hlp h.symm, hp'⟩
        rw [if_neg hpc]
        show (if l = l then p.val else _) = p.val
        rw [if_pos rfl]
    · obtain ⟨htne, htp⟩ := hcovne t htc
      obtain ⟨hT', hZ', hO', hL'⟩ := hall' t htc
      have hzr : d.zroot t = sg (d'.zroot t) := by
        show (if t = l then _ else _) = _; rw [if_neg htne]
      have hor : d.oroot t = sg (d'.oroot t) := by
        show (if t = l then _ else _) = _; rw [if_neg htne]
      refine ⟨?_, ?_, ?_, ?_⟩
      · obtain ⟨j0, hj0, hbw, hr, hop, hin⟩ := hT'
        refine ⟨L538_sh jg j0, hsglt j0 hj0, ?_, by rw [hrole j0 hj0]; exact hr, ?_, ?_⟩
        · show (if t = l then n + jg else sg (d'.bw t)) = _
          rw [if_neg htne, hbw]; exact L538_sg_gate n p.val jg j0 hpn
        · rw [hgate j0 hj0]; exact hop
        · rw [hgate j0 hj0, hzr, hor]
          rcases hin with h | h
          · left; simp only; rw [h]; rfl
          · right; simp only; rw [h]; rfl
      · rw [L538_gatesOf_tr C C' p.val jg hI d d' hrole Kind.z t.val (by rw [hrjg]; simp)]
        have hzl : zLeaves d t = (zLeaves d' t).image sg := by
          unfold zLeaves
          rw [Finset.image_insert, hsgv t htp]
          congr 1
          show ((insert l d'.cover).filter (fun s => d'.tie s = some t)).image d.bw = _
          rw [Finset.filter_insert, if_neg (by rw [htie_l]; simp), Finset.image_image]
          apply Finset.image_congr
          intro s hs
          have hs' := (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).1
          show (if s = l then n + jg else sg (d'.bw s)) = (sg ∘ d'.bw) s
          rw [if_neg (hcovne s hs').1]; rfl
        rw [hzl, hzr]
        exact (L538_tree_tr C C' p.val jg hpn hI _ (hGl _ _) _ _).2 hZ'
      · rw [L538_gatesOf_tr C C' p.val jg hI d d' hrole Kind.o t.val (by rw [hrjg]; simp)]
        have hol : oLeaves d t = (oLeaves d' t).image sg := by
          unfold oLeaves
          rw [Finset.image_image]
          have hf : (Finset.univ.filter (fun r => d.owns t r = true)) =
              (Finset.univ.filter (fun r => d'.owns t r = true)) := by
            apply Finset.filter_congr
            intro r _
            show (d'.owns t r || (decide (t = l) && decide (r = p))) = true ↔ _
            simp [htne]
          rw [hf]
          apply Finset.image_congr
          intro r _
          show (if t = l then p.val else sg (d'.lam t r)) = (sg ∘ d'.lam t) r
          rw [if_neg htne]; rfl
        rw [hol, hor]
        exact (L538_tree_tr C C' p.val jg hpn hI _ (hGl _ _) _ _).2 hO'
      · intro r hr
        change (d'.owns t r || (decide (t = l) && decide (r = p))) = true at hr
        have hr' : d'.owns t r = true := by simpa [htne] using hr
        have hrK := howK t r hr'
        have hrl : r ≠ l := fun h => hlK' t (h ▸ hrK.symm)
        have hrp : r ≠ p := fun h => hpK' t (h ▸ hrK.symm)
        have hmem : r ∈ d.cover ↔ r ∈ d'.cover := by
          show r ∈ insert l d'.cover ↔ _
          rw [Finset.mem_insert]
          constructor
          · rintro (h | h)
            · exact absurd h hrl
            · exact h
          · exact Or.inr
        have hlam : d.lam t r = sg (d'.lam t r) := by
          show (if t = l then _ else _) = _; rw [if_neg htne]
        have hL := hL' r hr'
        unfold LamOK at hL ⊢
        by_cases hrc : r ∈ d'.cover
        · rw [if_pos (hmem.2 hrc)]
          rw [if_pos hrc] at hL
          obtain ⟨hc, hform, htie⟩ := hL
          refine ⟨?_, ?_, ?_⟩
          · rw [hlam]
            apply (hflag _ _).2 hc
            rcases hform with h | ⟨j, _, h, _⟩
            · rw [h]; exact fun e => hrl (Fin.ext e)
            · rw [h]; omega
          · rcases hform with h | ⟨j, hj, h, hr2⟩
            · left; rw [hlam, h, hsgv r hrp]
            · right
              exact ⟨L538_sh jg j, hsglt j hj, by rw [hlam, h]; exact L538_sg_gate n p.val jg j hpn,
                by rw [hrole j hj]; exact hr2⟩
          · intro hti
            rw [hlam, htie hti]
            show _ = (if r = l then _ else sg (d'.zroot r))
            rw [if_neg hrl]
        · rw [if_neg (fun h => hrc (hmem.1 h))]
          rw [if_neg hrc] at hL
          rw [hlam, hL, hsgv r hrp]
  · rw [L538_topGates_tr C C' p.val jg hI d d' hrole (by rw [hrjg]; simp)]
    have htl2 : topLeaves d ∅ = (topLeaves d' {p}).image sg := by
      unfold topLeaves
      rw [Finset.image_union, Finset.image_empty, Finset.empty_union, Finset.image_singleton,
        Finset.image_singleton, Finset.image_image]
      show ((insert l d'.cover).filter (fun t => d'.tie t = none)).image d.bw = _
      rw [Finset.filter_insert, if_pos htie_l, Finset.image_insert]
      have e1 : d.bw l = sg p.val := by
        show (if l = l then n + jg else _) = L538_sg n p.val jg p.val
        rw [if_pos rfl]; simp [L538_sg]
      rw [e1, Finset.insert_eq]
      congr 1
      apply Finset.image_congr
      intro s hs
      have hs' := (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).1
      show (if s = l then n + jg else sg (d'.bw s)) = (sg ∘ d'.bw) s
      rw [if_neg (hcovne s hs').1]; rfl
    rw [htl2, hout]
    have hGt : ∀ j ∈ topGates d' C', j < C'.gates.length := by
      intro j hj
      simp only [topGates, Finset.mem_filter, Finset.mem_range] at hj
      exact hj.1
    exact (L538_tree_tr C C' p.val jg hpn hI _ hGt _ _).2 htop'

lemma L538_nested_ops {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
    (C : Circuit) (d : NCCData n) (hV : Valid n K A C d) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or ∨
      ((gateAt C j).op = GateOp.and ∧ ∃ t ∈ d.cover,
        (gateAt C j).inputs = [d.zroot t, d.oroot t] ∨ (gateAt C j).inputs = [d.oroot t, d.zroot t]) := by
  obtain ⟨_, _, _, _, hrole, hall, htop⟩ := hV
  intro j hj
  rcases hrole j hj with h | ⟨t, ht, h1, h2⟩
  · left
    have hjt : j ∈ topGates d C := by
      simp only [topGates, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, h⟩
    exact (htop.1 j hjt).1
  · obtain ⟨hT, hZ, hO, _⟩ := hall t ht
    rcases hk : (d.role j).1 with _ | _ | _ | _
    · left
      have hjz : j ∈ gatesOf d C Kind.z t.val := by
        simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj, Prod.ext hk h1⟩
      exact (hZ.1 j hjz).1
    · left
      have hjo : j ∈ gatesOf d C Kind.o t.val := by
        simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj, Prod.ext hk h1⟩
      exact (hO.1 j hjo).1
    · right
      have hbw := h2 hk
      obtain ⟨j0, _, hbw0, _, hop, hin⟩ := hT
      have : j0 = j := by omega
      subst this
      exact ⟨hop, t, ht, hin⟩
    · left
      have hjt : j ∈ topGates d C := by
        simp only [topGates, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hk⟩
      exact (htop.1 j hjt).1

lemma L538_preader {n : ℕ} (K' : SimpleGraph (Fin n)) [DecidableRel K'.Adj] (p : Fin n)
    (hp : ∀ v, ¬ K'.Adj p v) (C' : Circuit) (d : NCCData n) (hV : Valid n K' {p} C' d) :
    ∀ j < C'.gates.length, p.val ∈ (gateAt C' j).inputs → (gateAt C' j).op = GateOp.or := by
  intro j hj hpin
  have hpc : p ∉ d.cover := L538_iso_notin K' _ hV.2.1 p hp
  rcases L538_nested_ops K' {p} C' d hV j hj with h | ⟨_, t, ht, hin⟩
  · exact h
  · exfalso
    obtain ⟨_, hZ, hO, hL⟩ := hV.2.2.2.2.2.1 t ht
    have hz : d.zroot t ≠ p.val := by
      intro he
      by_cases hG : gatesOf d C' Kind.z t.val = ∅
      · have h4 := hZ.2.2.2
        rw [if_pos hG] at h4
        have : t.val ∈ zLeaves d t := Finset.mem_insert_self _ _
        rw [h4, Finset.mem_singleton, he] at this
        exact hpc (Fin.ext this ▸ ht)
      · have h4 := hZ.2.2.2
        rw [if_neg hG] at h4
        obtain ⟨j', _, hj'⟩ := h4
        have := p.isLt
        omega
    have ho : d.oroot t ≠ p.val := by
      intro he
      by_cases hG : gatesOf d C' Kind.o t.val = ∅
      · have h4 := hO.2.2.2
        rw [if_pos hG] at h4
        have hmem : d.oroot t ∈ oLeaves d t := by rw [h4]; exact Finset.mem_singleton_self _
        unfold oLeaves at hmem
        obtain ⟨r, hr, hre⟩ := Finset.mem_image.1 hmem
        have hr' : d.owns t r = true := (Finset.mem_filter.1 hr).2
        have hadj := (hV.2.2.1.1 t r hr').1
        have hrp : r ≠ p := fun h => hp t (h ▸ hadj.symm)
        have hlam := hL r hr'
        have he' : d.lam t r = p.val := hre.trans he
        unfold LamOK at hlam
        split_ifs at hlam with hrc
        · rcases hlam.2.1 with h | ⟨j', _, h, _⟩
          · rw [h] at he'; exact hrp (Fin.ext he')
          · rw [h] at he'; have := p.isLt; omega
        · rw [hlam] at he'; exact hrp (Fin.ext he')
      · have h4 := hO.2.2.2
        rw [if_neg hG] at h4
        obtain ⟨j', _, hj'⟩ := h4
        have := p.isLt
        omega
    rcases hin with h | h <;> rw [h] at hpin <;> simp at hpin <;>
      rcases hpin with h1 | h1 <;> first | exact hz h1.symm | exact ho h1.symm

lemma L538_norm_inputs (g : Gate) : (L538B.normGate g).inputs = L538A.deps g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [L538B.normGate, L538A.deps]
  cases ins <;> simp

lemma L538_norm_and (g : Gate) (h : (L538B.normGate g).op = GateOp.and) : L538B.normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [L538B.normGate]

lemma L538_simp_copy (op : GateOp) (m : ℕ) (ins : List ℕ) (st : ℕ → Bool ⊕ ℕ) (v : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hv : v ∈ ins) (hst : st v = Sum.inl true)
    (j : ℕ) (hj : (L538B.simplifyGate op m (ins.map st)).2 = Sum.inr j) :
    op = GateOp.and ∧ ∃ a, (ins = [v, a] ∨ ins = [a, v]) ∧ st a = Sum.inr j := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hv
  · simp at hv; subst hv
    rcases hop with rfl | rfl | rfl <;>
      simp [hst, L538B.simplifyGate, L538B.simpAnd, L538B.simpOr, L538B.simpNot] at hj
  · rcases hop with rfl | rfl | rfl
    · refine ⟨rfl, ?_⟩
      simp at hv
      rcases hv with rfl | rfl
      · cases hb : st b with
        | inl c => simp [hst, hb, L538B.simplifyGate, L538B.simpAnd] at hj
        | inr k =>
          simp [hst, hb, L538B.simplifyGate, L538B.simpAnd] at hj
          exact ⟨b, Or.inl rfl, by rw [hb, hj]⟩
      · cases ha : st a with
        | inl c => simp [hst, ha, L538B.simplifyGate, L538B.simpAnd] at hj
        | inr k =>
          simp [hst, ha, L538B.simplifyGate, L538B.simpAnd] at hj
          exact ⟨a, Or.inr rfl, by rw [ha, hj]⟩
    · exfalso
      simp at hv
      rcases hv with rfl | rfl
      · cases hb : st b <;> simp [hst, hb, L538B.simplifyGate, L538B.simpOr] at hj
      · cases ha : st a <;> simp [hst, ha, L538B.simplifyGate, L538B.simpOr] at hj
    · have := hnot rfl; simp at this
  · simp at hlen

lemma L538_len_lt_oob (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, L538B.NOkGate g) (hk : acc.1.length + gs.length ≤ k)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (L538B.elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [L538B.elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (L538B.simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply L538B.simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · refine ⟨false, List.mem_map.2 ⟨k, hkg, ?_⟩⟩
          rw [List.getD_eq_default _ _ (by simp at hk; omega)]
      have h2 : (L538B.elimStep m acc g).2.length = acc.2.length := by
        simp only [L538B.elimStep, hnone, Option.toList_none, List.append_nil]
      have := L538B.elimPass_len m gs (L538B.elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (L538B.elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [L538B.elimStep] at hk ⊢; omega) hex'
      have h2 : (L538B.elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [L538B.elimStep, List.length_append]
        have := L538B.toList_opt_len_le (L538B.simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma L538_filter_two {α : Type*} (l : List α) (p : α → Bool) (i j : ℕ) (hij : i < j)
    (hj : j < l.length) (hpi : p (l[i]'(by omega)) = true) (hpj : p l[j] = true) :
    2 ≤ (l.filter p).length := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  rw [hsplit, List.filter_append, List.length_append]
  have h1 : 1 ≤ ((l.take j).filter p).length := by
    apply List.length_pos_of_mem (a := l[i]'(by omega))
    rw [List.mem_filter]
    refine ⟨?_, hpi⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp⟩
  have h2 : 1 ≤ ((l.drop j).filter p).length := by
    apply List.length_pos_of_mem (a := l[j])
    rw [List.mem_filter]
    refine ⟨?_, hpj⟩
    rw [List.mem_iff_getElem]
    exact ⟨0, by simp; omega, by simp⟩
  omega

lemma L538_uniq {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) (hC : IsMinimalCircuit n C)
    (hCF : circuitFun n C = F) (v : Fin n)
    (hsmall : ∀ D : Circuit, FanInTwo D →
      circuitFun n D = (fun x => F (Function.update x v true)) → C.size ≤ D.size + 1)
    (hdep : ∃ x, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x', F (Function.update x v true) ≠ F (Function.update x' v true)) :
    ∃ jg < C.gates.length, ∃ y : ℕ, y < n + jg ∧ y ≠ v.val ∧
      (gateAt C jg = ⟨GateOp.and, [v.val, y]⟩ ∨ gateAt C jg = ⟨GateOp.and, [y, v.val]⟩) ∧
      ∀ j < C.gates.length, j ≠ jg → v.val ∉ L538A.deps (gateAt C j) := by
  obtain ⟨hok, hmin⟩ := hC
  have hev : ∀ x, C.eval (List.ofFn x) = F x := fun x => by rw [← hCF]; rfl
  set gs := C.gates.map L538B.normGate with hgs
  have hnok : ∀ g ∈ gs, L538B.NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact L538B.normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v true)
    have h2 := hev (Function.update x' v true)
    have hw1 : (C.wires (List.ofFn (Function.update x v true))).getD (v : ℕ) false = true := by
      show (L538B.wiresFrom C.gates (List.ofFn (Function.update x v true))).getD (v : ℕ) false = true
      rw [L538B.wiresFrom_getD_lt _ _ _ (by simp), L538B.ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v true))).getD (v : ℕ) false = true := by
      show (L538B.wiresFrom C.gates (List.ofFn (Function.update x' v true))).getD (v : ℕ) false = true
      rw [L538B.wiresFrom_getD_lt _ _ _ (by simp), L538B.ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v true) = true := by
      rw [← h1]; show (C.wires _).getD C.output false = true; rw [heq]; exact hw1
    have e2 : F (Function.update x' v true) = true := by
      rw [← h2]; show (C.wires _).getD C.output false = true; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := L538B.wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < n
        · have hne' : (⟨i, hlt⟩ : Fin n) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [L538B.ofFn_getD_lt _ _ _ hlt, L538B.ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, L538B.wiresFrom_norm, L538B.wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc0 : List (Bool ⊕ ℕ) × List Gate := (L538B.initVar n v true, []) with hacc0
  have hacc0len : acc0.1.length = n := by simp [hacc0, L538B.initVar]
  have hval : ∀ x : Fin n → Bool,
      L538B.statVal (L538B.wiresFrom (L538B.elimPass n gs acc0).2 (List.ofFn x))
        ((L538B.elimPass n gs acc0).1.getD C.output (Sum.inl false)) =
        F (Function.update x v true) := by
    intro x
    have hinv := L538B.elimInv_pass n (List.ofFn x) gs _ acc0
      (fun g hg => (hnok g hg).1) (L538B.elimInv_initVar n v true x)
    rw [(hinv.2.2 C.output).2, hgs, L538B.wiresFrom_norm]
    exact hev (Function.update x v true)
  have hcount : C.gates.length ≤ (L538B.elimPass n gs acc0).2.length + 1 := by
    cases hst : (L538B.elimPass n gs acc0).1.getD C.output (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨x, x', hne⟩ := hnc
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact hne (hx.symm.trans hx')
    | inr j =>
      have := hsmall ⟨(L538B.elimPass n gs acc0).2, j⟩
        (L538B.elimPass_ok n gs _ (by intro g hg; simp [hacc0] at hg))
        (by
          funext x
          have := hval x
          rw [hst] at this
          exact this)
      exact this
  have hstv0 : acc0.1.getD v.val (Sum.inl false) = Sum.inl true := by
    rw [hacc0]; simp only; rw [L538B.initVar, L538B.ofFn_getD_lt _ _ _ v.isLt]; simp
  have hone : ∀ i j (hij : i < j) (hj : j < gs.length), v.val ∈ (gs[i]'(by omega)).inputs →
      v.val ∈ gs[j].inputs → False := by
    intro i j hij hj hi hj'
    have h2 := L538_filter_two gs (fun g => decide (v.val ∈ g.inputs)) i j hij hj
      (by simpa using hi) (by simpa using hj')
    have := L538B.elimPass_len_two n v.val gs acc0 hnok (by rw [hacc0len]; exact v.isLt)
      ⟨true, hstv0⟩ h2
    have e : acc0.2.length = 0 := by simp [hacc0]
    omega
  obtain ⟨g0, hg0, hvg0⟩ := hex
  obtain ⟨jg, hjg, hgj⟩ := List.getElem_of_mem hg0
  have huniq : ∀ j (hj : j < gs.length), j ≠ jg → v.val ∉ gs[j].inputs := by
    intro j hj hne hvj
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hone j jg h hjg hvj (hgj ▸ hvg0)
    · exact hone jg j h hj (hgj ▸ hvg0) hvj
  have hgsj : ∀ j (hj : j < gs.length), gs[j] = L538B.normGate (gateAt C j) := by
    intro j hj
    simp only [hgs, List.getElem_map, gateAt]
    rw [List.getD_eq_getElem _ _ (by omega)]
  set acc1 := L538B.elimPass n (gs.take jg) acc0 with hacc1
  have hacc1len : acc1.1.length = n + jg := by
    rw [hacc1, L538B.elimPass_fst_len, hacc0len, List.length_take]; omega
  have hacc1le : acc1.2.length ≤ jg := by
    have := L538B.elimPass_len n (gs.take jg) acc0
    rw [← hacc1] at this
    have e : acc0.2.length = 0 := by simp [hacc0]
    rw [List.length_take] at this
    omega
  set g := gs[jg] with hg
  have hsplit : gs = gs.take jg ++ g :: gs.drop (jg + 1) := by simp [hg]
  set st : ℕ → Bool ⊕ ℕ := fun i => acc1.1.getD i (Sum.inl false) with hst
  have hstv : st v.val = Sum.inl true := by
    simp only [hst, hacc1]
    rw [L538B.elimPass_getD_lt _ _ _ _ _ (by rw [hacc0len]; exact v.isLt)]
    exact hstv0
  have hvg : v.val ∈ g.inputs := hgj ▸ hvg0
  have hgok := hnok g (List.getElem_mem hjg)
  set r := L538B.simplifyGate g.op (n + acc1.2.length) (g.inputs.map st) with hr
  have hrnone : r.1 = none := by
    apply L538B.simplifyGate_none_of_const
    · exact hgok.1.1
    · simpa using hgok.1.2
    · intro h; simpa using hgok.2 h
    · exact ⟨true, List.mem_map.2 ⟨v.val, hvg, hstv⟩⟩
  set acc2 := L538B.elimStep n acc1 g with hacc2
  have hfinal : L538B.elimPass n gs acc0 = L538B.elimPass n (gs.drop (jg + 1)) acc2 := by
    conv_lhs => rw [hsplit]
    rw [L538B.elimPass_append, L538B.elimPass_cons]
  have hacc2_2 : acc2.2.length = acc1.2.length := by
    simp only [hacc2, L538B.elimStep]
    rw [← hst, ← hr, hrnone]; simp
  have hacc2_1len : acc2.1.length = n + jg + 1 := by
    simp only [hacc2, L538B.elimStep, List.length_append, List.length_singleton]; omega
  have hacc2_1 : acc2.1.getD (n + jg) (Sum.inl false) = r.2 := by
    simp only [hacc2, L538B.elimStep]
    rw [← hst, ← hr]
    exact L538B.getD_snoc_eq _ _ _ _ (by omega)
  have hdl : (gs.drop (jg + 1)).length = gs.length - (jg + 1) := List.length_drop
  have hfl := L538B.elimPass_len n (gs.drop (jg + 1)) acc2
  rw [← hfinal] at hfl
  cases hr2 : r.2 with
  | inl c =>
    exfalso
    by_cases hrd : ∃ g' ∈ gs.drop (jg + 1), (n + jg) ∈ g'.inputs
    · have := L538B.elimPass_len_lt n (n + jg) (gs.drop (jg + 1)) acc2
        (fun g' hg' => hnok g' (List.mem_of_mem_drop hg')) (by omega)
        ⟨c, by rw [hacc2_1, hr2]⟩ hrd
      rw [← hfinal] at this
      omega
    · by_cases hre : ∃ g' ∈ gs.take jg, (n + jg) ∈ g'.inputs
      · have h1 := L538_len_lt_oob n (n + jg) (gs.take jg) acc0
          (fun g' hg' => hnok g' (List.mem_of_mem_take hg'))
          (by rw [hacc0len, List.length_take]; omega) hre
        rw [← hacc1] at h1
        have e : acc0.2.length = 0 := by simp [hacc0]
        rw [List.length_take] at h1
        omega
      · push_neg at hrd hre
        by_cases hout : C.output = n + jg
        · obtain ⟨x, x', hne⟩ := hnc
          have hfo : (L538B.elimPass n gs acc0).1.getD C.output (Sum.inl false) = Sum.inl c := by
            rw [hfinal, hout, L538B.elimPass_getD_lt _ _ _ _ _ (by omega), hacc2_1, hr2]
          have hx := hval x; have hx' := hval x'
          rw [hfo] at hx hx'
          exact hne (hx.symm.trans hx')
        · have hnr : ∀ g' ∈ C.gates.drop (jg + 1), n + jg ∉ L538A.deps g' := by
            intro g' hg' hd
            apply hrd (L538B.normGate g')
            · rw [hgs, ← List.map_drop]; exact List.mem_map_of_mem hg'
            · rw [L538_norm_inputs]; exact hd
          have hjC : jg < C.gates.length := by omega
          have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
          have hDf : circuitFun n ⟨L538A.del C.gates jg (n + jg) 0, L538A.ren (n + jg) 0 C.output⟩ =
              circuitFun n C := by
            funext x
            have := L538A.del_eval C.gates C.output (List.ofFn x) jg 0 hjC
              (Or.inl (by simp; omega)) (fun g' hg' hd => absurd (by simpa using hd) (hnr g' hg'))
              (fun h => absurd (by simpa using h) hout)
            simp only [List.length_ofFn] at this
            exact this
          have := hmin _ (L538A.fanInTwo_del _ _ _ _ _ _ hok) hDf
          simp only [Circuit.size, L538A.del_length _ _ _ _ hjC] at this
          omega
  | inr y' =>
    obtain ⟨hand, a, hin, hsta⟩ := L538_simp_copy g.op (n + acc1.2.length) g.inputs st v.val
      hgok.1.1 hgok.1.2 hgok.2 hvg hstv y' (by rw [← hr]; exact hr2)
    have ha : a < n + jg := by
      by_contra hcon
      push_neg at hcon
      have : st a = Sum.inl false := by
        simp only [hst]; rw [List.getD_eq_default _ _ (by omega)]
      rw [this] at hsta; cases hsta
    have hav : a ≠ v.val := by intro h; rw [h, hstv] at hsta; cases hsta
    have hgC : gateAt C jg = g := by
      rw [hg, hgsj jg hjg]
      exact (L538_norm_and _ (by rw [← hgsj jg hjg]; exact hand)).symm
    refine ⟨jg, by omega, a, ha, hav, ?_, ?_⟩
    · rw [hgC]
      have hgeq : g = ⟨g.op, g.inputs⟩ := rfl
      rw [hgeq, hand]
      rcases hin with h | h
      · left; rw [h]
      · right; rw [h]
    · intro j hj hne hd
      rw [← L538_norm_inputs, ← hgsj j (by omega)] at hd
      exact huniq j (by omega) hne hd

lemma L538_tree_single {n : ℕ} (C : Circuit) (hrb : ReadsBack n C) (G : Finset ℕ) (w ρ : ℕ)
    (hT : IsOrTree n C G {w} ρ) : G = ∅ ∧ ρ = w := by
  by_cases hG : G = ∅
  · have h4 := hT.2.2.2
    rw [if_pos hG] at h4
    exact ⟨hG, (Finset.singleton_inj.1 h4).symm⟩
  · exfalso
    have hne : G.Nonempty := Finset.nonempty_iff_ne_empty.2 hG
    set j := G.min' hne with hj
    have hjG : j ∈ G := Finset.min'_mem G hne
    obtain ⟨hop, hlen, hin⟩ := hT.1 j hjG
    have hjl : j < C.gates.length := by
      by_contra hc
      push_neg at hc
      unfold gateAt at hlen
      rw [List.getD_eq_default _ _ hc] at hlen
      simp at hlen
    have hall : ∀ i ∈ (gateAt C j).inputs, i = w := by
      intro i hi
      rcases hin i hi with h | ⟨h1, h2⟩
      · exact Finset.mem_singleton.1 h
      · have := Finset.min'_le G (i - n) h2
        have := hrb j hjl i hi
        omega
    have hw2 : 2 ≤ (gateAt C j).inputs.count w := by
      rw [List.count_eq_length.2 (fun b hb => (hall b hb).symm), hlen]
    have hr := (hT.2.1 w (Finset.mem_singleton_self w)).2
    have hle : (gateAt C j).inputs.count w ≤ readsIn C G w := by
      unfold readsIn
      exact Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w) (fun _ _ => Nat.zero_le _) hjG
    rw [hr] at hle
    split_ifs at hle <;> omega

lemma L538_down_struct {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (C : Circuit) (d : NCCData n) (hV : Valid n K ∅ C d) (t0 o : Fin n)
    (hto : (t0 = l ∧ o = p) ∨ (t0 = p ∧ o = l)) (ht0 : t0 ∈ d.cover) (ho : o ∉ d.cover) :
    ∃ j0 < C.gates.length, d.bw t0 = n + j0 ∧ d.role j0 = (Kind.b, t0.val) ∧
      d.zroot t0 = t0.val ∧ d.oroot t0 = o.val ∧
      gatesOf d C Kind.z t0.val = ∅ ∧ gatesOf d C Kind.o t0.val = ∅ ∧
      (gateAt C j0 = ⟨GateOp.and, [t0.val, o.val]⟩ ∨ gateAt C j0 = ⟨GateOp.and, [o.val, t0.val]⟩) ∧
      d.owns t0 o = true ∧ (∀ v, d.owns o v = false) ∧ (∀ v, d.owns t0 v = true → v = o) ∧
      (∀ s, d.tie s ≠ some t0) ∧ d.tie t0 = none := by
  obtain ⟨hrb, _, how, htie, _, hall, _⟩ := hV
  have hat : ∀ v, K.Adj t0 v ↔ v = o := by
    rcases hto with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> assumption
  have hao : ∀ v, K.Adj o v ↔ v = t0 := by
    rcases hto with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> assumption
  have hoo : ∀ v, d.owns o v = false := by
    intro v
    cases h : d.owns o v with
    | false => rfl
    | true => exact absurd (how.1 o v h).2 ho
  have hto' : ∀ v, d.owns t0 v = true → v = o := fun v h => (hat v).1 (how.1 t0 v h).1
  have hto1 : d.owns t0 o = true := by
    have := how.2 t0 o ((hat o).2 rfl)
    rw [hoo t0] at this
    simpa using this
  have hts : ∀ s, d.tie s ≠ some t0 := by
    intro s h
    obtain ⟨h1, h2⟩ := htie s t0 h
    have := hto' s h2
    rw [this] at h1
    exact ho h1
  have ht0n : d.tie t0 = none := by
    cases h : d.tie t0 with
    | none => rfl
    | some t =>
      obtain ⟨_, h2⟩ := htie t0 t h
      have hadj := (how.1 t t0 h2).1
      have : t = o := (hat t).1 hadj.symm
      rw [this, hoo] at h2
      cases h2
  obtain ⟨hT, hZ, hO, hL⟩ := hall t0 ht0
  have hzl : zLeaves d t0 = {t0.val} := by
    unfold zLeaves
    have : (d.cover.filter (fun s => d.tie s = some t0)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      exact hts s (Finset.mem_filter.1 hs).2
    rw [this, Finset.image_empty]; rfl
  have hlam : d.lam t0 o = o.val := by
    have := hL o hto1
    unfold LamOK at this
    rw [if_neg ho] at this
    exact this
  have hol : oLeaves d t0 = {o.val} := by
    unfold oLeaves
    have : (Finset.univ.filter (fun r => d.owns t0 r = true)) = {o} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact hto' r
      · intro h; rw [h]; exact hto1
    rw [this, Finset.image_singleton, hlam]
  rw [hzl] at hZ
  rw [hol] at hO
  obtain ⟨hgz, hzr⟩ := L538_tree_single C hrb _ _ _ hZ
  obtain ⟨hgo, hor⟩ := L538_tree_single C hrb _ _ _ hO
  obtain ⟨j0, hj0, hbw, hr, hop, hin⟩ := hT
  refine ⟨j0, hj0, hbw, hr, hzr, hor, hgz, hgo, ?_, hto1, hoo, hto', hts, ht0n⟩
  rw [hzr, hor] at hin
  have hgeq : gateAt C j0 = ⟨(gateAt C j0).op, (gateAt C j0).inputs⟩ := rfl
  rw [hgeq, hop]
  rcases hin with h | h
  · left; rw [h]
  · right; rw [h]

lemma L538_down_only {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (C : Circuit) (d : NCCData n) (hV : Valid n K ∅ C d) (t0 o : Fin n)
    (hto : (t0 = l ∧ o = p) ∨ (t0 = p ∧ o = l)) (ht0 : t0 ∈ d.cover) (ho : o ∉ d.cover)
    (j0 : ℕ) (hbw : d.bw t0 = n + j0) (hgz : gatesOf d C Kind.z t0.val = ∅)
    (hgo : gatesOf d C Kind.o t0.val = ∅) (v : Fin n) (hv : v = t0 ∨ v = o) :
    ∀ j < C.gates.length, j ≠ j0 → v.val ∉ (gateAt C j).inputs := by
  obtain ⟨hrb, _, how, htie, hrole, hall, htop⟩ := hV
  have hvn := v.isLt
  have hcov2 : ∀ t ∈ d.cover, t ≠ t0 → t ≠ l ∧ t ≠ p := by
    intro t ht hne
    rcases hto with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => hne (h.trans h1.symm), fun h => ho (h2 ▸ h ▸ ht)⟩
    · exact ⟨fun h => ho (h2 ▸ h ▸ ht), fun h => hne (h.trans h1.symm)⟩
  have hvlp : v = l ∨ v = p := by
    rcases hto with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with h | h <;> rw [h] <;> simp [h1, h2]
  have hbwn : ∀ t ∈ d.cover, n ≤ d.bw t := by
    intro t ht
    obtain ⟨j', _, h, _⟩ := (hall t ht).1
    omega
  have htopL : ∀ w ∈ topLeaves d ∅, n ≤ w := by
    intro w hw
    unfold topLeaves at hw
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · simp at hw
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hw
      exact hbwn t (Finset.mem_filter.1 ht).1
  have hadjv : ∀ t, K.Adj t v → t = l ∨ t = p := by
    intro t h
    rcases hvlp with rfl | rfl
    · right; exact (hl t).1 h.symm
    · left; exact (hp t).1 h.symm
  intro j hj hne hmem
  rcases hrole j hj with hk | ⟨t, ht, h1, h2⟩
  · have hjt : j ∈ topGates d C := by
      simp only [topGates, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hk⟩
    rcases (htop.1 j hjt).2.2 v.val hmem with h | h
    · have := htopL _ h; omega
    · omega
  · obtain ⟨hT, hZ, hO, hL⟩ := hall t ht
    rcases hkk : (d.role j).1 with _ | _ | _ | _
    · have hjz : j ∈ gatesOf d C Kind.z t.val := by
        simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj, Prod.ext hkk h1⟩
      rcases (hZ.1 j hjz).2.2 v.val hmem with h | h
      · unfold zLeaves at h
        rcases Finset.mem_insert.1 h with h | h
        · have hvt : v = t := Fin.ext h
          rcases hv with h' | h'
          · rw [← hvt, h', hgz] at hjz; simp at hjz
          · exact ho (h' ▸ hvt ▸ ht)
        · obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 h
          have := hbwn s (Finset.mem_filter.1 hs).1
          omega
      · omega
    · have hjo : j ∈ gatesOf d C Kind.o t.val := by
        simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj, Prod.ext hkk h1⟩
      rcases (hO.1 j hjo).2.2 v.val hmem with h | h
      · unfold oLeaves at h
        obtain ⟨r, hr, hre⟩ := Finset.mem_image.1 h
        have hr' : d.owns t r = true := (Finset.mem_filter.1 hr).2
        have hrv : r = v := by
          have hlr := hL r hr'
          unfold LamOK at hlr
          split_ifs at hlr with hrc
          · rcases hlr.2.1 with h3 | ⟨j', _, h3, _⟩
            · rw [h3] at hre; exact Fin.ext hre
            · rw [h3] at hre; omega
          · rw [hlr] at hre; exact Fin.ext hre
        rw [hrv] at hr'
        have hadj := (how.1 t v hr').1
        have htlp := hadjv t hadj
        by_cases htt : t = t0
        · rcases hv with h' | h'
          · rw [h', ← htt] at hadj; exact K.irrefl hadj
          · rw [htt, hgo] at hjo; simp at hjo
        · have := hcov2 t ht htt
          rcases htlp with h' | h'
          · exact this.1 h'
          · exact this.2 h'
      · omega
    · have hbt := h2 hkk
      by_cases htt : t = t0
      · rw [htt, hbw] at hbt; omega
      · obtain ⟨hnl, hnp⟩ := hcov2 t ht htt
        have htv : t ≠ v := by rcases hvlp with h | h <;> rw [h] <;> assumption
        obtain ⟨j', hj', hbw', _, _, hin⟩ := hT
        have : j' = j := by omega
        subst this
        have hz : d.zroot t ≠ v.val := by
          intro he
          by_cases hG : gatesOf d C Kind.z t.val = ∅
          · have h4 := hZ.2.2.2
            rw [if_pos hG] at h4
            have : t.val ∈ zLeaves d t := Finset.mem_insert_self _ _
            rw [h4, Finset.mem_singleton, he] at this
            exact htv (Fin.ext this)
          · have h4 := hZ.2.2.2
            rw [if_neg hG] at h4
            obtain ⟨j'', _, hj''⟩ := h4
            omega
        have hor : d.oroot t ≠ v.val := by
          intro he
          by_cases hG : gatesOf d C Kind.o t.val = ∅
          · have h4 := hO.2.2.2
            rw [if_pos hG] at h4
            have hm : d.oroot t ∈ oLeaves d t := by rw [h4]; exact Finset.mem_singleton_self _
            unfold oLeaves at hm
            obtain ⟨r, hr, hre⟩ := Finset.mem_image.1 hm
            have hr' : d.owns t r = true := (Finset.mem_filter.1 hr).2
            have hadj := (how.1 t r hr').1
            have hrv : r ≠ v := by
              intro h; rw [h] at hadj
              rcases hadjv t hadj with h5 | h5
              · exact hnl h5
              · exact hnp h5
            have he' : d.lam t r = v.val := hre.trans he
            have hlr := hL r hr'
            unfold LamOK at hlr
            split_ifs at hlr with hrc
            · rcases hlr.2.1 with h3 | ⟨j'', _, h3, _⟩
              · rw [h3] at he'; exact hrv (Fin.ext he')
              · rw [h3] at he'; omega
            · rw [hlr] at he'; exact hrv (Fin.ext he')
          · have h4 := hO.2.2.2
            rw [if_neg hG] at h4
            obtain ⟨j'', _, hj''⟩ := h4
            omega
        rcases hin with h | h <;> rw [h] at hmem <;> simp at hmem <;>
          rcases hmem with h5 | h5 <;> first | exact hz h5.symm | exact hor h5.symm
    · have hjt : j ∈ topGates d C := by
        simp only [topGates, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hkk⟩
      rcases (htop.1 j hjt).2.2 v.val hmem with h | h
      · have := htopL _ h; omega
      · omega

lemma L538_mincover_down {n : ℕ} (K K' : SimpleGraph (Fin n)) (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (T : Finset (Fin n)) (hT : IsMinCover K T) (t0 : Fin n) (ht0 : t0 ∈ T) (htl : t0 = l ∨ t0 = p) :
    IsMinCover K' (T.erase t0) := by
  refine ⟨?_, fun S hS => ?_⟩
  · intro u v huv
    obtain ⟨h0, h1, h2, h3, h4⟩ := (hK' u v).1 huv
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
    have hu : u ≠ t0 := by rcases htl with h | h <;> rw [h] <;> assumption
    have hv : v ≠ t0 := by rcases htl with h | h <;> rw [h] <;> assumption
    rcases hT.1 h0 with h | h
    · left; exact ⟨h, hu⟩
    · right; exact ⟨h, hv⟩
  · have h1 := hT.2 _ (L538_cover_up K K' l p hl hp hK' S hS)
    have h2 := Finset.card_insert_le l S
    have h3 := Finset.card_erase_of_mem ht0
    have h4 : 0 < T.card := Finset.card_pos.2 ⟨t0, ht0⟩
    omega

lemma L538_sg_lt_rev (n p jg i j : ℕ) (hpn : p < n) (h : L538_sg n p jg i < n + L538_sh jg j) :
    i < n + j := by
  unfold L538_sg L538_sh at h
  split_ifs at h <;> omega

lemma L538_ren_gate (n p jg j : ℕ) (hpn : p < n) :
    L538A.ren (n + jg) p (n + L538_sh jg j) = n + j := by
  unfold L538A.ren L538_sh
  split_ifs <;> omega

lemma L538_down {n : ℕ} (K K' : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K'.Adj]
    (l p : Fin n)
    (hl : ∀ v : Fin n, K.Adj l v ↔ v = p) (hp : ∀ v : Fin n, K.Adj p v ↔ v = l)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p)
    (C : Circuit) (d : NCCData n) (hV : Valid n K ∅ C d) :
    ∃ (jg : ℕ) (C' : Circuit) (d' : NCCData n), L538_Ins n p jg C C' ∧
      (gateAt C jg = ⟨GateOp.and, [l.val, p.val]⟩ ∨ gateAt C jg = ⟨GateOp.and, [p.val, l.val]⟩) ∧
      Valid n K' {p} C' d' := by
  classical
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  have hpn := p.isLt
  have hln := l.isLt
  have hV0 := hV
  obtain ⟨hrb, hmc, how, htie, hrole, hall, htop⟩ := hV
  have hlpc : l ∈ d.cover ∨ p ∈ d.cover := hmc.1 ((hl p).2 rfl)
  have hnboth : ¬ (l ∈ d.cover ∧ p ∈ d.cover) := by
    rintro ⟨h1, h2⟩
    have hc : K.IsVertexCover ((d.cover.erase p : Finset (Fin n)) : Set (Fin n)) := by
      intro u v huv
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      rcases hmc.1 huv with h | h
      · by_cases hu : u = p
        · right; have := (hp v).1 (hu ▸ huv); rw [this]; exact ⟨h1, hlp⟩
        · left; exact ⟨h, hu⟩
      · by_cases hv : v = p
        · left; have := (hp u).1 (hv ▸ huv.symm); rw [this]; exact ⟨h1, hlp⟩
        · right; exact ⟨h, hv⟩
    have := hmc.2 _ hc
    have := Finset.card_erase_lt_of_mem h2
    omega
  obtain ⟨t0, o, hto, ht0, ho⟩ : ∃ t0 o : Fin n, ((t0 = l ∧ o = p) ∨ (t0 = p ∧ o = l)) ∧
      t0 ∈ d.cover ∧ o ∉ d.cover := by
    rcases hlpc with h | h
    · exact ⟨l, p, Or.inl ⟨rfl, rfl⟩, h, fun h' => hnboth ⟨h, h'⟩⟩
    · exact ⟨p, l, Or.inr ⟨rfl, rfl⟩, h, fun h' => hnboth ⟨h', h⟩⟩
  obtain ⟨j0, hj0, hbw0, hr0, hzr0, hor0, hgz, hgo, hg0, hto1, hoo, hto', hts, ht0n⟩ :=
    L538_down_struct K l p hl hp C d hV0 t0 o hto ht0 ho
  have hgl : gateAt C j0 = ⟨GateOp.and, [l.val, p.val]⟩ ∨
      gateAt C j0 = ⟨GateOp.and, [p.val, l.val]⟩ := by
    rcases hto with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hg0
    · exact hg0
    · exact hg0.symm
  have honly := L538_down_only K l p hl hp C d hV0 t0 o hto ht0 ho j0 hbw0 hgz hgo
  have hponly := honly p (by rcases hto with ⟨_, h⟩ | ⟨h, _⟩ <;> [right; left] <;> exact h.symm)
  have hlonly := honly l (by rcases hto with ⟨h, _⟩ | ⟨_, h⟩ <;> [left; right] <;> exact h.symm)
  have hbwn : ∀ t ∈ d.cover, n ≤ d.bw t := by
    intro t ht
    obtain ⟨j', _, h, _⟩ := (hall t ht).1
    omega
  have hout : n ≤ C.output := by
    have h4 := htop.2.2.2
    split_ifs at h4 with hG
    · have hm : C.output ∈ topLeaves d ∅ := by rw [h4]; exact Finset.mem_singleton_self _
      unfold topLeaves at hm
      rw [Finset.mem_union] at hm
      rcases hm with hm | hm
      · simp at hm
      · obtain ⟨t, ht, he⟩ := Finset.mem_image.1 hm
        rw [← he]; exact hbwn t (Finset.mem_filter.1 ht).1
    · obtain ⟨j, _, hj⟩ := h4; omega
  set C' : Circuit := ⟨L538A.del C.gates j0 (n + j0) p.val, L538A.ren (n + j0) p.val C.output⟩
    with hC'
  have hI : L538_Ins n p j0 C C' := L538_del_ins C j0 hj0 p hponly (by omega)
    (fun j hj i hi => hrb j (by omega) i hi)
  obtain ⟨hlen, hjgl, hgate, hout', hpre⟩ := hI
  have hI : L538_Ins n p j0 C C' := ⟨hlen, hjgl, hgate, hout', hpre⟩
  have hshl : ∀ j < C'.gates.length, L538_sh j0 j < C.gates.length := by
    intro j hj; simp only [L538_sh]; split_ifs <;> omega
  have hsgl : L538_sg n p.val j0 l.val = l.val := by
    simp only [L538_sg]
    rw [if_neg (fun h => hlp (Fin.ext h)), if_neg (by omega)]
  have hnl : ∀ j < C'.gates.length, l.val ∉ (gateAt C' j).inputs := by
    intro j hj hmem
    have := hlonly (L538_sh j0 j) (hshl j hj) (L538_sh_ne j0 j)
    rw [hgate j hj] at this
    apply this
    simp only [List.mem_map]
    exact ⟨l.val, hmem, hsgl⟩
  have hrb' : ReadsBack n C' := by
    intro j hj i hi
    have := hrb (L538_sh j0 j) (hshl j hj) (L538_sg n p.val j0 i) (by
      rw [hgate j hj]; simp only [List.mem_map]; exact ⟨i, hi, rfl⟩)
    exact L538_sg_lt_rev n p.val j0 i j hpn this
  have hcov2 : ∀ t ∈ d.cover, t ≠ t0 → t ≠ l ∧ t ≠ p := by
    intro t ht hne
    rcases hto with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => hne (h.trans h1.symm), fun h => ho (h2 ▸ h ▸ ht)⟩
    · exact ⟨fun h => ho (h2 ▸ h ▸ ht), fun h => hne (h.trans h1.symm)⟩
  have ht0lp : t0 = l ∨ t0 = p := by rcases hto with ⟨h, _⟩ | ⟨h, _⟩ <;> [left; right] <;> exact h
  have hadjlp : ∀ t r, K.Adj t r → (r = l ∨ r = p) → (t = l ∨ t = p) := by
    intro t r h hr
    rcases hr with rfl | rfl
    · right; exact (hl t).1 h.symm
    · left; exact (hp t).1 h.symm
  let ren := L538A.ren (n + j0) p.val
  let sg := L538_sg n p.val j0
  have hsr : ∀ w, w ≠ p.val → sg (ren w) = w := fun w hw => L538_sg_ren n p.val j0 w hpn hw
  have hrenv : ∀ v : Fin n, ren v.val = v.val := by
    intro v; show L538A.ren (n + j0) p.val v.val = v.val
    unfold L538A.ren; have := v.isLt; rw [if_pos (by omega)]
  have hsgv : ∀ v : Fin n, v ≠ p → sg v.val = v.val := by
    intro v hv
    show L538_sg n p.val j0 v.val = v.val
    have := v.isLt
    simp only [L538_sg]
    rw [if_neg (fun h => hv (Fin.ext h)), if_neg (by omega)]
  have hzrp' : ∀ t ∈ d.cover, t ≠ t0 → d.zroot t ≠ p.val ∧ d.oroot t ≠ p.val := by
    intro t ht hne
    obtain ⟨jt, hjt, hbwt, hrt, _, hin⟩ := (hall t ht).1
    have hjne : jt ≠ j0 := by
      intro h; rw [h, hr0] at hrt
      exact hne (Fin.ext (Prod.mk.inj hrt).2.symm)
    have := hponly jt hjt hjne
    rcases hin with h | h <;> rw [h] at this
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact ⟨fun e => this.1 e.symm, fun e => this.2 e.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact ⟨fun e => this.2 e.symm, fun e => this.1 e.symm⟩
  have hlamp : ∀ t ∈ d.cover, t ≠ t0 → ∀ r, d.owns t r = true →
      d.lam t r ≠ p.val ∧ d.lam t r ≠ l.val ∧ r ≠ l ∧ r ≠ p := by
    intro t ht hne r hr
    obtain ⟨htl, htp⟩ := hcov2 t ht hne
    have hadj := (how.1 t r hr).1
    have hrl : r ≠ l := fun h => by rcases hadjlp t r hadj (Or.inl h) with h' | h' <;> contradiction
    have hrp : r ≠ p := fun h => by rcases hadjlp t r hadj (Or.inr h) with h' | h' <;> contradiction
    have hlr := (hall t ht).2.2.2 r hr
    unfold LamOK at hlr
    split_ifs at hlr with hrc
    · rcases hlr.2.1 with h3 | ⟨j'', _, h3, _⟩
      · rw [h3]
        exact ⟨fun e => hrp (Fin.ext e), fun e => hrl (Fin.ext e), hrl, hrp⟩
      · rw [h3]; exact ⟨by omega, by omega, hrl, hrp⟩
    · rw [hlr]
      exact ⟨fun e => hrp (Fin.ext e), fun e => hrl (Fin.ext e), hrl, hrp⟩
  let d' : NCCData n :=
    { cover := d.cover.erase t0
      owns := fun u v => d.owns u v && decide (u ≠ t0)
      tie := d.tie
      role := fun j => d.role (L538_sh j0 j)
      bw := fun t => ren (d.bw t)
      zroot := fun t => ren (d.zroot t)
      oroot := fun t => ren (d.oroot t)
      lam := fun t r => ren (d.lam t r) }
  have hrole' : ∀ j < C'.gates.length, d.role (L538_sh j0 j) = d'.role j := fun _ _ => rfl
  have hGl : ∀ k t, ∀ j ∈ gatesOf d' C' k t, j < C'.gates.length := by
    intro k t j hj
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hj
    exact hj.1
  have hpc' : p ∉ d'.cover := by
    show p ∉ d.cover.erase t0
    rw [Finset.mem_erase, not_and]
    intro hne hpc
    rcases hto with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ho (h2 ▸ hpc)
    · exact hne h1.symm
  have hflag : ∀ w, w ≠ l.val → (IsCentred n C d (sg w) ↔ IsCentred n C' d' w) :=
    L538_flag_tr C C' p l.val j0 hI d d'
      (by
        intro i hi hip
        show i ∈ d.cover ↔ i ∈ d.cover.erase t0
        rw [Finset.mem_erase]
        have : i ≠ t0 := by
          rcases ht0lp with h | h <;> rw [h]
          · exact fun e => hi (congrArg Fin.val e)
          · exact hip
        exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩)
      hpc' hrole' (by rw [hr0]; simp) hnl hrb'
  refine ⟨j0, C', d', hI, hgl, hrb', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact L538_mincover_down K K' l p hl hp hK' d.cover hmc t0 ht0 ht0lp
  · refine ⟨?_, ?_⟩
    · intro u v h
      change (d.owns u v && decide (u ≠ t0)) = true at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hadj, huc⟩ := how.1 u v h1
      obtain ⟨hul, hup⟩ := hcov2 u huc h2
      have hvl : v ≠ l := fun e => by rcases hadjlp u v hadj (Or.inl e) with h' | h' <;> contradiction
      have hvp : v ≠ p := fun e => by rcases hadjlp u v hadj (Or.inr e) with h' | h' <;> contradiction
      exact ⟨(hK' u v).2 ⟨hadj, hul, hup, hvl, hvp⟩, Finset.mem_erase.2 ⟨h2, huc⟩⟩
    · intro u v huv
      obtain ⟨hadj, hul, hup, hvl, hvp⟩ := (hK' u v).1 huv
      have hu0 : u ≠ t0 := by rcases ht0lp with h | h <;> rw [h] <;> assumption
      have hv0 : v ≠ t0 := by rcases ht0lp with h | h <;> rw [h] <;> assumption
      show (d.owns u v && decide (u ≠ t0)) ≠ (d.owns v u && decide (v ≠ t0))
      simp only [hu0, hv0, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
      exact how.2 u v hadj
  · intro s t h
    obtain ⟨h1, h2⟩ := htie s t h
    have hs0 : s ≠ t0 := by intro e; rw [e, ht0n] at h; cases h
    have ht0' : t ≠ t0 := by intro e; rw [e] at h; exact hts s h
    refine ⟨Finset.mem_erase.2 ⟨hs0, h1⟩, ?_⟩
    show (d.owns t s && decide (t ≠ t0)) = true
    simp [h2, ht0']
  · intro j hj
    show (d.role (L538_sh j0 j)).1 = Kind.top ∨ ∃ t ∈ d.cover.erase t0,
      (d.role (L538_sh j0 j)).2 = t.val ∧ ((d.role (L538_sh j0 j)).1 = Kind.b →
        ren (d.bw t) = n + j)
    rcases hrole (L538_sh j0 j) (hshl j hj) with h | ⟨t, ht, h1, h2⟩
    · left; exact h
    · rcases hk : (d.role (L538_sh j0 j)).1 with _ | _ | _ | _
      · right
        have htt : t ≠ t0 := by
          intro e
          have : L538_sh j0 j ∈ gatesOf d C Kind.z t0.val := by
            simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
            exact ⟨hshl j hj, Prod.ext hk (e ▸ h1)⟩
          rw [hgz] at this; simp at this
        exact ⟨t, Finset.mem_erase.2 ⟨htt, ht⟩, h1, fun hb => by cases hb⟩
      · right
        have htt : t ≠ t0 := by
          intro e
          have : L538_sh j0 j ∈ gatesOf d C Kind.o t0.val := by
            simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
            exact ⟨hshl j hj, Prod.ext hk (e ▸ h1)⟩
          rw [hgo] at this; simp at this
        exact ⟨t, Finset.mem_erase.2 ⟨htt, ht⟩, h1, fun hb => by cases hb⟩
      · right
        have hb := h2 hk
        have htt : t ≠ t0 := by
          intro e; rw [e, hbw0] at hb
          exact L538_sh_ne j0 j (by omega)
        refine ⟨t, Finset.mem_erase.2 ⟨htt, ht⟩, h1, fun _ => ?_⟩
        rw [hb]
        exact L538_ren_gate n p.val j0 j hpn
      · left; rfl
  · intro t ht
    obtain ⟨htne, htc⟩ := Finset.mem_erase.1 ht
    obtain ⟨hT, hZ, hO, hL⟩ := hall t htc
    obtain ⟨hzp, hop⟩ := hzrp' t htc htne
    have hzr : d.zroot t = sg (d'.zroot t) := (hsr _ hzp).symm
    have hor : d.oroot t = sg (d'.oroot t) := (hsr _ hop).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨jt, hjt, hbwt, hrt, hopt, hin⟩ := hT
      have hjne : jt ≠ j0 := by
        intro h; rw [h, hr0] at hrt
        exact htne (Fin.ext (Prod.mk.inj hrt).2.symm)
      obtain ⟨j', hj', hjs⟩ := L538_unsh j0 jt C'.gates.length (by omega) hjne hjgl
      refine ⟨j', hj', ?_, ?_, ?_, ?_⟩
      · show ren (d.bw t) = n + j'
        rw [hbwt, ← hjs]; exact L538_ren_gate n p.val j0 j' hpn
      · show d.role (L538_sh j0 j') = _
        rw [hjs]; exact hrt
      · have := hgate j' hj'
        rw [hjs] at this
        rw [this] at hopt
        exact hopt
      · have hg := hgate j' hj'
        rw [hjs] at hg
        rw [hg] at hin
        simp only at hin
        rw [hzr, hor] at hin
        have hinj := L538_sg_inj n p.val j0 hpn
        rcases hin with h | h
        · left
          exact (List.map_injective_iff.2 hinj) (by rw [h]; rfl)
        · right
          exact (List.map_injective_iff.2 hinj) (by rw [h]; rfl)
    · rw [L538_gatesOf_tr C C' p.val j0 hI d d' hrole' Kind.z t.val (by rw [hr0]; simp)] at hZ
      have hzl : zLeaves d t = (zLeaves d' t).image sg := by
        unfold zLeaves
        rw [Finset.image_insert, hsgv t (hcov2 t htc htne).2]
        congr 1
        show (d.cover.filter (fun s => d.tie s = some t)).image d.bw =
          (((d.cover.erase t0).filter (fun s => d.tie s = some t)).image (fun s => ren (d.bw s))).image sg
        rw [Finset.image_image, Finset.filter_erase, Finset.erase_eq_of_notMem (by
          rw [Finset.mem_filter, not_and]; intro _ h; rw [ht0n] at h; cases h)]
        apply Finset.image_congr
        intro s hs
        have hs' := (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).1
        show d.bw s = sg (ren (d.bw s))
        rw [hsr _ (by have := hbwn s hs'; omega)]
      rw [hzl, hzr] at hZ
      exact (L538_tree_tr C C' p.val j0 hpn hI _ (hGl _ _) _ _).1 hZ
    · rw [L538_gatesOf_tr C C' p.val j0 hI d d' hrole' Kind.o t.val (by rw [hr0]; simp)] at hO
      have hol : oLeaves d t = (oLeaves d' t).image sg := by
        unfold oLeaves
        rw [Finset.image_image]
        have hf : (Finset.univ.filter (fun r => d'.owns t r = true)) =
            (Finset.univ.filter (fun r => d.owns t r = true)) := by
          apply Finset.filter_congr
          intro r _
          show (d.owns t r && decide (t ≠ t0)) = true ↔ _
          simp [htne]
        rw [hf]
        apply Finset.image_congr
        intro r hr
        have hr' := (Finset.mem_filter.1 (Finset.mem_coe.1 hr)).2
        show d.lam t r = sg (ren (d.lam t r))
        rw [hsr _ (hlamp t htc htne r hr').1]
      rw [hol, hor] at hO
      exact (L538_tree_tr C C' p.val j0 hpn hI _ (hGl _ _) _ _).1 hO
    · intro r hr
      change (d.owns t r && decide (t ≠ t0)) = true at hr
      have hr' : d.owns t r = true := by simpa [htne] using hr
      obtain ⟨hlp1, hll1, hrl, hrp⟩ := hlamp t htc htne r hr'
      have hr0' : r ≠ t0 := by rcases ht0lp with h | h <;> rw [h] <;> assumption
      have hmem : r ∈ d'.cover ↔ r ∈ d.cover := by
        show r ∈ d.cover.erase t0 ↔ _
        rw [Finset.mem_erase]
        exact ⟨fun h => h.2, fun h => ⟨hr0', h⟩⟩
      have hlam : sg (d'.lam t r) = d.lam t r := hsr _ hlp1
      have hlr := hL r hr'
      unfold LamOK at hlr ⊢
      by_cases hrc : r ∈ d.cover
      · rw [if_pos (hmem.2 hrc)]
        rw [if_pos hrc] at hlr
        obtain ⟨hc, hform, htie'⟩ := hlr
        have hl'ne : d'.lam t r ≠ l.val := by
          intro e
          have : sg (d'.lam t r) = sg l.val := by rw [e]
          rw [hlam, hsgv l hlp] at this
          exact hll1 this
        refine ⟨?_, ?_, ?_⟩
        · rw [← hlam] at hc
          exact (hflag _ hl'ne).1 hc
        · rcases hform with h | ⟨j, hj, h, hr2⟩
          · left
            show ren (d.lam t r) = r.val
            rw [h]; exact hrenv r
          · right
            have hjne : j ≠ j0 := by intro e; rw [e, hr0] at hr2; cases hr2
            obtain ⟨j', hj', hjs⟩ := L538_unsh j0 j C'.gates.length (by omega) hjne hjgl
            refine ⟨j', hj', ?_, ?_⟩
            · show ren (d.lam t r) = n + j'
              rw [h, ← hjs]; exact L538_ren_gate n p.val j0 j' hpn
            · show d.role (L538_sh j0 j') = _
              rw [hjs]; exact hr2
        · intro hti
          show ren (d.lam t r) = ren (d.zroot r)
          rw [htie' hti]
      · rw [if_neg (fun h => hrc (hmem.1 h))]
        rw [if_neg hrc] at hlr
        show ren (d.lam t r) = r.val
        rw [hlr]; exact hrenv r
  · rw [L538_topGates_tr C C' p.val j0 hI d d' hrole' (by rw [hr0]; simp)] at htop
    have htl2 : topLeaves d ∅ = (topLeaves d' {p}).image sg := by
      unfold topLeaves
      rw [Finset.image_union, Finset.image_empty, Finset.empty_union, Finset.image_singleton,
        Finset.image_singleton, Finset.image_image]
      show (d.cover.filter (fun t => d.tie t = none)).image d.bw =
        {sg p.val} ∪ ((d.cover.erase t0).filter (fun t => d.tie t = none)).image (sg ∘ fun t => ren (d.bw t))
      have hcov_eq : d.cover = insert t0 (d.cover.erase t0) := (Finset.insert_erase ht0).symm
      rw [hcov_eq, Finset.filter_insert, if_pos ht0n, Finset.image_insert, Finset.erase_insert
        (Finset.notMem_erase t0 d.cover)]
      have e1 : d.bw t0 = sg p.val := by
        rw [hbw0]; show n + j0 = L538_sg n p.val j0 p.val; simp [L538_sg]
      rw [e1, Finset.insert_eq]
      congr 1
      apply Finset.image_congr
      intro s hs
      have hs' := (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).1
      show d.bw s = sg (ren (d.bw s))
      rw [hsr _ (by have := hbwn s (Finset.mem_of_mem_erase hs'); omega)]
    rw [htl2, hout'] at htop
    have hGt : ∀ j ∈ topGates d' C', j < C'.gates.length := by
      intro j hj
      simp only [topGates, Finset.mem_filter, Finset.mem_range] at hj
      exact hj.1
    exact (L538_tree_tr C C' p.val j0 hpn hI _ hGt _ _).1 htop

theorem PEqualNP.Outside.L_meta_538 : ∀ (n : ℕ) (K K' : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K'.Adj] (l p : Fin n), ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 3 ≤ k → Nonempty (K.Adj ↪r (PEqualNP.Library.Subdivision.subdiv k H).Adj) → (∀ v : Fin n, K.Adj l v ↔ v = p) → (∀ v : Fin n, K.Adj p v ↔ v = l) → (∃ u v : Fin n, K.Adj u v ∧ u ≠ l ∧ u ≠ p) → (∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K' {p}) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K' {p} C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K ∅) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K ∅ C) := by
  intro n K K' _ _ l p k m H _ _ hl hp hex hK' hyp C
  have hlp : l ≠ p := by
    intro h; have h1 := (hl p).2 rfl; rw [h] at h1; exact K.irrefl h1
  have hpK' : ∀ v, ¬ K'.Adj p v := fun v h => ((hK' p v).1 h).2.2.1 rfl
  have hFrec : ∀ (v w : Fin n), ((v = l ∧ w = p) ∨ (v = p ∧ w = l)) → ∀ x,
      graphFun K ∅ (Function.update (Function.update x w (x w && x v)) v true) = graphFun K ∅ x :=
    fun v w h x => L538_fun_rec K l p hl hp v w h x
  have hFl : ∀ x, graphFun K ∅ (Function.update x l true) = graphFun K' {p} x :=
    fun x => L538_fun_l K K' l p hl hp hK' x
  have hFins : ∀ x, graphFun K' {p} (Function.update x p (x l && x p)) = graphFun K ∅ x :=
    fun x => L538_fun_ins K K' l p hl hp hK' x
  constructor
  · rintro ⟨hmin, hfun⟩
    have hsmall : ∀ v w : Fin n, ((v = l ∧ w = p) ∨ (v = p ∧ w = l)) → ∀ D : Circuit, FanInTwo D →
        circuitFun n D = (fun x => graphFun K ∅ (Function.update x v true)) →
        C.size ≤ D.size + 1 := by
      intro v w hvw D hD hDf
      obtain ⟨D', hD', hsz, hD'f⟩ := L538_prepend D hD v w
      have := hmin.2 D' hD' (by
        funext x; rw [hD'f, hDf, hfun]; exact hFrec v w hvw x)
      omega
    obtain ⟨jg, hjg, y, hy, hyl, hgl, hlonly⟩ := L538_uniq (graphFun K ∅) C hmin hfun l
      (hsmall l p (Or.inl ⟨rfl, rfl⟩)) (L538_fun_dep K l p hl hp l (Or.inl rfl)).1
      (L538_fun_dep K l p hl hp l (Or.inl rfl)).2
    obtain ⟨jg2, hjg2, y2, hy2, hyp2, hgp, hponly⟩ := L538_uniq (graphFun K ∅) C hmin hfun p
      (hsmall p l (Or.inr ⟨rfl, rfl⟩)) (L538_fun_dep K l p hl hp p (Or.inr rfl)).1
      (L538_fun_dep K l p hl hp p (Or.inr rfl)).2
    set C' : Circuit := ⟨L538A.del C.gates jg (n + jg) y, L538A.ren (n + jg) y C.output⟩ with hC'
    have hC'fan : FanInTwo C' := L538A.fanInTwo_del C.gates C.output jg (n + jg) y _ hmin.1
    have hC'size : C'.size + 1 = C.size := by
      show (L538A.del C.gates jg (n + jg) y).length + 1 = C.gates.length
      rw [L538A.del_length _ _ _ _ hjg]; omega
    have hnl' : ∀ j < C'.gates.length, l.val ∉ L538A.deps (gateAt C' j) := by
      intro j hj hmem
      have hjlen : j + 1 < C.gates.length := by
        have : C'.gates.length + 1 = C.gates.length := hC'size
        omega
      by_cases hjj : j < jg
      · rw [L538_del_gate_lt C jg y n hjg j hjj] at hmem
        exact hlonly j (by omega) (by omega) hmem
      · rw [L538_del_gate_ge C jg y n hjg j (by omega) hjlen, L538A.deps_renG] at hmem
        simp only [List.mem_map] at hmem
        obtain ⟨i, hi, hie⟩ := hmem
        unfold L538A.ren at hie
        split_ifs at hie with h1 h2
        · subst hie; exact hlonly (j + 1) hjlen (by omega) hi
        · exact hyl hie
        · have := l.isLt; omega
    have hC'out : C'.output ≠ l.val := by
      show L538A.ren (n + jg) y C.output ≠ l.val
      have hne := L538_out_ne K l p hl hp C hfun l (Or.inl rfl)
      unfold L538A.ren
      split_ifs with h1 h2
      · exact hne
      · exact hyl
      · have := l.isLt; omega
    have hC'fun : circuitFun n C' = graphFun K' {p} := by
      funext x
      rw [← L538_noread C' l hnl' hC'out x true, ← hFl x, ← hfun]
      show Circuit.eval ⟨L538A.del C.gates jg (n + jg) y, L538A.ren (n + jg) y C.output⟩
        (List.ofFn (Function.update x l true)) = Circuit.eval C (List.ofFn (Function.update x l true))
      have hlen : (List.ofFn (Function.update x l true)).length = n := List.length_ofFn
      have hval : (C.wires (List.ofFn (Function.update x l true))).getD (n + jg) false =
          (C.wires (List.ofFn (Function.update x l true))).getD y false := by
        rcases hgl with hg | hg
        · rw [L538_gate_val C jg hjg l.val y ⟨by have := l.isLt; omega, hy⟩ hg _ hlen,
            L538_wire_input C _ l]
          simp
        · rw [L538_gate_val C jg hjg y l.val ⟨hy, by have := l.isLt; omega⟩ hg _ hlen,
            L538_wire_input C _ l]
          simp
      have := L538A.del_eval C.gates C.output (List.ofFn (Function.update x l true)) jg y hjg
        (Or.inl (by rw [hlen]; exact hy)) (fun g _ _ => by rw [hlen] at *; exact hval)
        (fun _ => by rw [hlen] at *; exact hval)
      rw [hlen] at this
      exact this
    have hC'min : IsMinimalCircuit n C' := by
      refine ⟨hC'fan, fun D hD hDf => ?_⟩
      obtain ⟨D', hD', hsz, hD'f⟩ := L538_prepend D hD l p
      have := hmin.2 D' hD' (by
        funext x; rw [hD'f, hDf, hC'fun, hfun, ← hFins x, Bool.and_comm])
      have h2 : C'.size + 1 = C.size := hC'size
      omega
    obtain ⟨d', hd'⟩ := (hyp C').1 ⟨hC'min, hC'fun⟩
    have hlenC : C'.gates.length + 1 = C.gates.length := hC'size
    have hops' : ∀ j < C'.gates.length, (gateAt C' j).op ≠ GateOp.not := by
      intro j hj h
      rcases L538_nested_ops K' {p} C' d' hd' j hj with h1 | ⟨h1, _⟩ <;> rw [h] at h1 <;> cases h1
    have hdeps : ∀ g : Gate, g.op ≠ GateOp.not → L538A.deps g = g.inputs := by
      intro g hg; obtain ⟨op, ins⟩ := g; cases op <;> simp_all [L538A.deps]
    have hopsC : ∀ j < C.gates.length, j ≠ jg → (gateAt C j).op ≠ GateOp.not := by
      intro j hj hne
      by_cases hjj : j < jg
      · rw [← L538_del_gate_lt C jg y n hjg j hjj]; exact hops' j (by omega)
      · have := hops' (j - 1) (by omega)
        rw [L538_del_gate_ge C jg y n hjg (j - 1) (by omega) (by omega)] at this
        simp only [L538A.renG] at this
        rwa [show j - 1 + 1 = j by omega] at this
    have hnlS : ∀ j < C'.gates.length, l.val ∉ (gateAt C' j).inputs := fun j hj => by
      rw [← hdeps _ (hops' j hj)]; exact hnl' j hj
    have hjj : jg2 = jg := by
      by_contra hne
      have hrd := L538_preader K' p hpK' C' d' hd'
      have hpin : p.val ∈ (gateAt C jg2).inputs := by
        rcases hgp with h | h <;> rw [h] <;> simp
      have hand : (gateAt C jg2).op = GateOp.and := by
        rcases hgp with h | h <;> rw [h]
      have hlen' : C'.gates.length + 1 = C.gates.length := hC'size
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := hrd jg2 (by omega) (by rw [L538_del_gate_lt C jg y n hjg jg2 hlt]; exact hpin)
        rw [L538_del_gate_lt C jg y n hjg jg2 hlt, hand] at this
        exact absurd this (by intro h; cases h)
      · have hj1 : jg2 - 1 + 1 = jg2 := by omega
        have hg2 := L538_del_gate_ge C jg y n hjg (jg2 - 1) (by omega) (by omega)
        rw [hj1] at hg2
        have hpin' : p.val ∈ (gateAt C' (jg2 - 1)).inputs := by
          rw [hg2]
          simp only [L538A.renG, List.mem_map]
          refine ⟨p.val, hpin, ?_⟩
          unfold L538A.ren
          have := p.isLt
          rw [if_pos (by omega)]
        have := hrd (jg2 - 1) (by omega) hpin'
        rw [hg2] at this
        simp only [L538A.renG] at this
        rw [hand] at this
        exact absurd this (by intro h; cases h)
    subst hjj
    have hyeq : y = p.val := by
      have hlpv : l.val ≠ p.val := fun h => hlp (Fin.ext h)
      rcases hgl with h1 | h1 <;> rcases hgp with h2 | h2 <;> rw [h1] at h2 <;>
        simp only [Gate.mk.injEq, List.cons.injEq, and_true, true_and] at h2 <;> omega
    subst hyeq
    have hrb : ∀ j < jg2, ∀ i ∈ (gateAt C j).inputs, i < n + j := by
      intro j hj i hi
      have := hd'.1 j (by have : C'.gates.length + 1 = C.gates.length := hC'size; omega)
      rw [L538_del_gate_lt C jg2 p.val n hjg j hj] at this
      exact this i hi
    have hponlyS : ∀ j < C.gates.length, j ≠ jg2 → p.val ∉ (gateAt C j).inputs :=
      fun j hj hne => by rw [← hdeps _ (hopsC j hj hne)]; exact hponly j hj hne
    have hI : L538_Ins n p jg2 C C' := L538_del_ins C jg2 hjg p hponlyS
      (L538_out_ne K l p hl hp C hfun p (Or.inr rfl)) hrb
    have hg : gateAt C jg2 = ⟨GateOp.and, [l.val, p.val]⟩ ∨
        gateAt C jg2 = ⟨GateOp.and, [p.val, l.val]⟩ := hgl
    exact L538_up K K' l p hl hp hK' C C' jg2 hI hg hnlS d' hd'
  · rintro ⟨d, hd⟩
    obtain ⟨jg, C', d', hI, hg, hd'⟩ := L538_down K K' l p hl hp hK' C d hd
    obtain ⟨⟨hC'fan, hC'min⟩, hC'fun⟩ := (hyp C').2 ⟨d', hd'⟩
    obtain ⟨hCfan, hCsize⟩ := L538_ins_fan C C' p jg hI
      (by rcases hg with h | h <;> rw [h] <;> simp) hC'fan
    have hCfun : circuitFun n C = graphFun K ∅ := by
      funext x; rw [L538_ins_eval C C' l p jg hI hg x, hC'fun, hFins]
    refine ⟨⟨hCfan, fun D hD hDf => ?_⟩, hCfun⟩
    obtain ⟨D', hD', hsz, hD'f⟩ := L538_elim (graphFun K ∅) D hD (hDf.trans hCfun) l
      (L538_fun_dep K l p hl hp l (Or.inl rfl)).1 (L538_fun_dep K l p hl hp l (Or.inl rfl)).2
    have := hC'min D' hD' (by rw [hD'f, hC'fun]; funext x; exact hFl x)
    omega
