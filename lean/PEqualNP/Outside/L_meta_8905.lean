import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8905

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Each original wire becomes a constant or a reference to a new wire.
abbrev Ref := Bool ⊕ ℕ

def fixed : Ref := .inl false

def value (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr i => w.getD i false

def valid (n : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr i => i < n

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = w.length + (g :: gs).length
    rw [ih]
    simp [step]
    omega

lemma run_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma getD_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

def allowed (g : Gate) : Prop := g.op = .and ∨ g.op = .or

def binaryGate (g : Gate) : Prop := allowed g ∧ g.inputs.length = 2

def back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j

lemma back_append {n : ℕ} {a b : List Gate} (ha : back n a)
    (hb : back (n + a.length) b) : back n (a ++ b) := by
  intro j hj i hi
  by_cases h : j < a.length
  · rw [List.getElem_append_left h] at hi
    exact ha j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have hb' := hb (j - a.length) (by simp at hj; omega) i hi
    omega

def binary (op : GateOp) (neutral : Bool) (n : ℕ) (a b : Ref) : Ref × List Gate :=
  match a, b with
  | .inl c, _ => (if c = neutral then b else .inl c, [])
  | _, .inl c => (if c = neutral then a else .inl c, [])
  | .inr i, .inr j => (.inr n, [⟨op, [i, j]⟩])

def emit (op : GateOp) (n : ℕ) (rs : List Ref) : Ref × List Gate :=
  match op, rs with
  | .and, [] => (.inl true, [])
  | .or, [] => (.inl false, [])
  | .and, [a] | .or, [a] => (a, [])
  | .and, a :: b :: _ => binary .and true n a b
  | .or, a :: b :: _ => binary .or false n a b
  | _, _ => (fixed, [])

lemma emit_ok (op : GateOp) (n : ℕ) (rs : List Ref)
    (hop : op = .and ∨ op = .or) (hl : rs.length ≤ 2)
    (hv : ∀ r ∈ rs, valid n r) :
    let e := emit op n rs
    e.2.length ≤ 1 ∧ (rs = [] → e.2 = []) ∧ (∀ g ∈ e.2, binaryGate g) ∧
      back n e.2 ∧
      ∀ w : List Bool, w.length = n →
        valid (run e.2 w).length e.1 ∧
          value (run e.2 w) e.1 = op.eval (rs.map (value w)) := by
  dsimp only
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [emit, back, valid, value, GateOp.eval]
  · rcases hop with rfl | rfl
    · simpa [emit, back, run, GateOp.eval] using
        (fun (w : List Bool) (hw : w.length = n) => hw.symm ▸ hv a (by simp))
    · simpa [emit, back, run, GateOp.eval] using
        (fun (w : List Bool) (hw : w.length = n) => hw.symm ▸ hv a (by simp))
  · have ha := hv a (by simp)
    have hb := hv b (by simp)
    rcases hop with rfl | rfl <;>
      rcases a with (a | a) <;> rcases b with (b | b) <;>
      (try cases (show Bool from a)) <;> (try cases (show Bool from b)) <;>
      simp_all [emit, binary, run, step, binaryGate, allowed, back, valid, value, GateOp.eval,
        -List.getD_eq_getElem?_getD] <;>
      intro w hw <;> simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
  · simp at hl

def read (refs : List Ref) (i : ℕ) : Ref := refs.getD i fixed

-- The reference table recovers every original wire and only points to available new wires.
def related (refs : List Ref) (w old : List Bool) : Prop :=
  old = refs.map (value w) ∧ ∀ r ∈ refs, valid w.length r

lemma read_value {refs : List Ref} {w old : List Bool} (h : related refs w old) (i : ℕ) :
    value w (read refs i) = old.getD i false := by
  rw [h.1]
  exact (List.getD_map refs fixed (value w)).symm

lemma related_extend {refs : List Ref} {w old : List Bool} (h : related refs w old)
    (extra : List Gate) (r : Ref) (b : Bool) (hv : valid (run extra w).length r)
    (he : value (run extra w) r = b) :
    related (refs ++ [r]) (run extra w) (old ++ [b]) := by
  have same : refs.map (value (run extra w)) = refs.map (value w) := by
    apply List.map_congr_left
    intro q hq
    rcases q with c | i
    · rfl
    · exact run_prefix _ _ _ (h.2 _ hq)
  constructor
  · rw [List.map_append, same, ← h.1]
    simp [he]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have hqv := h.2 q hq
      cases q with
      | inl c => trivial
      | inr i =>
        change i < w.length at hqv
        change i < (run extra w).length
        rw [run_length]
        omega
    · simpa using (List.mem_singleton.mp hq ▸ hv : valid (run extra w).length q)

lemma table_valid {refs : List Ref} {n : ℕ} (h : ∀ r ∈ refs, valid n r) (i : ℕ) :
    valid n (read refs i) := by
  by_cases hi : i < refs.length
  · rw [read, List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [read, List.getD_eq_default _ _ (by omega)]
    trivial

-- Emit at most one gate per source gate. A zero-input gate emits none.
lemma sweep (gs : List Gate) (hg : ∀ g ∈ gs, allowed g ∧ g.inputs.length ≤ 2)
    (refs : List Ref) (n : ℕ) (hvalid : ∀ r ∈ refs, valid n r) :
    ∃ (out : List Gate) (outRefs : List Ref),
      (∀ g ∈ out, binaryGate g) ∧ back n out ∧ out.length ≤ gs.length ∧
      ((∃ g ∈ gs, g.inputs = []) → out.length < gs.length) ∧
      ∀ w old, w.length = n → related refs w old →
        related outRefs (run out w) (run gs old) := by
  induction gs generalizing refs n with
  | nil => exact ⟨[], refs, by simp, by simp [back], by simp, by simp, fun _ _ _ h => h⟩
  | cons g gs ih =>
    have hg' := hg g (by simp)
    let rs := g.inputs.map (read refs)
    let e := emit g.op n rs
    have hv : ∀ r ∈ rs, valid n r := by
      intro r hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
      exact table_valid hvalid i
    obtain ⟨hlen, hzero, hgood, hback, heval⟩ :
        e.2.length ≤ 1 ∧ (rs = [] → e.2 = []) ∧ (∀ g ∈ e.2, binaryGate g) ∧
        back n e.2 ∧ ∀ w : List Bool, w.length = n →
          valid (run e.2 w).length e.1 ∧
            value (run e.2 w) e.1 = g.op.eval (rs.map (value w)) :=
      emit_ok g.op n rs hg'.1 (by simpa [rs] using hg'.2) hv
    have heValid : valid (n + e.2.length) e.1 := by
      obtain ⟨h, _⟩ := heval (List.replicate n false) (by simp)
      simpa [run_length] using h
    obtain ⟨tail, outRefs, htail, htback, hsize, hstrict, hcorrect⟩ :=
      ih (fun g hg₀ => hg g (by simp [hg₀])) (refs ++ [e.1]) (n + e.2.length) (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · have h := hvalid r hr
          cases r with
          | inl _ => trivial
          | inr i => exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
        · rwa [List.mem_singleton.mp hr])
    refine ⟨e.2 ++ tail, outRefs, ?_, back_append hback htback, ?_, ?_, ?_⟩
    · intro g hg
      exact (List.mem_append.mp hg).elim (hgood g) (htail g)
    · simp only [List.length_append, List.length_cons]
      omega
    · rintro ⟨a, ha, hnil⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · have hz := hzero (by simp [rs, hnil])
        simp [hz]
        omega
      · have hs := hstrict ⟨a, ha, hnil⟩
        simp only [List.length_append, List.length_cons]
        omega
    · intro w old hw hr
      obtain ⟨hv', he'⟩ := heval w hw
      have hm : rs.map (value w) = g.inputs.map (fun i => old.getD i false) := by
        dsimp only [rs]
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => read_value hr i)
      rw [hm] at he'
      rw [run_append]
      change related outRefs (run tail (run e.2 w)) (run gs (step old g))
      exact hcorrect _ _ (by rw [run_length, hw]) (related_extend hr _ _ _ hv' he')

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

lemma gateAt_get {C : Circuit} {j : ℕ} (h : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ h

lemma normalize {n : ℕ} (C : Circuit) (hM : Monotone2 C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
      ((∃ g ∈ C.gates, g.inputs = []) → D.size < C.size) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let refs : List Ref := List.ofFn (fun i : Fin n => .inr i.val)
  have hr : ∀ r ∈ refs, valid n r := by
    intro r h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact i.isLt
  obtain ⟨gs, rs, hgood, hb, hsz, hlt, heval⟩ :=
    sweep C.gates (fun g hg => ⟨by simpa [allowed] using (hM g hg).1, (hM g hg).2⟩) refs n hr
  have hv (x : Fin n → Bool) : value (run gs (List.ofFn x)) (read rs C.output) =
      C.eval (List.ofFn x) := by
    have hinit : related refs (List.ofFn x) (List.ofFn x) := by
      refine ⟨?_, by simpa using hr⟩
      simp only [refs, List.map_ofFn]
      congr 1
      funext i
      simp [value, i.isLt]
    exact read_value (heval _ _ (by simp) hinit) C.output
  cases ho : read rs C.output with
  | inl b =>
    obtain ⟨x, y, hne⟩ := hnc
    exact (hne ((hv x).symm.trans ((congrArg (value (run gs (List.ofFn x))) ho).trans
      ((congrArg (value (run gs (List.ofFn y))) ho).symm.trans (hv y))))).elim
  | inr i =>
    refine ⟨⟨gs, i⟩, ⟨fun g hg => (hgood g hg).1, ?_, fun g hg => (hgood g hg).2⟩,
      hsz, hlt, ?_⟩
    · intro j hj k hk
      rw [gateAt_get hj] at hk
      exact hb j hj k hk
    · intro x
      rw [ho] at hv
      exact hv x

lemma ao_mono {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using h.1 g hg, by rw [h.2.2 g hg]⟩

lemma getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

def wireImp (w z : List Bool) : Prop :=
  ∀ i, w.getD i false = true → z.getD i false = true

lemma snoc_imp {w z : List Bool} {a b : Bool} (hlen : w.length = z.length)
    (hw : wireImp w z) (hab : a = true → b = true) : wireImp (w ++ [a]) (z ++ [b]) := by
  intro i
  rw [getD_snoc, getD_snoc, hlen]
  split_ifs
  · exact hw i
  · exact hab
  · exact id

def gateEval (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma gateEval_imp {w z : List Bool} {g : Gate} (hg : allowed g) (h : wireImp w z) :
    gateEval w g = true → gateEval z g = true := by
  rcases hg with hg | hg
  · simp only [gateEval, hg, GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun ha i hi => h i (ha i hi)
  · simp only [gateEval, hg, GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, h i hv⟩

lemma run_imp (gs : List Gate) (hgs : ∀ g ∈ gs, allowed g) {w z : List Bool}
    (hlen : w.length = z.length) (hw : wireImp w z) : wireImp (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact hw
  | cons g gs ih =>
    change wireImp (run gs (w ++ [gateEval w g])) (run gs (z ++ [gateEval z g]))
    apply ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (by simp [hlen])
    exact snoc_imp hlen hw (gateEval_imp (hgs g (by simp)) hw)

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def disable (C : Circuit) (j : ℕ) : Circuit := patch C j ⟨.or, []⟩

def before (C : Circuit) (j : ℕ) (x : List Bool) : List Bool := run (C.gates.take j) x

lemma patch_list (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate) :
    (patch C j g).gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
  simp [patch, List.set_eq_take_append_cons_drop, hj]

lemma patch_id (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    patch C j (gateAt C j) = C := by
  cases C with
  | mk gs out =>
    simp [patch, gateAt_get hj]

lemma patch_run (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate) (x : List Bool) :
    (patch C j g).wires x =
      run (C.gates.drop (j + 1)) (before C j x ++ [gateEval (before C j x) g]) := by
  change run (patch C j g).gates x = _
  rw [patch_list C j hj, run_append]
  rfl

-- Both circuits run the same gates before and after the replacement.
lemma patch_imp (C : Circuit) (hC : AndOrOnly C) (j : ℕ) (hj : j < C.gates.length)
    (a b : Gate) (x : List Bool)
    (h : gateEval (before C j x) a = true → gateEval (before C j x) b = true) :
    wireImp ((patch C j a).wires x) ((patch C j b).wires x) := by
  rw [patch_run C j hj, patch_run C j hj]
  apply run_imp _ (fun g hg => hC g (List.mem_of_mem_drop hg)) (by simp)
  exact snoc_imp rfl (fun _ => id) h

lemma patch_gateVal {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateEval (before C j (List.ofFn x)) g := by
  have hb : (before C j (List.ofFn x)).length = n + j := by
    simp [before, run_length, Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [patch_run C j hj, run_prefix _ _ _ (by simp [hb]), ← hb, getD_last]

lemma patch_gate_self (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  have h : j < (C.gates.set j g).length := by simpa using hj
  exact (gateAt_get h).trans (List.getElem_set_self h)

lemma patch_gate_other (C : Circuit) (j k : ℕ) (hk : k < C.gates.length) (hjk : j ≠ k) (g : Gate) :
    gateAt (patch C j g) k = gateAt C k := by
  have hp : k < (patch C j g).gates.length := by simpa [patch] using hk
  rw [gateAt_get hp, gateAt_get hk]
  exact List.getElem_set_ne hjk hp

lemma patch_ao {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (g : Gate)
    (hg : binaryGate g) (hb : ∀ i ∈ g.inputs, i < n + j) : IsAO2 n (patch C j g) := by
  have hgate (k : ℕ) (hk : k < (patch C j g).gates.length) :
      binaryGate (gateAt (patch C j g) k) := by
    have hk' : k < C.gates.length := by simpa [patch] using hk
    by_cases h : j = k
    · subst k
      exact (patch_gate_self C j hk' g).symm ▸ hg
    · rw [patch_gate_other C j k hk' h, gateAt_get hk']
      exact ⟨hC.1 _ (List.getElem_mem hk'), hC.2.2 _ (List.getElem_mem hk')⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    simpa only [gateAt_get hk, allowed] using (hgate k hk).1
  · intro k hk i hi
    by_cases h : j = k
    · subst k
      rw [patch_gate_self C j (by simpa [patch] using hk) g] at hi
      exact hb i hi
    · have hk' : k < C.gates.length := by simpa [patch] using hk
      rw [patch_gate_other C j k hk' h] at hi
      exact hC.2.1 k hk' i hi
  · intro a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    simpa only [gateAt_get hk] using (hgate k hk).2

lemma disable_mono {C : Circuit} (hC : Monotone2 C) (j : ℕ) : Monotone2 (disable C j) := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  change k < (C.gates.set j ⟨.or, []⟩).length at hk
  simp only [disable, patch, List.getElem_set]
  split_ifs
  · simp
  · exact hC _ (List.getElem_mem (by simpa using hk))

def hits {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def Computes {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ hits G x

lemma pair_bit {n : ℕ} {u v i : Fin n} : pairInput u v i = true ↔ i = u ∨ i = v := by
  simp [pairInput]

lemma edge_hits {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (h : G.Adj u v) :
    hits G (pairInput u v) :=
  ⟨u, v, h, pair_bit.mpr (Or.inl rfl), pair_bit.mpr (Or.inr rfl)⟩

lemma nonconstant {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hne : ∃ u v, G.Adj u v) (hc : Computes G C) :
    ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
  obtain ⟨u, v, huv⟩ := hne
  refine ⟨pairInput u v, fun _ => false, ?_⟩
  rw [(hc _).mpr (edge_hits huv)]
  intro h
  obtain ⟨_, _, _, hh, _⟩ := (hc _).mp h.symm
  cases hh

lemma computes_edges {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hm : Monotone2 C) (hupper : ∀ x, C.eval (List.ofFn x) = true → hits G x)
    (hedges : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true) : Computes G C := by
  intro x
  refine ⟨hupper x, ?_⟩
  rintro ⟨u, v, huv, hu, hv⟩
  apply run_imp C.gates (fun g hg => by simpa [allowed] using (hm g hg).1)
    (by simp) ?_ C.output (hedges u v huv)
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · intro h
    rcases pair_bit.mp h with h | h
    · rwa [h]
    · rwa [h]
  · exact id

def pivotal {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n) : Prop :=
  (disable C j).eval (List.ofFn (pairInput u v)) = false

lemma every_pivotal {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hne : ∃ u v, G.Adj u v) (hC : IsAO2 n C) (hc : Computes G C)
    (hmin : ∀ D, Monotone2 D → Computes G D → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) : ∃ u v, G.Adj u v ∧ pivotal C j u v := by
  classical
  by_contra h
  have hm := disable_mono (ao_mono hC) j
  have hd : Computes G (disable C j) := by
    apply computes_edges hm
    · intro x hx
      apply (hc x).mp
      have hi := patch_imp C hC.1 j hj ⟨.or, []⟩ (gateAt C j) (List.ofFn x)
        (fun h0 => by cases h0) C.output
      rw [patch_id C j hj] at hi
      exact hi hx
    · intro u v huv
      apply Bool.eq_true_of_not_eq_false
      exact fun hf => h ⟨u, v, huv, hf⟩
  obtain ⟨D, dao, _, hsm, hval⟩ := normalize (disable C j) hm (nonconstant hne hd)
  have hsmall := hsm (by
    refine ⟨⟨.or, []⟩, ?_, rfl⟩
    change (⟨.or, []⟩ : Gate) ∈ C.gates.set j ⟨.or, []⟩
    have hjs : j < (C.gates.set j (⟨.or, []⟩ : Gate)).length := by simpa using hj
    have hmem := List.getElem_mem hjs
    have hself := List.getElem_set_self hjs
    exact (congrArg (fun a : Gate => a ∈ C.gates.set j ⟨.or, []⟩) hself).mp hmem)
  have hle := hmin D (ao_mono dao) (fun x => (hval x ▸ hd x))
  have heq : (disable C j).size = C.size := by simp [disable, patch, Circuit.size]
  omega

def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨.and, [u.val, v.val]⟩

lemma edgeGate_val {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (u v : Fin n) (x : Fin n → Bool) :
    gateVal n (patch C j (edgeGate u v)) j x = (x u && x v) := by
  rw [patch_gateVal C j hj]
  have read_input (i : Fin n) : (before C j (List.ofFn x)).getD i.val false = x i := by
    change (run (C.gates.take j) (List.ofFn x)).getD i.val false = _
    rw [run_prefix _ _ _ (by simp), ofFn_getD, dite_eq_left i.isLt]
  simp [edgeGate, gateEval, GateOp.eval, read_input, -List.getD_eq_getElem?_getD]

lemma patch_wire_imp {n : ℕ} (C : Circuit) (hC : AndOrOnly C) (j : ℕ)
    (hj : j < C.gates.length) (a b : Gate) (x : Fin n → Bool)
    (h : gateVal n (patch C j a) j x = true → gateVal n (patch C j b) j x = true) :
    wireImp ((patch C j a).wires (List.ofFn x)) ((patch C j b).wires (List.ofFn x)) := by
  apply patch_imp C hC j hj
  simpa only [patch_gateVal C j hj] using h

lemma hits_pair {n : ℕ} {G : SimpleGraph (Fin n)} {a b : Fin n}
    (h : hits G (pairInput a b)) : G.Adj a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  rcases pair_bit.mp hu with rfl | rfl <;> rcases pair_bit.mp hv with rfl | rfl
  · exact (G.loopless.irrefl _ huv).elim
  · exact huv
  · exact huv.symm
  · exact (G.loopless.irrefl _ huv).elim

lemma pure_ao {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (j : ℕ) (u v : Fin n) :
    IsAO2 n (patch C j (edgeGate u v)) := by
  apply patch_ao hC _ (by simp [binaryGate, allowed, edgeGate])
  intro i hi
  simp [edgeGate] at hi
  rcases hi with rfl | rfl
  · exact Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
  · exact Nat.lt_of_lt_of_le v.isLt (Nat.le_add_right _ _)

lemma pure_computes {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : IsAO2 n C) (hc : Computes G C) (j : ℕ) (hj : j < C.gates.length)
    (u v : Fin n) (huv : G.Adj u v)
    (hsingle : ∀ a b, G.Adj a b → pivotal C j a b → s(a, b) = s(u, v)) :
    Computes G (patch C j (edgeGate u v)) := by
  apply computes_edges (ao_mono (pure_ao hC j u v))
  · intro x hx
    by_contra hmiss
    have hi := patch_wire_imp C hC.1 j hj (edgeGate u v) (gateAt C j) x (fun h => by
      rw [edgeGate_val C j hj, Bool.and_eq_true] at h
      exact (hmiss ⟨u, v, huv, h.1, h.2⟩).elim) C.output
    rw [patch_id C j hj] at hi
    exact hmiss ((hc x).mp (hi hx))
  · intro a b hab
    let x := pairInput a b
    by_cases hp : pivotal C j a b
    · have he : gateVal n (patch C j (edgeGate u v)) j x = true := by
        rw [edgeGate_val C j hj, Bool.and_eq_true]
        rcases Sym2.eq_iff.mp (hsingle a b hab hp) with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨pair_bit.mpr (Or.inl ha.symm), pair_bit.mpr (Or.inr hb.symm)⟩
        · exact ⟨pair_bit.mpr (Or.inr hb.symm), pair_bit.mpr (Or.inl ha.symm)⟩
      have hi := patch_wire_imp C hC.1 j hj (gateAt C j) (edgeGate u v) x (fun _ => he) C.output
      rw [patch_id C j hj] at hi
      exact hi ((hc x).mpr (edge_hits hab))
    · have hi := patch_imp C hC.1 j hj ⟨.or, []⟩ (edgeGate u v) (List.ofFn x)
        (fun h => by cases h) C.output
      exact hi (Bool.eq_true_of_not_eq_false hp)

def Leaks {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  ∃ a b, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true

noncomputable def leakyAnds {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and ∧ Leaks G C j

lemma mem_leakyAnds {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {j : ℕ} :
    j ∈ leakyAnds G C ↔ j < C.gates.length ∧ (gateAt C j).op = .and ∧ Leaks G C j := by
  classical
  unfold leakyAnds
  rw [Finset.mem_filter, Finset.mem_range]

lemma pure_no_leak {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {j : ℕ}
    (hj : j < C.gates.length) {u v : Fin n} (huv : G.Adj u v) {a b : Fin n} (hab : ¬ G.Adj a b) :
    gateVal n (patch C j (edgeGate u v)) j (pairInput a b) ≠ true := by
  intro h
  rw [edgeGate_val C j hj, Bool.and_eq_true] at h
  exact hab (hits_pair ⟨u, v, huv, h.1, h.2⟩)

-- The new gate stays false on nonedges, so no other gate can start leaking there.
lemma pure_fewer_leaks {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .and) (hl : Leaks G C j) {u v : Fin n} (huv : G.Adj u v) :
    (leakyAnds G (patch C j (edgeGate u v))).card < (leakyAnds G C).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    obtain ⟨hk', hkop, a, b, hab, hval⟩ := mem_leakyAnds.mp hk
    have hkc : k < C.gates.length := by simpa [patch] using hk'
    have hne : j ≠ k := by
      rintro rfl
      exact pure_no_leak hj huv hab hval
    refine mem_leakyAnds.mpr ⟨hkc, ?_, a, b, hab, ?_⟩
    · rwa [patch_gate_other C j k hkc hne (edgeGate u v)] at hkop
    · have hi := patch_wire_imp C hC.1 j hj (edgeGate u v) (gateAt C j) (pairInput a b)
        (fun h => (pure_no_leak hj huv hab h).elim) (n + k)
      rw [patch_id C j hj] at hi
      exact hi hval
  · intro heq
    have hm : j ∈ leakyAnds G C := mem_leakyAnds.mpr ⟨hj, hop, hl⟩
    rw [← heq] at hm
    obtain ⟨_, _, a, b, hab, hv⟩ := mem_leakyAnds.mp hm
    exact pure_no_leak hj huv hab hv

lemma solve (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (hne : ∃ u v, G.Adj u v) (hC : Monotone2 C) (hc : Computes G C) :
    ∃ D : Circuit, IsAO2 n D ∧ Monotone2 D ∧ D.size ≤ C.size ∧ Computes G D ∧
      (∀ B, Monotone2 B → Computes G B → D.size ≤ B.size) ∧
      (∀ j < D.gates.length, ∃ u v, G.Adj u v ∧ pivotal D j u v) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and → Leaks G D j →
        ∃ u v a b, G.Adj u v ∧ G.Adj a b ∧ s(u, v) ≠ s(a, b) ∧
          pivotal D j u v ∧ pivotal D j a b := by
  classical
  -- Minimize size first among all monotone circuits, then count leaking ANDs within that size.
  let feasible (k : ℕ) := ∃ B, Monotone2 B ∧ Computes G B ∧ B.size = k
  have hfeas : ∃ k, feasible k := ⟨C.size, C, hC, hc, rfl⟩
  let minimum := Nat.find hfeas
  obtain ⟨B, hm, hb, hbs⟩ : feasible minimum := Nat.find_spec hfeas
  have lower {A : Circuit} (ha : Monotone2 A) (he : Computes G A) : minimum ≤ A.size :=
    Nat.find_min' hfeas ⟨A, ha, he, rfl⟩
  obtain ⟨A, hao, hle, _, hval⟩ := normalize B hm (nonconstant hne hb)
  have ha : Computes G A := fun x => hval x ▸ hb x
  have has : A.size = minimum := Nat.le_antisymm (hle.trans_eq hbs) (lower (ao_mono hao) ha)
  let optimal (k : ℕ) := ∃ D : Circuit, IsAO2 n D ∧ Computes G D ∧ D.size = minimum ∧
    (leakyAnds G D).card = k
  have hex : ∃ k, optimal k := ⟨_, A, hao, ha, has, rfl⟩
  obtain ⟨D, hD, hd, hds, hjunk⟩ := Nat.find_spec hex
  have hmin : ∀ E, Monotone2 E → Computes G E → D.size ≤ E.size :=
    fun E hm he => hds ▸ lower hm he
  have hp := every_pivotal hne hD hd hmin
  refine ⟨D, hD, ao_mono hD, hmin C hC hc, hd, hmin, hp, ?_⟩
  intro j hj hop hl
  obtain ⟨u, v, huv, hpuv⟩ := hp j hj
  by_contra h
  have hsingle (a b : Fin n) (hab : G.Adj a b) (hpab : pivotal D j a b) :
      s(a, b) = s(u, v) := by
    by_contra hn
    exact h ⟨u, v, a, b, huv, hab, Ne.symm hn, hpuv, hpab⟩
  have hnew := pure_computes hD hd j hj u v huv hsingle
  have hlt := pure_fewer_leaks hD hj hop hl huv
  have hopt : optimal (leakyAnds G (patch D j (edgeGate u v))).card :=
    ⟨_, pure_ao hD j u v, hnew, by simpa [patch, Circuit.size] using hds, rfl⟩
  exact (Nat.not_lt_of_ge (Nat.find_min' hex hopt)) (hjunk ▸ hlt)

end PEqualNP.Outside.L_meta_8905

theorem PEqualNP.Outside.L_meta_8905 :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   have x4 : (Fin x1 → Bool) → Prop := fun (x4 : Fin x1 → Bool) => ∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true;   have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x1) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput x7 x8)) = Bool.false;   (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x8 : Fin x1 → Bool), x3.eval (List.ofFn x8) = Bool.true ↔ x4 x8) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x9 ∧ PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size ≤ x3.size ∧ (∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = Bool.true ↔ x4 x10) ∧ (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x12 : Fin x1 → Bool), x10.eval (List.ofFn x12) = Bool.true ↔ x4 x12) → x9.size ≤ x10.size) ∧ (∀ x10 < x9.gates.length, ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x5 x9 x10 x12 x13) ∧ ∀ x10 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ (x13 : Fin x1) (x14 : Fin x1), ¬x2.Adj x13 x14 ∧ PEqualNP.EdgeOwnership.gateVal x1 x9 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x14 : Fin x1) (x15 : Fin x1) (x16 : Fin x1) (x17 : Fin x1), x2.Adj x14 x15 ∧ x2.Adj x16 x17 ∧ s(x14, x15) ≠ s(x16, x17) ∧ x5 x9 x10 x14 x15 ∧ x5 x9 x10 x16 x17 := by
  exact PEqualNP.Outside.L_meta_8905.solve

