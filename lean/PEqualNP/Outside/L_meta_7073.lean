import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7073

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def width (op : GateOp) : ℕ := if op.eval [true] = true then 2 else 1

def touched (s : ℕ) (g : Gate) : Bool :=
  (g.inputs.take (width g.op)).contains s || (g.inputs.take (width g.op)).contains 10

def binary (op : GateOp) (neutral : Bool) (n : ℕ) (a b : Ref) : Ref × List Gate :=
  match a, b with
  | .inl c, _ => (if c = neutral then b else .inl c, [])
  | _, .inl c => (if c = neutral then a else .inl c, [])
  | .inr i, .inr j => (.inr n, [⟨op, [i, j]⟩])

def emit (op : GateOp) (n : ℕ) (rs : List Ref) : Ref × List Gate :=
  match op, rs with
  | .not, [] => (.inl true, [])
  | .not, .inl b :: _ => (.inl (!b), [])
  | .not, .inr i :: _ => (.inr n, [⟨.not, [i]⟩])
  | .and, [] => (.inl true, [])
  | .or, [] => (.inl false, [])
  | .and, [a] | .or, [a] => (a, [])
  | .and, a :: b :: _ => binary .and true n a b
  | .or, a :: b :: _ => binary .or false n a b
  | _, _ => (fixed, [])

lemma emit_ok (op : GateOp) (n : ℕ) (rs : List Ref)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hl : rs.length ≤ 2) :
    let e := emit op n rs
    e.2.length ≤ 1 ∧ (∀ g ∈ e.2, good g) ∧
      (∀ b : Bool, Sum.inl b ∈ rs.take (width op) → e.2 = []) ∧
      ∀ w : List Bool, w.length = n → (∀ r ∈ rs, valid n r) →
        valid (run e.2 w).length e.1 ∧
          value (run e.2 w) e.1 = op.eval (rs.map (value w)) := by
  dsimp only
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [emit, valid, value, GateOp.eval]
  · rcases hop with rfl | rfl | rfl
    · simp [emit, run, GateOp.eval]
      intro w hw
      simp [hw]
    · simp [emit, run, GateOp.eval]
      intro w hw
      simp [hw]
    · rcases a with a | a
      · simp [emit, valid, value, GateOp.eval]
      · simp [emit, width, run, step, good, valid, value, GateOp.eval, -List.getD_eq_getElem?_getD]
        intro w hw
        simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
  · rcases hop with rfl | rfl | rfl
    · rcases a with (a | a) <;> rcases b with (b | b) <;>
        (try cases (show Bool from a)) <;> (try cases (show Bool from b)) <;>
        simp [emit, binary, width, run, step, good, valid, value, GateOp.eval,
          -List.getD_eq_getElem?_getD] <;>
        intro w hw <;> simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
    · rcases a with (a | a) <;> rcases b with (b | b) <;>
        (try cases (show Bool from a)) <;> (try cases (show Bool from b)) <;>
        simp [emit, binary, width, run, step, good, valid, value, GateOp.eval,
          -List.getD_eq_getElem?_getD] <;>
        intro w hw <;> simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
    · rcases a with a | a
      · simp [emit, valid, value, GateOp.eval]
      · simp [emit, width, run, step, good, valid, value, GateOp.eval, -List.getD_eq_getElem?_getD]
        intro w hw
        simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
  · simp at hl

def read (refs : List Ref) (i : ℕ) : Ref := refs.getD i fixed

-- The reference table recovers every original wire and only points to available new wires.
def related (refs : List Ref) (w old : List Bool) : Prop :=
  old = refs.map (value w) ∧ ∀ r ∈ refs, valid w.length r

lemma read_value {refs : List Ref} {w old : List Bool} (h : related refs w old) (i : ℕ) :
    value w (read refs i) = old.getD i false := by
  rw [h.1]
  exact (List.getD_map refs fixed (value w)).symm

lemma read_valid {refs : List Ref} {w old : List Bool} (h : related refs w old) (i : ℕ) :
    valid w.length (read refs i) := by
  by_cases hi : i < refs.length
  · rw [read, List.getD_eq_getElem _ _ hi]
    exact h.2 _ (List.getElem_mem _)
  · rw [read, List.getD_eq_default _ _ (by omega)]
    trivial

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

lemma sweep (s : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, good g) (refs : List Ref) (n : ℕ)
    (hs : s < refs.length) (ht : 10 < refs.length)
    (hfs : read refs s = fixed) (hft : read refs 10 = fixed) :
    ∃ (out : List Gate) (outRefs : List Ref),
      (∀ g ∈ out, good g) ∧ out.length + (gs.filter (touched s)).length ≤ gs.length ∧
      ∀ w old, w.length = n → related refs w old →
        related outRefs (run out w) (run gs old) := by
  induction gs generalizing refs n with
  | nil => exact ⟨[], refs, by simp, by simp, fun _ _ _ h => h⟩
  | cons g gs ih =>
    have hg' := hg g (by simp)
    let rs := g.inputs.map (read refs)
    let e := emit g.op n rs
    have he : e.2.length ≤ 1 ∧ (∀ g ∈ e.2, good g) ∧
        (∀ b : Bool, Sum.inl b ∈ rs.take (width g.op) → e.2 = []) ∧
        ∀ w : List Bool, w.length = n → (∀ r ∈ rs, valid n r) →
          valid (run e.2 w).length e.1 ∧
            value (run e.2 w) e.1 = g.op.eval (rs.map (value w)) :=
      emit_ok _ _ _ (by simpa [Set.mem_insert_iff] using hg'.1) (by simpa [rs] using hg'.2)
    let nextRefs := refs ++ [e.1]
    obtain ⟨tail, outRefs, htail, hsize, hcorrect⟩ :=
      ih (fun g hg₀ => hg g (by simp [hg₀])) nextRefs (n + e.2.length)
        (by simp [nextRefs]; omega) (by simp [nextRefs]; omega)
        ((List.getD_append _ _ _ _ hs).trans hfs)
        ((List.getD_append _ _ _ _ ht).trans hft)
    refine ⟨e.2 ++ tail, outRefs, ?_, ?_, ?_⟩
    · intro g hg
      exact (List.mem_append.mp hg).elim (he.2.1 g) (htail g)
    · have hone := he.1
      cases hc : touched s g
      · simp only [List.length_append, List.filter_cons, hc, Bool.false_eq_true, ite_false,
          List.length_cons]
        omega
      · have hm : s ∈ g.inputs.take (width g.op) ∨ 10 ∈ g.inputs.take (width g.op) := by
          simpa [touched] using hc
        have hf : fixed ∈ rs.take (width g.op) := by
          dsimp only [rs]
          rw [← List.map_take, List.mem_map]
          exact hm.elim (fun h => ⟨s, h, hfs⟩) (fun h => ⟨10, h, hft⟩)
        have hz := he.2.2.1 false hf
        simp [hz, hc]
        omega
    · intro w old hw hr
      have hv : ∀ r ∈ rs, valid n r := by
        intro r hr'
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr'
        rw [← hw]
        exact read_valid hr i
      obtain ⟨hv', he'⟩ := he.2.2.2 w hw hv
      have hm : rs.map (value w) = g.inputs.map (fun i => old.getD i false) := by
        dsimp only [rs]
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => read_value hr i)
      rw [hm] at he'
      rw [run_append]
      change related outRefs (run tail (run e.2 w)) (run gs (step old g))
      exact hcorrect _ _ (by rw [run_length, hw]) (related_extend hr _ _ _ hv' he')

def edges10 : List ℕ := [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85]

def edges9 : List ℕ := [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85]

def graph {n : ℕ} [NeZero n] (es : List ℕ) (y : Fin n → Bool) : Bool :=
  es.any fun e => y (Fin.ofNat n (e / 10)) && y (Fin.ofNat n (e % 10))

-- Each row relabels the Petersen graph and sends its deleted vertex to 9.
def label (s : ℕ) (i : Fin 10) : ℕ :=
  let rows : List (List ℕ) :=
    [[9, 6, 8, 5, 7, 4, 1, 3, 0, 2], [7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
      [5, 7, 9, 6, 8, 0, 2, 4, 1, 3]]
  (rows.getD s []).getD i.val 9

def selected (y : Fin 9 → Bool) (k : ℕ) : Bool := if k = 9 then false else y (Fin.ofNat 9 k)

def extend (s : ℕ) (y : Fin 9 → Bool) (i : Fin 10) : Bool := selected y (label s i)

def labelRef (s : ℕ) (i : Fin 10) : Ref :=
  if label s i = 9 then fixed else .inr (label s i % 9)

def seed (s : ℕ) : List Ref := List.ofFn (labelRef s) ++ [fixed]

def canon (a b : ℕ) : ℕ × ℕ := if a ≤ b then (a, b) else (b, a)

def score (f : ℕ → Bool) (p : ℕ × ℕ) : Bool := f p.1 && f p.2

lemma score_canon (f : ℕ → Bool) (a b : ℕ) :
    score f (canon a b) = (f a && f b) := by
  unfold canon
  split <;> simp [score, Bool.and_comm]

def mappedEdges (s : ℕ) : List (ℕ × ℕ) :=
  edges10.map fun e => canon (label s (Fin.ofNat 10 (e / 10))) (label s (Fin.ofNat 10 (e % 10)))

def liveEdge (p : ℕ × ℕ) : Bool := (p.1 != 9) && (p.2 != 9)

lemma edge_perm (s : Fin 3) :
    ((mappedEdges s.val).filter liveEdge).Perm (edges9.map fun e => canon (e / 10) (e % 10)) := by
  revert s
  decide

lemma graph_extend (s : ℕ) (hs : s < 3) (y : Fin 9 → Bool) :
    graph edges10 (extend s y) = graph edges9 y := by
  calc
    graph edges10 (extend s y) = (mappedEdges s).any (score (selected y)) := by
      rw [mappedEdges, List.any_map]
      apply congrArg (List.any edges10)
      funext e
      exact (score_canon _ _ _).symm
    _ = ((mappedEdges s).filter liveEdge).any (score (selected y)) := by
      rw [List.any_filter]
      apply congrArg (List.any (mappedEdges s))
      funext p
      rcases p with ⟨a, b⟩
      by_cases ha : a = 9 <;> by_cases hb : b = 9 <;> simp [liveEdge, score, selected, ha, hb]
    _ = (edges9.map fun e => canon (e / 10) (e % 10)).any (score (selected y)) :=
      (edge_perm ⟨s, hs⟩).any_eq
    _ = graph edges9 y := by
      rw [List.any_map]
      change (edges9.any fun e => score (selected y) (canon (e / 10) (e % 10))) = _
      simp only [score_canon]
      simp [edges9, graph, selected, List.any]

lemma label_fixed (s : Fin 3) : label s.val (Fin.ofNat 10 s.val) = 9 := by
  revert s
  decide

lemma seed_fixed (s : Fin 3) : read (seed s.val) s.val = fixed := by
  revert s
  decide

lemma seed_related (s : ℕ) (y : Fin 9 → Bool) :
    related (seed s) (List.ofFn y) (List.ofFn (extend s y) ++ [false]) := by
  constructor
  · rw [seed, List.map_append, List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    by_cases hi : label s i = 9
    · simp [extend, selected, labelRef, hi, value, fixed]
    · simp only [Function.comp_apply, extend, selected, labelRef, hi, ite_false, value]
      have hidx : label s i % 9 < (List.ofFn y).length := by
        simpa only [List.length_ofFn] using Nat.mod_lt (label s i) (by decide : 0 < 9)
      rw [List.getD_eq_getElem _ _ hidx]
      simp only [List.getElem_ofFn, Fin.ofNat]
  · intro r hr
    rw [seed, List.mem_append, List.mem_ofFn] at hr
    rcases hr with ⟨i, rfl⟩ | hr
    · simp only [labelRef]
      split <;> simp [fixed, valid]
      omega
    · obtain rfl := List.mem_singleton.mp hr
      trivial

lemma finish (out : List Gate) (r : Ref) (hgood : ∀ g ∈ out, good g) (hsize : out.length ≤ 15)
    (he : ∀ y : Fin 9 → Bool, value (run out (List.ofFn y)) r = graph edges9 y) :
    HasCircuitSize 9 (graph edges9) 15 := by
  rcases r with b | i
  · have h₀ := he (fun _ => false)
    have h₁ := he (fun _ => true)
    change b = false at h₀
    change b = true at h₁
    rw [h₀] at h₁
    contradiction
  · exact ⟨⟨out, i⟩, hgood, hsize, he⟩

lemma main (b : Bool) (C : Circuit) (u v s : ℕ) (hfan : FanInTwo C) (hsize : C.size ≤ 17)
    (hs : s = 0 ∨ s = if b = true then 1 else 2)
    (ht : 3 ≤ (C.gates.filter (touched s)).length)
    (he : ∀ x : Fin 10 → Bool,
      ((C.wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD u false &&
       (C.wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD v false) =
        graph edges10 x) :
    HasCircuitSize 9 (graph edges9) 15 := by
  have hs3 : s < 3 := by cases b <;> simp at hs <;> omega
  have hseed : (seed s).length = 11 := by simp [seed]
  have hx (y : Fin 9 → Bool) : (extend s y 0 && (if b = true then extend s y 1 else extend s y 2)) = false := by
    have hlabel : label s (Fin.ofNat 10 s) = 9 := label_fixed ⟨s, hs3⟩
    have hf : extend s y (Fin.ofNat 10 s) = false := by
      rw [extend, selected, hlabel]
      rfl
    rcases hs with rfl | hs
    · simp [show extend 0 y 0 = false from hf]
    · cases b
      · change s = 2 at hs
        subst s
        simp [show extend 2 y 2 = false from hf]
      · change s = 1 at hs
        subst s
        simp [show extend 1 y 1 = false from hf]
  obtain ⟨out, refs, ho, hsz, hcorr⟩ :=
    sweep s C.gates hfan (seed s) 9 (by omega) (by omega) (seed_fixed ⟨s, hs3⟩) (by
      simpa only [read, seed, List.length_ofFn] using getD_last (List.ofFn (labelRef s)) fixed fixed)
  have hc : ∀ y : Fin 9 → Bool,
      related refs (run out (List.ofFn y)) (C.wires (List.ofFn (extend s y) ++ [false])) :=
    fun y => hcorr _ _ (by simp) (seed_related s y)
  let e := emit .and (9 + out.length) [read refs u, read refs v]
  have he' := emit_ok GateOp.and (9 + out.length) [read refs u, read refs v]
    (Or.inl rfl) (by simp)
  change e.2.length ≤ 1 ∧ _ at he'
  apply finish (out ++ e.2) e.1
  · intro g hg
    exact (List.mem_append.mp hg).elim (ho g) (he'.2.1 g)
  · change C.gates.length ≤ 17 at hsize
    have := he'.1
    simp only [List.length_append]
    omega
  · intro y
    have hw : (run out (List.ofFn y)).length = 9 + out.length := by simp [run_length]
    have hv : ∀ r ∈ [read refs u, read refs v], valid (9 + out.length) r := by
      rw [← hw]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact read_valid (hc y) u
      · exact read_valid (hc y) v
    have hh := (he'.2.2.2 _ hw hv).2
    have hyp := he (extend s y)
    rw [hx y, graph_extend s hs3 y] at hyp
    rw [run_append, hh]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, read_value (hc y)]
    exact hyp

end PEqualNP.Outside.L_meta_7073

theorem PEqualNP.Outside.L_meta_7073 :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (17 : ℕ) → (x5 = (0 : ℕ) ∨ x5 = if x1 = Bool.true then (1 : ℕ) else (2 : ℕ)) → (3 : ℕ) ≤ (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (if x9.op.eval [Bool.true] = Bool.true then (2 : ℕ) else (1 : ℕ)) x9.inputs).contains x5 || (List.take (if x9.op.eval [Bool.true] = Bool.true then (2 : ℕ) else (1 : ℕ)) x9.inputs).contains (10 : ℕ)) x2.gates).length → (∀ (x10 : Fin (10 : ℕ) → Bool), ((x2.wires (List.ofFn x10 ++ [x10 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x10 (1 : Fin (10 : ℕ)) else x10 (2 : Fin (10 : ℕ))])).getD x3 Bool.false && (x2.wires (List.ofFn x10 ++ [x10 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x10 (1 : Fin (10 : ℕ)) else x10 (2 : Fin (10 : ℕ))])).getD x4 Bool.false) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (10 : ℕ) (x11 / (10 : ℕ))) && x10 (Fin.ofNat (10 : ℕ) (x11 % (10 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x11 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) (15 : ℕ) := by
  exact PEqualNP.Outside.L_meta_7073.main
