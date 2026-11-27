import PEqualNP.Defs.MetaComplexityMinimal
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The cover circuit, explicit, from an edge list and a cover list

For a graph given as a list of edges `(u, v)` and a vertex cover given as a list, an explicit
circuit for the edge function `q(x) = OR over listed edges (u, v) of (x u AND x v)`.

ASSIGNMENT RULE. Each edge is assigned to the FIRST entry of the cover list that is one of its
ends. Edges with no end in the cover list are assigned to nobody (and dropped). The pass runs over
the cover list keeping the edges not yet assigned: at entry `c`, the remaining edges with an end
`c` are assigned to `c`, and the other end of each, in edge-list order, is a neighbour of `c`.

GATE ORDER (one pass). For each cover entry `c` with at least one assigned edge, in cover-list
order: an OR chain over its neighbour inputs (one gate fewer than neighbours), then one AND gate
reading input `c` and the end of that chain. A cover entry with no assigned edge (for example a
repeated entry) emits no gate. Then an OR chain over the AND gates. The output is the end of the
last chain. With no edge assigned at all there are no gates and the output is wire `n`, which does
not exist and reads `false`.

WIRES. A block that starts when `s` gates exist has its gates at wires `n + s`, `n + s + 1`, and
so on; with `d` neighbours its AND gate is at wire `n + s + d - 1`. The final chain starts at wire
`n + (number of block gates)`.
-/

namespace PEqualNP.MetaComplexity.CoverCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- `c` is an end of the edge `e`. -/
def isEnd (c : ℕ) (e : ℕ × ℕ) : Bool := e.1 == c || e.2 == c

/-- The end of `e` other than `c` (the first end if `c` is not the first end). -/
def other (c : ℕ) (e : ℕ × ℕ) : ℕ := if e.1 = c then e.2 else e.1

/-- Each cover entry, in order, with the list of its assigned neighbours: one pass over the
cover list carrying the edges not yet assigned. -/
def assign (edges : List (ℕ × ℕ)) (cover : List ℕ) : List (ℕ × List ℕ) :=
  (cover.foldl
    (fun st c => (st.1.filter (fun e => !isEnd c e),
      st.2 ++ [(c, (st.1.filter (isEnd c)).map (other c))]))
    (edges, [])).2

/-- The cover entries with at least one assigned neighbour. -/
def blocks (edges : List (ℕ × ℕ)) (cover : List ℕ) : List (ℕ × List ℕ) :=
  (assign edges cover).filter (fun b => decide (0 < b.2.length))

/-- An OR chain whose first gate is at wire `start`: gate `j` reads the previous gate (for
`j = 0`, the wire `first`) and the wire `rest[j]`. One gate per entry of `rest`. -/
def orChain (start first : ℕ) (rest : List ℕ) : List Gate :=
  rest.foldl
    (fun gs v => gs ++ [⟨GateOp.or, [if gs.length = 0 then first else start + gs.length - 1, v]⟩])
    []

/-- The wire at the end of `orChain start first rest`. -/
def chainOut (start first : ℕ) (rest : List ℕ) : ℕ :=
  if rest.length = 0 then first else start + rest.length - 1

/-- The gates of one block `(c, N)` starting at wire `start`: the OR chain over `N`, then the
AND of input `c` with the end of that chain. -/
def blockGates (start : ℕ) (b : ℕ × List ℕ) : List Gate :=
  orChain start (b.2.headD 0) b.2.tail ++
    [⟨GateOp.and, [b.1, chainOut start (b.2.headD 0) b.2.tail]⟩]

/-- All block gates, and the list of the wires of the AND gates. -/
def blockPass (n : ℕ) (bs : List (ℕ × List ℕ)) : List Gate × List ℕ :=
  bs.foldl
    (fun st b => (st.1 ++ blockGates (n + st.1.length) b, st.2 ++ [n + st.1.length + b.2.length - 1]))
    ([], [])

/-- The cover circuit on `n` inputs for the edge list `edges` and the cover list `cover`. -/
def coverCircuit (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) : Circuit :=
  let bp := blockPass n (blocks edges cover)
  let w := n + bp.1.length
  ⟨bp.1 ++ orChain w (bp.2.headD w) bp.2.tail, chainOut w (bp.2.headD w) bp.2.tail⟩

/-! ## Evaluation of a gate list -/

/-- The wires after running the gates `gs` on the wire list `w`. -/
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem any_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (v : ℕ) (h : v < n) :
    (List.ofFn x).getD v false = x ⟨v, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## The OR chain -/

theorem orChain_snoc_aux (s f : ℕ) (r : List ℕ) (v : ℕ) :
    orChain s f (r ++ [v]) = orChain s f r ++
      [⟨GateOp.or, [if (orChain s f r).length = 0 then f else s + (orChain s f r).length - 1, v]⟩] := by
  unfold orChain; rw [List.foldl_append]; rfl

theorem orChain_length (s f : ℕ) (r : List ℕ) : (orChain s f r).length = r.length := by
  induction r using List.reverseRecOn with
  | nil => rfl
  | append_singleton r v ih => rw [orChain_snoc_aux]; simp [ih]

theorem orChain_snoc (s f : ℕ) (r : List ℕ) (v : ℕ) :
    orChain s f (r ++ [v]) = orChain s f r ++ [⟨GateOp.or, [chainOut s f r, v]⟩] := by
  rw [orChain_snoc_aux, orChain_length]; rfl

theorem orChain_ops (s f : ℕ) (r : List ℕ) :
    ∀ g ∈ orChain s f r, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction r using List.reverseRecOn with
  | nil => intro g hg; simp [orChain] at hg
  | append_singleton r v ih =>
    intro g hg
    rw [orChain_snoc, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih g hg
    · exact ⟨rfl, rfl⟩

theorem chainOut_lt (s f : ℕ) (r : List ℕ) (hf : f < s) : chainOut s f r < s + r.length := by
  unfold chainOut; split <;> omega

theorem orChain_eval (s f : ℕ) (r : List ℕ) (w : List Bool) (hw : w.length = s) (hf : f < s)
    (hr : ∀ v ∈ r, v < s) :
    (run (orChain s f r) w).getD (chainOut s f r) false =
      (w.getD f false || r.any (fun v => w.getD v false)) := by
  induction r using List.reverseRecOn with
  | nil => simp [orChain, run_nil, chainOut]
  | append_singleton r v ih =>
    have hr' : ∀ u ∈ r, u < s := fun u hu => hr u (List.mem_append_left _ hu)
    have hv : v < s := hr v (by simp)
    rw [orChain_snoc, run_append, run_singleton]
    have hlen : (run (orChain s f r) w).length = s + r.length := by
      rw [run_length, orChain_length, hw]
    have hco : chainOut s f (r ++ [v]) = (run (orChain s f r) w).length := by
      rw [hlen]; simp [chainOut]
    rw [hco, getD_snoc_length]
    have hv' : (run (orChain s f r) w).getD v false = w.getD v false :=
      getD_run _ _ _ (by omega)
    simp only [List.map_cons, List.map_nil, eval_or2]
    rw [ih hr', hv', List.any_append]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

/-! ## One block -/

theorem blockGates_length (s : ℕ) (b : ℕ × List ℕ) :
    (blockGates s b).length = b.2.tail.length + 1 := by
  simp [blockGates, orChain_length]

theorem blockGates_ops (s : ℕ) (b : ℕ × List ℕ) :
    ∀ g ∈ blockGates s b, (g.op = GateOp.or ∨ g.op = GateOp.and) ∧ g.inputs.length = 2 := by
  intro g hg
  unfold blockGates at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨h1, h2⟩ := orChain_ops _ _ _ g hg
    exact ⟨Or.inl h1, h2⟩
  · exact ⟨Or.inr rfl, rfl⟩

theorem blockGates_eval (s c h : ℕ) (t : List ℕ) (w : List Bool) (hw : w.length = s)
    (hc : c < s) (hh : h < s) (ht : ∀ v ∈ t, v < s) :
    (run (blockGates s (c, h :: t)) w).getD (s + t.length) false =
      (w.getD c false && (w.getD h false || t.any (fun v => w.getD v false))) := by
  unfold blockGates
  simp only [List.headD_cons, List.tail_cons]
  rw [run_append, run_singleton]
  have hlen : (run (orChain s h t) w).length = s + t.length := by
    rw [run_length, orChain_length, hw]
  rw [← hlen, getD_snoc_length]
  have hc' : (run (orChain s h t) w).getD c false = w.getD c false := getD_run _ _ _ (by omega)
  simp only [List.map_cons, List.map_nil, eval_and2]
  rw [hc', orChain_eval s h t w hw hh ht]

/-! ## The block pass -/

/-- The step of `blockPass`. -/
def passStep (n : ℕ) (st : List Gate × List ℕ) (b : ℕ × List ℕ) : List Gate × List ℕ :=
  (st.1 ++ blockGates (n + st.1.length) b, st.2 ++ [n + st.1.length + b.2.length - 1])

theorem blockPass_eq (n : ℕ) (bs : List (ℕ × List ℕ)) :
    blockPass n bs = bs.foldl (passStep n) ([], []) := rfl

/-- The value of a block on the wire list `w`. -/
def blockVal (w : List Bool) (b : ℕ × List ℕ) : Bool :=
  w.getD b.1 false && b.2.any (fun v => w.getD v false)

theorem pass_len (n : ℕ) : ∀ (bs : List (ℕ × List ℕ)) (st : List Gate × List ℕ),
    (bs.foldl (passStep n) st).1.length = st.1.length + (bs.map (fun b => b.2.tail.length + 1)).sum ∧
    (bs.foldl (passStep n) st).2.length = st.2.length + bs.length := by
  intro bs
  induction bs with
  | nil => intro st; simp
  | cons b bs ih =>
    intro st
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (passStep n st b)
    rw [h1, h2]
    simp [passStep, blockGates_length]
    omega

theorem pass_ops (n : ℕ) : ∀ (bs : List (ℕ × List ℕ)) (st : List Gate × List ℕ),
    (∀ g ∈ st.1, (g.op = GateOp.or ∨ g.op = GateOp.and) ∧ g.inputs.length = 2) →
    ∀ g ∈ (bs.foldl (passStep n) st).1, (g.op = GateOp.or ∨ g.op = GateOp.and) ∧ g.inputs.length = 2 := by
  intro bs
  induction bs with
  | nil => intro st h; simpa using h
  | cons b bs ih =>
    intro st h
    rw [List.foldl_cons]
    apply ih
    intro g hg
    simp only [passStep, List.mem_append] at hg
    rcases hg with hg | hg
    · exact h g hg
    · exact blockGates_ops _ _ g hg

theorem pass_eval (n : ℕ) (w0 : List Bool) (hw : w0.length = n) :
    ∀ (bs : List (ℕ × List ℕ)) (gs : List Gate) (as : List ℕ) (L : List Bool),
    (∀ b ∈ bs, 0 < b.2.length ∧ b.1 < n ∧ ∀ v ∈ b.2, v < n) →
    (∀ a ∈ as, a < n + gs.length) →
    as.map (fun a => (run gs w0).getD a false) = L →
    (∀ a ∈ (bs.foldl (passStep n) (gs, as)).2, a < n + (bs.foldl (passStep n) (gs, as)).1.length) ∧
    (bs.foldl (passStep n) (gs, as)).2.map
      (fun a => (run (bs.foldl (passStep n) (gs, as)).1 w0).getD a false) = L ++ bs.map (blockVal w0) := by
  intro bs
  induction bs with
  | nil =>
    intro gs as L _ h2 h3
    simp only [List.foldl_nil, List.map_nil, List.append_nil]
    exact ⟨h2, h3⟩
  | cons b bs ih =>
    intro gs as L hb h2 h3
    obtain ⟨hpos, hc, hv⟩ := hb b (by simp)
    obtain ⟨c, N⟩ := b
    obtain ⟨h, t⟩ | ⟨h, t⟩ := N
    · simp at hpos
    rw [List.foldl_cons]
    have hlen : (run gs w0).length = n + gs.length := by rw [run_length, hw]
    have key := ih (gs ++ blockGates (n + gs.length) (c, h :: t))
      (as ++ [n + gs.length + (h :: t).length - 1]) (L ++ [blockVal w0 (c, h :: t)])
      (fun b' hb' => hb b' (by simp [hb']))
      (by
        intro a ha
        rw [List.length_append, blockGates_length]
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · have := h2 a ha; omega
        · simp only [List.length_cons, List.tail_cons]; omega)
      (by
        rw [List.map_append, run_append]
        congr 1
        · rw [← h3]
          apply List.map_congr_left
          intro a ha
          exact getD_run _ _ _ (by rw [hlen]; exact h2 a ha)
        · simp only [List.map_cons, List.map_nil, List.length_cons]
          have e : n + gs.length + (t.length + 1) - 1 = n + gs.length + t.length := by omega
          rw [e]
          have hh : h < n := hv h (by simp)
          have ht : ∀ v ∈ t, v < n := fun v hvt => hv v (by simp [hvt])
          rw [blockGates_eval (n + gs.length) c h t (run gs w0) hlen (by omega) (by omega)
            (fun v hvt => by have := ht v hvt; omega)]
          have g1 : ∀ v, v < n → (run gs w0).getD v false = w0.getD v false :=
            fun v hvn => getD_run _ _ _ (by omega)
          simp only [blockVal, List.any_cons]
          rw [g1 c hc, g1 h hh]
          rw [any_congr_mem t _ (fun v => w0.getD v false) (fun v hvt => g1 v (ht v hvt))])
    simpa [passStep, List.append_assoc] using key

/-! ## The whole circuit, in terms of its blocks -/

theorem blocks_pos (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    ∀ b ∈ blocks edges cover, 0 < b.2.length := by
  intro b hb
  unfold blocks at hb
  rw [List.mem_filter] at hb
  simpa using hb.2

theorem gates_ops (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    ∀ g ∈ (coverCircuit n edges cover).gates,
      (g.op = GateOp.or ∨ g.op = GateOp.and) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [coverCircuit, List.mem_append] at hg
  rcases hg with hg | hg
  · rw [blockPass_eq] at hg
    exact pass_ops n _ ([], []) (by simp) g hg
  · obtain ⟨h1, h2⟩ := orChain_ops _ _ _ g hg
    exact ⟨Or.inl h1, h2⟩

theorem circuitFun_blocks (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) (x : Fin n → Bool)
    (hb : ∀ b ∈ blocks edges cover, 0 < b.2.length ∧ b.1 < n ∧ ∀ v ∈ b.2, v < n) :
    circuitFun n (coverCircuit n edges cover) x =
      (blocks edges cover).any (blockVal (List.ofFn x)) := by
  have hw : (List.ofFn x).length = n := List.length_ofFn
  obtain ⟨hlt, hmap⟩ :=
    pass_eval n (List.ofFn x) hw (blocks edges cover) [] [] [] hb (by simp) (by simp)
  rw [← blockPass_eq] at hlt hmap
  simp only [List.nil_append] at hmap
  unfold circuitFun Circuit.eval coverCircuit
  simp only [wires_eq]
  generalize blockPass n (blocks edges cover) = bp at hlt hmap ⊢
  obtain ⟨gs, as⟩ := bp
  simp only at hlt hmap ⊢
  rw [run_append]
  have hlen : (run gs (List.ofFn x)).length = n + gs.length := by rw [run_length, hw]
  cases as with
  | nil =>
    simp only [List.map_nil] at hmap
    have h0 : blocks edges cover = [] := List.map_eq_nil_iff.mp hmap.symm
    rw [h0]
    simp only [List.headD_nil, List.tail_nil]
    rw [show orChain (n + gs.length) (n + gs.length) [] = [] from rfl, run_nil,
      show chainOut (n + gs.length) (n + gs.length) [] = n + gs.length from rfl,
      List.getD_eq_default _ _ (by omega)]
    rfl
  | cons a as =>
    simp only [List.headD_cons, List.tail_cons]
    rw [orChain_eval (n + gs.length) a as _ hlen (hlt a (by simp))
      (fun v hv => hlt v (by simp [hv]))]
    have := congrArg (fun l => l.any id) hmap
    simp only [List.map_cons, List.any_cons, List.any_map] at this
    exact this

theorem size_nil (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) (h : blocks edges cover = []) :
    (coverCircuit n edges cover).size = 0 := by
  unfold Circuit.size coverCircuit
  simp only [h, blockPass_eq, List.foldl_nil, List.nil_append]
  rfl

theorem size_blocks (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) (hne : blocks edges cover ≠ []) :
    (coverCircuit n edges cover).size + 1 =
      ((blocks edges cover).map (fun b => b.2.length)).sum + (blocks edges cover).length := by
  have h := pass_len n (blocks edges cover) ([], [])
  rw [← blockPass_eq] at h
  simp only [List.length_nil, zero_add] at h
  unfold Circuit.size coverCircuit
  simp only [List.length_append, orChain_length, List.length_tail, h.1, h.2]
  have hs : ((blocks edges cover).map (fun b => b.2.tail.length + 1)).sum =
      ((blocks edges cover).map (fun b => b.2.length)).sum := by
    congr 1
    apply List.map_congr_left
    intro b hb
    have := blocks_pos edges cover b hb
    simp only [List.length_tail]
    omega
  simp only [List.length_tail] at hs
  rw [hs]
  have : 0 < (blocks edges cover).length := List.length_pos_iff.mpr hne
  omega

/-! ## The assignment pass -/

/-- The step of `assign`. -/
def assignStep (st : List (ℕ × ℕ) × List (ℕ × List ℕ)) (c : ℕ) :
    List (ℕ × ℕ) × List (ℕ × List ℕ) :=
  (st.1.filter (fun e => !isEnd c e), st.2 ++ [(c, (st.1.filter (isEnd c)).map (other c))])

theorem assign_eq (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    assign edges cover = (cover.foldl assignStep (edges, [])).2 := rfl

theorem isEnd_iff (c : ℕ) (e : ℕ × ℕ) : isEnd c e = true ↔ e.1 = c ∨ e.2 = c := by
  simp [isEnd]

theorem other_lt (c : ℕ) (e : ℕ × ℕ) (n : ℕ) (h1 : e.1 < n) (h2 : e.2 < n) : other c e < n := by
  unfold other; split <;> assumption

theorem assign_len : ∀ (l : List ℕ) (st : List (ℕ × ℕ) × List (ℕ × List ℕ)),
    (l.foldl assignStep st).2.length = st.2.length + l.length := by
  intro l
  induction l with
  | nil => intro st; simp
  | cons c l ih =>
    intro st
    rw [List.foldl_cons, ih]
    simp [assignStep]
    omega

theorem assign_mem : ∀ (l : List ℕ) (R : List (ℕ × ℕ)) (acc : List (ℕ × List ℕ)),
    ∀ b ∈ (l.foldl assignStep (R, acc)).2,
      b ∈ acc ∨ ∀ v ∈ b.2, ∃ e ∈ R, isEnd b.1 e = true ∧ v = other b.1 e := by
  intro l
  induction l with
  | nil => intro R acc b hb; exact Or.inl hb
  | cons c l ih =>
    intro R acc b hb
    rw [List.foldl_cons] at hb
    rcases ih _ _ b hb with h | h
    · simp only [assignStep, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · right
        intro v hv
        simp only [List.mem_map, List.mem_filter] at hv
        obtain ⟨e, ⟨he, hce⟩, rfl⟩ := hv
        exact ⟨e, he, hce, rfl⟩
    · right
      intro v hv
      obtain ⟨e, he, h1, h2⟩ := h v hv
      simp only [assignStep, List.mem_filter] at he
      exact ⟨e, he.1, h1, h2⟩

theorem block_iff (W : ℕ → Bool) (c : ℕ) (R : List (ℕ × ℕ)) :
    (W c && ((R.filter (isEnd c)).map (other c)).any W) = true ↔
      ∃ e ∈ R, isEnd c e = true ∧ W e.1 = true ∧ W e.2 = true := by
  simp only [Bool.and_eq_true, List.any_map, List.any_eq_true, List.mem_filter, Function.comp]
  constructor
  · rintro ⟨hc, e, ⟨he, hce⟩, hv⟩
    refine ⟨e, he, hce, ?_⟩
    rw [isEnd_iff] at hce
    unfold other at hv
    by_cases h1 : e.1 = c
    · rw [if_pos h1] at hv
      exact ⟨by rw [h1]; exact hc, hv⟩
    · rw [if_neg h1] at hv
      rcases hce with h | h
      · exact absurd h h1
      · exact ⟨hv, by rw [h]; exact hc⟩
  · rintro ⟨e, he, hce, h1, h2⟩
    have hce' := (isEnd_iff c e).mp hce
    unfold other
    by_cases h3 : e.1 = c
    · refine ⟨by rw [← h3]; exact h1, e, ⟨he, hce⟩, ?_⟩
      rw [if_pos h3]; exact h2
    · rcases hce' with h | h
      · exact absurd h h3
      · refine ⟨by rw [← h]; exact h2, e, ⟨he, hce⟩, ?_⟩
        rw [if_neg h3]; exact h1

theorem assign_any (W : ℕ → Bool) : ∀ (l : List ℕ) (R : List (ℕ × ℕ)) (acc : List (ℕ × List ℕ)),
    (∃ b ∈ (l.foldl assignStep (R, acc)).2, (W b.1 && b.2.any W) = true) ↔
      (∃ b ∈ acc, (W b.1 && b.2.any W) = true) ∨
        ∃ e ∈ R, (∃ c ∈ l, isEnd c e = true) ∧ W e.1 = true ∧ W e.2 = true := by
  intro l
  induction l with
  | nil => intro R acc; simp
  | cons c l ih =>
    intro R acc
    rw [List.foldl_cons]
    simp only [assignStep]
    rw [ih]
    have hN := block_iff W c R
    constructor
    · rintro (⟨b, hb, hF⟩ | ⟨e, he, ⟨c', hc', hce'⟩, hG⟩)
      · rw [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact Or.inl ⟨b, hb, hF⟩
        · obtain ⟨e, he, hce, hG⟩ := hN.mp hF
          exact Or.inr ⟨e, he, ⟨c, List.mem_cons_self .., hce⟩, hG⟩
      · rw [List.mem_filter] at he
        exact Or.inr ⟨e, he.1, ⟨c', List.mem_cons_of_mem _ hc', hce'⟩, hG⟩
    · rintro (⟨b, hb, hF⟩ | ⟨e, he, ⟨c', hc', hce'⟩, hG⟩)
      · exact Or.inl ⟨b, List.mem_append_left _ hb, hF⟩
      · by_cases hce : isEnd c e = true
        · exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
            hN.mpr ⟨e, he, hce, hG⟩⟩
        · rw [List.mem_cons] at hc'
          rcases hc' with rfl | hc'
          · exact absurd hce' hce
          · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simpa using hce⟩, ⟨c', hc', hce'⟩, hG⟩

theorem filter_split (R : List (ℕ × ℕ)) (p q : ℕ × ℕ → Bool) :
    (R.filter (fun e => p e || q e)).length =
      (R.filter p).length + ((R.filter (fun e => !p e)).filter q).length := by
  induction R with
  | nil => rfl
  | cons e R ih =>
    cases hp : p e <;> cases hq : q e <;> simp [List.filter_cons, hp, hq, ih] <;> omega

theorem assign_sum : ∀ (l : List ℕ) (R : List (ℕ × ℕ)) (acc : List (ℕ × List ℕ)),
    ((l.foldl assignStep (R, acc)).2.map (fun b => b.2.length)).sum =
      (acc.map (fun b => b.2.length)).sum + (R.filter (fun e => l.any (fun c => isEnd c e))).length := by
  intro l
  induction l with
  | nil => intro R acc; simp
  | cons c l ih =>
    intro R acc
    rw [List.foldl_cons]
    simp only [assignStep]
    rw [ih]
    simp only [List.any_cons]
    rw [filter_split R (isEnd c) (fun e => l.any (fun c => isEnd c e))]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_map]
    omega

theorem assign_pos : ∀ (l : List ℕ) (R : List (ℕ × ℕ)) (acc : List (ℕ × List ℕ)), l.Nodup →
    (∀ c ∈ l, ∃ e ∈ R, isEnd c e = true ∧ ∀ d ∈ l, isEnd d e = true → d = c) →
    (∀ b ∈ acc, b.2 ≠ []) → ∀ b ∈ (l.foldl assignStep (R, acc)).2, b.2 ≠ [] := by
  intro l
  induction l with
  | nil => intro R acc _ _ hacc; exact hacc
  | cons c l ih =>
    intro R acc hnd hpriv hacc
    rw [List.foldl_cons]
    have hcl : c ∉ l := (List.nodup_cons.mp hnd).1
    apply ih _ _ (List.nodup_cons.mp hnd).2
    · intro c' hc'
      obtain ⟨e, he, hce, hd⟩ := hpriv c' (List.mem_cons_of_mem _ hc')
      refine ⟨e, ?_, hce, fun d hdl hde => hd d (List.mem_cons_of_mem _ hdl) hde⟩
      simp only [assignStep, List.mem_filter]
      refine ⟨he, ?_⟩
      cases h : isEnd c e
      · rfl
      · have := hd c (List.mem_cons_self ..) h
        subst this
        exact absurd hc' hcl
    · intro b hb
      simp only [assignStep, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hacc b hb
      · obtain ⟨e, he, hce, _⟩ := hpriv c (List.mem_cons_self ..)
        intro h0
        have : other c e ∈ (R.filter (isEnd c)).map (other c) :=
          List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, hce⟩, rfl⟩
        simp only at h0
        rw [h0] at this
        simp at this

theorem sum_filter_pos (l : List (ℕ × List ℕ)) :
    ((l.filter (fun b => decide (0 < b.2.length))).map (fun b => b.2.length)).sum =
      (l.map (fun b => b.2.length)).sum := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : 0 < b.2.length
    · simp [List.filter_cons, h, ih]
    · have h0 : b.2.length = 0 := by omega
      simp [List.filter_cons, h, ih, h0]

/-! ## The three lemmas -/

/-- (C1) The cover circuit has fan-in two and no NOT gate. No hypothesis. -/
theorem fanInTwo_notFree (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    FanInTwo (coverCircuit n edges cover) ∧
      ∀ g ∈ (coverCircuit n edges cover).gates, g.op ≠ GateOp.not := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨h1, h2⟩ := gates_ops n edges cover g hg
    refine ⟨?_, by omega⟩
    rcases h1 with h | h <;> simp [h]
  · obtain ⟨h1, _⟩ := gates_ops n edges cover g hg
    rcases h1 with h | h <;> rw [h] <;> intro h' <;> cases h'

theorem blocks_ok (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
    (hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    ∀ b ∈ blocks edges cover, 0 < b.2.length ∧ b.1 < n ∧ ∀ v ∈ b.2, v < n := by
  intro b hb
  have hpos := blocks_pos edges cover b hb
  have hb' : b ∈ assign edges cover := (List.mem_filter.mp hb).1
  rw [assign_eq] at hb'
  rcases assign_mem cover edges [] b hb' with h | h
  · simp at h
  · obtain ⟨v0, hv0⟩ := List.exists_mem_of_length_pos hpos
    obtain ⟨e, he, hce, _⟩ := h v0 hv0
    refine ⟨hpos, ?_, ?_⟩
    · rcases (isEnd_iff _ _).mp hce with h1 | h1
      · rw [← h1]; exact (hE e he).1
      · rw [← h1]; exact (hE e he).2
    · intro v hv
      obtain ⟨e', he', _, rfl⟩ := h v hv
      exact other_lt _ _ _ (hE e' he').1 (hE e' he').2

/-- (C2) The function: if every listed edge has both ends below `n` and an end in the cover
list, the circuit computes the edge function of the edge list (adjacency is membership of the
pair in the list, in either order). -/
theorem circuitFun_eq (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
    (hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) :
    circuitFun n (coverCircuit n edges cover) = fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges) ∧
        x i = true ∧ x j = true) := by
  funext x
  rw [circuitFun_blocks n edges cover x (blocks_ok n edges cover hE)]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, decide_eq_true_eq]
  have hA := assign_any (fun v => (List.ofFn x).getD v false) cover edges []
  rw [← assign_eq] at hA
  have hblk : (∃ b ∈ blocks edges cover, blockVal (List.ofFn x) b = true) ↔
      ∃ b ∈ assign edges cover, blockVal (List.ofFn x) b = true := by
    constructor
    · rintro ⟨b, hb, hv⟩
      exact ⟨b, (List.mem_filter.mp hb).1, hv⟩
    · rintro ⟨b, hb, hv⟩
      refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hv⟩
      simp only [blockVal, Bool.and_eq_true, List.any_eq_true] at hv
      obtain ⟨_, v, hv, _⟩ := hv
      simpa using List.length_pos_of_mem hv
  rw [hblk]
  simp only [blockVal] at hA ⊢
  rw [hA]
  simp only [List.not_mem_nil, false_and, exists_false, false_or]
  constructor
  · rintro ⟨e, he, _, h1, h2⟩
    refine ⟨⟨e.1, (hE e he).1⟩, ⟨e.2, (hE e he).2⟩, Or.inl (by simpa using he), ?_, ?_⟩
    · rw [← getD_ofFn x e.1 (hE e he).1]; exact h1
    · rw [← getD_ofFn x e.2 (hE e he).2]; exact h2
  · rintro ⟨i, j, hij, hi, hj⟩
    have gi : (List.ofFn x).getD i.val false = true := by rw [getD_ofFn x i.val i.isLt]; exact hi
    have gj : (List.ofFn x).getD j.val false = true := by rw [getD_ofFn x j.val j.isLt]; exact hj
    have cov : ∀ e ∈ edges, ∃ c ∈ cover, isEnd c e = true := by
      intro e he
      rcases hT e he with h | h
      · exact ⟨e.1, h, by simp [isEnd]⟩
      · exact ⟨e.2, h, by simp [isEnd]⟩
    rcases hij with h | h
    · exact ⟨_, h, cov _ h, gi, gj⟩
    · exact ⟨_, h, cov _ h, gj, gi⟩

/-- (C2, graph form) The same for a `SimpleGraph (Fin n)` whose adjacency is membership in the
edge list, in the form of the checked rows L-meta-154 and L-meta-221. -/
theorem circuitFun_eq_graph (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ i j : Fin n, G.Adj i j ↔ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges))
    (hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) :
    circuitFun n (coverCircuit n edges cover) =
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  rw [circuitFun_eq n edges cover hE hT]
  funext x
  simp only [hG]

theorem sum_blocks (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    ((blocks edges cover).map (fun b => b.2.length)).sum =
      (edges.filter (fun e => cover.any (fun c => isEnd c e))).length := by
  unfold blocks
  rw [sum_filter_pos, assign_eq, assign_sum]
  simp

/-- (C3, inequality) With at least one edge: size + 1 is at most edges + cover entries. -/
theorem size_le (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) (hne : edges ≠ []) :
    (coverCircuit n edges cover).size + 1 ≤ edges.length + cover.length := by
  by_cases hb : blocks edges cover = []
  · rw [size_nil n edges cover hb]
    have := List.length_pos_iff.mpr hne
    omega
  · rw [size_blocks n edges cover hb, sum_blocks]
    have h1 := List.length_filter_le (fun e => cover.any (fun c => isEnd c e)) edges
    have h2 : (blocks edges cover).length ≤ cover.length := by
      unfold blocks
      have := List.length_filter_le (fun b => decide (0 < b.2.length)) (assign edges cover)
      have hl := assign_len cover (edges, [])
      rw [← assign_eq] at hl
      simp only [List.length_nil, zero_add] at hl
      omega
    omega

/-- (C3, exact, assignment form) With at least one edge, every edge with an end in the cover
list, and every cover entry assigned at least one edge: size + 1 = edges + cover entries. -/
theorem size_eq_of_assign (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) (hne : edges ≠ [])
    (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) (hA : ∀ b ∈ assign edges cover, b.2 ≠ []) :
    (coverCircuit n edges cover).size + 1 = edges.length + cover.length := by
  have hbl : blocks edges cover = assign edges cover := by
    unfold blocks
    rw [List.filter_eq_self]
    intro b hb
    have := hA b hb
    simpa [List.length_pos_iff] using this
  have hlen : (assign edges cover).length = cover.length := by
    rw [assign_eq, assign_len]; simp
  have hcov : cover ≠ [] := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil edges hne
    intro h0
    rcases hT e he with h | h <;> simp [h0] at h
  have hb : blocks edges cover ≠ [] := by
    intro h0
    rw [hbl] at h0
    have := congrArg List.length h0
    rw [hlen] at this
    exact hcov (List.length_eq_zero_iff.mp this)
  rw [size_blocks n edges cover hb, sum_blocks, hbl, hlen]
  rw [List.filter_eq_self.mpr]
  intro e he
  rcases hT e he with h | h
  · simp only [List.any_eq_true]; exact ⟨e.1, h, by simp [isEnd]⟩
  · simp only [List.any_eq_true]; exact ⟨e.2, h, by simp [isEnd]⟩

/-- (C3, exact) With at least one edge, every edge with an end in the cover list, no repeated
cover entry, and every cover entry `c` the only cover end of some listed edge (a private edge;
for an edge with distinct ends: its other end is outside the cover): size + 1 = edges + cover
entries. -/
theorem size_eq (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) (hne : edges ≠ [])
    (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) (hnd : cover.Nodup)
    (hpriv : ∀ c ∈ cover, ∃ e ∈ edges, (e.1 = c ∨ e.2 = c) ∧
      ∀ d ∈ cover, (e.1 = d ∨ e.2 = d) → d = c) :
    (coverCircuit n edges cover).size + 1 = edges.length + cover.length := by
  apply size_eq_of_assign n edges cover hne hT
  rw [assign_eq]
  apply assign_pos cover edges [] hnd
  · intro c hc
    obtain ⟨e, he, hce, hd⟩ := hpriv c hc
    exact ⟨e, he, (isEnd_iff c e).mpr hce, fun d hdc hde => hd d hdc ((isEnd_iff d e).mp hde)⟩
  · simp

end PEqualNP.MetaComplexity.CoverCircuit
