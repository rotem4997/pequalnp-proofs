import PEqualNP.MetaComplexity.Helpers.WellFormed

/-!
# A verifier for partial MCSP made of finite-state transducers

Helper for "partial MCSP is in NP". The verifier `verify x u` reads an instance `x` and a
witness `u` over `Sym`. It is a conjunction of checks, each of which is a comparison of the
outputs of finite-state transducers (`Format`, `WellFormed`, `RowCode`): equality of two
strings, comparison of two lengths, or "every flag is true".

* `normCircuit`: a circuit rewritten so that no gate has an empty operand list and every wire
  index is bounded, with the same values (`eval_normCircuit`).
* `verify`, `witnessBound`.
* `verify_complete`, `verify_sound`, and `verify_iff`: the members of partial MCSP are exactly
  the instances with a witness of polynomial length that the verifier accepts.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.Library.Machines PEqualNP.MetaComplexity

/-! ## Circuits with no empty gate -/

/-- Cut the wire indices of a gate down to `B`; a gate that reads nothing is replaced by a
gate with the same value that reads wire `B`. -/
def fillGate (B : ℕ) (g : Gate) : Gate :=
  match g.inputs with
  | [] => ⟨match g.op with
      | GateOp.or => GateOp.or
      | _ => GateOp.not, [B]⟩
  | _ :: _ => clampGate B g

/-- Apply `fillGate` to every gate and cut the output index down to `B`. -/
def normCircuit (B : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (fillGate B), min C.output B⟩

theorem eval_normGate (B : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (w : List Bool)
    (hw : w.length ≤ B) :
    (fillGate B g).op.eval ((fillGate B g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  cases ins with
  | nil =>
    simp only at hop
    rcases hop with rfl | rfl | rfl <;>
      simp [fillGate, GateOp.eval, List.getElem?_eq_none hw]
  | cons a ins =>
    show (clampGate B ⟨op, a :: ins⟩).op.eval
        ((clampGate B ⟨op, a :: ins⟩).inputs.map fun i => w.getD i false) = _
    have e1 : ((clampGate B ⟨op, a :: ins⟩).inputs.map fun i => w.getD i false)
        = (a :: ins).map fun i => w.getD i false := by
      simp only [clampGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact getD_min hw i
    rw [e1]
    rfl

theorem wiresFrom_fill (B : ℕ) (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) → ∀ w : List Bool,
      w.length + gs.length ≤ B → wiresFrom (gs.map (fillGate B)) w = wiresFrom gs w := by
  induction gs with
  | nil => intro _ w _; rfl
  | cons g gs ih =>
    intro hg w h
    rw [List.length_cons] at h
    have e := eval_normGate B g (hg g List.mem_cons_self) w (by omega)
    have s1 : wiresFrom ((g :: gs).map (fillGate B)) w
        = wiresFrom (gs.map (fillGate B))
            (w ++ [(fillGate B g).op.eval ((fillGate B g).inputs.map fun i => w.getD i false)]) :=
      rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, e]
    apply ih fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')
    rw [List.length_append, List.length_singleton]
    omega

theorem fanInTwo_op {C : Circuit} (h : FanInTwo C) (g : Gate) (hg : g ∈ C.gates) :
    g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
  simpa using (h g hg).1

/-- The rewritten circuit has the same value on every input short enough. -/
theorem eval_normCircuit (B : ℕ) (C : Circuit) (hC : FanInTwo C) (x : List Bool)
    (h : x.length + C.gates.length ≤ B) : (normCircuit B C).eval x = C.eval x := by
  have hl : (wiresFrom C.gates x).length ≤ B := by rw [length_wiresFrom]; exact h
  show (wiresFrom (C.gates.map (fillGate B)) x).getD (min C.output B) false
    = (wiresFrom C.gates x).getD C.output false
  rw [wiresFrom_fill B _ (fanInTwo_op hC) _ h, getD_min hl]

theorem size_normCircuit (B : ℕ) (C : Circuit) :
    (normCircuit B C).gates.length = C.gates.length := by
  simp [normCircuit]

theorem goodGate_normGate (B : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) : GoodGate (fillGate B g) := by
  obtain ⟨op, ins⟩ := g
  cases ins with
  | nil =>
    simp only at hop
    rcases hop with rfl | rfl | rfl
    · exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
    · exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
  | cons a ins =>
    refine ⟨hop, ?_⟩
    show ((a :: ins).map fun i => min i B).length = 1 ∨ ((a :: ins).map fun i => min i B).length = 2
    simp only [List.length_map, List.length_cons] at hlen ⊢
    omega

/-- The rewritten circuit is good: AND, OR, NOT gates with one or two operands. -/
theorem goodC_normCircuit (B : ℕ) (C : Circuit) (hC : FanInTwo C) : GoodC (normCircuit B C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  exact goodGate_normGate B g' (fanInTwo_op hC g' hg') (hC g' hg').2

theorem fanInTwo_of_goodC {C : Circuit} (h : GoodC C) : FanInTwo C := by
  intro g hg
  obtain ⟨hop, hlen⟩ := h g hg
  refine ⟨?_, by omega⟩
  rcases hop with e | e | e <;> rw [e] <;> simp

theorem fanInTwo_normCircuit (B : ℕ) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (normCircuit B C) :=
  fanInTwo_of_goodC (goodC_normCircuit B C hC)

/-- Every wire index of the rewritten circuit is at most `B`. -/
theorem inputs_normCircuit_le (B : ℕ) (C : Circuit) :
    ∀ g ∈ (normCircuit B C).gates, ∀ a ∈ g.inputs, a ≤ B := by
  intro g hg a ha
  obtain ⟨g', _, rfl⟩ := List.mem_map.1 hg
  obtain ⟨op, ins⟩ := g'
  cases ins with
  | nil =>
    have : a ∈ [B] := ha
    rw [List.mem_singleton.1 this]
  | cons a' ins =>
    have : a ∈ (a' :: ins).map fun i => min i B := ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 this
    exact Nat.min_le_right _ _

theorem output_normCircuit_le (B : ℕ) (C : Circuit) : (normCircuit B C).output ≤ B :=
  Nat.min_le_right _ _

/-! ## The verifier -/

/-- The verifier. `x` is the instance, `u` the witness. In order: the witness is well formed;
the successor of every row is the next row, and the successor of the last row is the first;
the entries of the rows are the table of the instance; the first row has at most as many gates
as the size bound of the instance; after `x.length` evaluation steps every row has no cell left
and its entry is absent or equal to the value of its output; the instance contains a `false`.
The last check is the flag of the transducer `δsep`, `finSep`. -/
def verify (x : List Bool) (u : List Sym) : Bool :=
  (wfFlags u).all id
    && decide (succStr u = tailStr u ++ headStr u)
    && decide (tabStr u = instStr x)
    && decide ((gatesStr u).length ≤ (unaryStr x).length)
    && (outStr (stepStr^[x.length] u)).all id
    && (sepFlags x).all id

/-- A bound on the length of the witness in the length of the instance. -/
noncomputable def witnessBound : Polynomial ℕ :=
  Polynomial.X * (Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X
    + Polynomial.C 3)

theorem eval_witnessBound (L : ℕ) : witnessBound.eval L = L * (4 * L ^ 2 + 6 * L + 3) := by
  simp [witnessBound]

theorem verify_eq_true_iff (x : List Bool) (u : List Sym) :
    verify x u = true ↔ (wfFlags u).all id = true ∧ succStr u = tailStr u ++ headStr u ∧
      tabStr u = instStr x ∧ (gatesStr u).length ≤ (unaryStr x).length ∧
      (outStr (stepStr^[x.length] u)).all id = true ∧ (sepFlags x).all id = true := by
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ## Lengths -/

theorem length_encodePartial (T : List (Option Bool)) : (encodePartial T).length = 2 * T.length := by
  induction T with
  | nil => rfl
  | cons o T ih =>
    have : encodePartial (o :: T) = encodePartial [o] ++ encodePartial T := by
      simp [encodePartial]
    rw [this, List.length_append, ih, List.length_cons]
    rcases o with _ | b
    · show 2 + _ = _
      omega
    · show 2 + _ = _
      omega

theorem length_flatMap_le {α β : Type} (f : α → List β) (B : ℕ) (l : List α)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem length_encGate_le (B : ℕ) (g : Gate) (hg : GoodGate g) (hb : ∀ a ∈ g.inputs, a ≤ B) :
    (encGate g).length ≤ 2 * B + 3 := by
  obtain ⟨op, ins⟩ := g
  rcases goodGate_inputs hg with ⟨a, ha⟩ | ⟨a, b, ha⟩
  · simp only at ha
    subst ha
    have := hb a (by simp)
    simp [encGate, encRef]
    omega
  · simp only at ha
    subst ha
    have h1 := hb a (by simp)
    have h2 := hb b (by simp)
    simp [encGate, encRef]
    omega

theorem length_encW_le (B : ℕ) (w : WRow) (hw : GoodC w.2.1)
    (hb : ∀ g ∈ w.2.1.gates, ∀ a ∈ g.inputs, a ≤ B) (ho : w.2.1.output ≤ B) :
    (encW w).length ≤ w.1.length + w.2.1.gates.length * (2 * B + 3) + B + 3 := by
  have h1 := length_flatMap_le encGate (2 * B + 3) w.2.1.gates
    fun g hg => length_encGate_le B g (hw g hg) (hb g hg)
  simp only [encW, rowPre, encBody, encRef, List.length_append, List.length_map,
    List.length_cons, List.length_replicate, List.length_nil]
  omega

/-! ## Completeness -/

theorem map_getD_range {α : Type} (T : List α) (d : α) :
    (List.range T.length).map (fun j => T.getD j d) = T := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

theorem encWs_append (W W' : List WRow) : encWs (W ++ W') = encWs W ++ encWs W' :=
  List.flatMap_append

theorem encWs_singleton (w : WRow) : encWs [w] = encW w := by simp [encWs]

/-- The witness made of the rows of a good circuit on all inputs is accepted. -/
theorem verify_honest (n s B : ℕ) (T : List (Option Bool)) (hT : T.length = 2 ^ n)
    (C : Circuit) (hgood : GoodC C) (hsize : C.gates.length ≤ s)
    (hb : ∀ g ∈ C.gates, ∀ a ∈ g.inputs, a ≤ B) (ho : C.output ≤ B)
    (hval : ∀ j < 2 ^ n, T.getD j none = none ∨ T.getD j none = some (C.eval (bitsL n j))) :
    verify (List.replicate s true ++ false :: encodePartial T)
        (encWs ((List.range (2 ^ n)).map fun j => ((bitsL n j, C, T.getD j none) : WRow))) = true ∧
      (encWs ((List.range (2 ^ n)).map fun j => ((bitsL n j, C, T.getD j none) : WRow))).length
        ≤ 2 ^ n * (n + s * (2 * B + 3) + B + 3) := by
  set fW : ℕ → WRow := fun j => (bitsL n j, C, T.getD j none) with hfW
  set W : List WRow := (List.range (2 ^ n)).map fW with hWdef
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ n = N + 1 :=
    ⟨2 ^ n - 1, by have := Nat.pos_of_ne_zero (show 2 ^ n ≠ 0 by simp); omega⟩
  have hW : W = fW 0 :: (List.range N).map (fun j => fW (j + 1)) := by
    rw [hWdef, hN, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  have hWg : ∀ w ∈ W, GoodC w.2.1 := by
    intro w hw
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hw
    exact hgood
  have hWlen : W.length = 2 ^ n := by simp [hWdef]
  have hWn : NoOnes W := by
    intro i w hi hl
    rw [hWlen] at hl
    have hi' : i < 2 ^ n := by omega
    rw [hWdef, List.getElem?_map, List.getElem?_range hi'] at hi
    have : fW i = w := by simpa using hi
    rw [← this]
    exact false_mem_bitsL n i hl
  refine ⟨?_, ?_⟩
  · rw [verify_eq_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h0 : ∀ b ∈ (fW 0).1, b = false := by
        intro b hb'
        have : b ∈ bitsL n 0 := hb'
        rw [bitsL_zero] at this
        exact List.eq_of_mem_replicate this
      have := wfFlags_encWs (fW 0) _ h0 (by rw [← hW]; exact hWg) (by rw [← hW]; exact hWn)
      rw [← hW] at this
      rw [this]
      rfl
    · rw [succStr_encWs W hWg]
      have e1 : tailStr (encWs W) ++ headStr (encWs W)
          = encWs (((List.range N).map fun j => fW (j + 1)).map neutW ++ [neutW (fW 0)]) := by
        rw [hW, tailStr_encWs, headStr_encWs, encWs_append, encWs_singleton]
      rw [e1]
      congr 1
      rw [hWdef, hN, List.range_succ, List.map_append, List.map_append]
      simp only [List.map_map]
      congr 1
      · apply List.map_congr_left
        intro j _
        show (inc (bitsL n j), C, (none : Option Bool)) = (bitsL n (j + 1), C, none)
        rw [inc_bitsL]
      · show [((inc (bitsL n N), C, none) : WRow)] = [(bitsL n 0, C, none)]
        rw [inc_bitsL, ← hN, bitsL_zero, (bitsL_eq_zero_iff n (2 ^ n)).2 (dvd_refl _)]
    · rw [tabStr_encWs, instStr_eq, hWdef, List.map_map]
      congr 1
      rw [← hT]
      exact map_getD_range T none
    · rw [hW, gatesStr_encWs _ _ hgood, unaryStr_eq]
      simpa using hsize
    · set ps : List (List Bool × Option Bool) :=
        (List.range (2 ^ n)).map fun j => (bitsL n j, T.getD j none) with hps
      have hst : encWs W = encState (ps.map fun p => ((initRow C p.1, p.2) : Row)) := by
        rw [encWs_eq_encState, hWdef, hps, List.map_map, List.map_map]
        rfl
      have hk : ∀ p ∈ ps, p.1.length + C.gates.length
          ≤ (List.replicate s true ++ false :: encodePartial T).length := by
        intro p hp
        obtain ⟨j, _, rfl⟩ := List.mem_map.1 hp
        have := Nat.lt_two_pow_self (n := n)
        simp only [length_bitsL, List.length_append, List.length_replicate, List.length_cons,
          length_encodePartial, hT]
        omega
      have hout := out_step_initRow C (fun g hg => (hgood g hg).1) ps _ hk
      show (fstRun2 δout finOut OutQ.init
        ((fstRun2 δstep finStep StepQ.start)^[_] (encWs W))).all id = true
      rw [hst, hout, List.all_eq_true]
      intro b hb'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
      simpa using hval j (List.mem_range.1 hj)
    · rw [sepFlags_eq]
      rfl
  · have h1 := length_flatMap_le encW (n + s * (2 * B + 3) + B + 3) W (by
      intro w hw
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hw
      have h2 := length_encW_le B (fW j) hgood hb ho
      have h3 : (fW j).1.length = n := length_bitsL n j
      have h4 : (fW j).2.1.gates.length * (2 * B + 3) ≤ s * (2 * B + 3) :=
        Nat.mul_le_mul_right _ hsize
      omega)
    rw [hWlen] at h1
    exact h1

/-- Completeness: a member of partial MCSP has an accepted witness of bounded length. -/
theorem verify_complete (x : List Bool) (hx : x ∈ PartialMCSP) :
    ∃ u : List Sym, u.length ≤ witnessBound.eval x.length ∧ verify x u = true := by
  obtain ⟨n, s, T, rfl, hT, f, hcons, C, hfan, hsize, hev⟩ := hx
  have hC' := goodC_normCircuit (n + s) C hfan
  have hsz : (normCircuit (n + s) C).gates.length ≤ s := by
    rw [size_normCircuit]; exact hsize
  have hval : ∀ j < 2 ^ n, T.getD j none = none
      ∨ T.getD j none = some ((normCircuit (n + s) C).eval (bitsL n j)) := by
    intro j hj
    have e : (normCircuit (n + s) C).eval (bitsL n j) = f (bitsOf n j) := by
      rw [eval_normCircuit _ _ hfan _ (by
        rw [length_bitsL]
        exact Nat.add_le_add_left hsize n), bitsL_eq_ofFn, hev]
    rw [e]
    rcases hT' : T.getD j none with _ | b
    · exact Or.inl rfl
    · right
      have := hcons (bitsOf n j) b (by rw [tableIndex_bitsOf hj]; exact hT')
      rw [this]
  obtain ⟨hv, hl⟩ := verify_honest n s (n + s) T hT _ hC' hsz
    (inputs_normCircuit_le _ C) (output_normCircuit_le _ C) hval
  refine ⟨_, ?_, hv⟩
  refine le_trans hl ?_
  rw [eval_witnessBound]
  have hL : (List.replicate s true ++ false :: encodePartial T).length = s + 1 + 2 * 2 ^ n := by
    simp only [List.length_append, List.length_replicate, List.length_cons,
      length_encodePartial, hT]
    omega
  rw [hL]
  have hn := Nat.lt_two_pow_self (n := n)
  set P := 2 ^ n with hP
  set L := s + 1 + 2 * P with hLdef
  have h1 : P ≤ L := by omega
  have h2 : s * (2 * (n + s) + 3) ≤ L * (4 * L + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : n + s * (2 * (n + s) + 3) + (n + s) + 3 ≤ 4 * L ^ 2 + 6 * L + 3 := by
    have : L * (4 * L + 3) = 4 * L ^ 2 + 3 * L := by ring
    omega
  exact Nat.mul_le_mul h1 h3

/-! ## Soundness -/

/-- The successor of a row, without its entry. -/
def succW (w : WRow) : WRow := (inc w.1, w.2.1, none)

/-- If the successors of the rows `a :: W` are the rows `W` followed by `z`, and `a` holds the
bits of `j`, then row `i` holds the bits of `j + i`, `z` holds the bits of `j + W.length + 1`,
and all have the circuit of `a`. -/
theorem chain_rows (m : ℕ) (c : Circuit) (W : List WRow) : ∀ (a z : WRow) (j : ℕ),
    (a :: W).map succW = W.map neutW ++ [neutW z] → a.1 = bitsL m j → a.2.1 = c →
      (∀ i w, (a :: W)[i]? = some w → w.1 = bitsL m (j + i) ∧ w.2.1 = c) ∧
        z.1 = bitsL m (j + W.length + 1) ∧ z.2.1 = c := by
  induction W with
  | nil =>
    intro a z j h ha hc
    have h0 : succW a = neutW z := by simpa using h
    have h1 : inc a.1 = z.1 := congrArg Prod.fst h0
    have h2 : a.2.1 = z.2.1 := by
      have := congrArg (fun w : WRow => w.2.1) h0
      exact this
    refine ⟨?_, ?_, ?_⟩
    · intro i w hi
      cases i with
      | zero =>
        have : a = w := by simpa using hi
        rw [← this]
        exact ⟨ha, hc⟩
      | succ i => simp at hi
    · rw [← h1, ha, inc_bitsL]
      rfl
    · rw [← h2, hc]
  | cons b W ih =>
    intro a z j h ha hc
    have h' : succW a :: (b :: W).map succW = neutW b :: (W.map neutW ++ [neutW z]) := h
    obtain ⟨h0, hrest⟩ := List.cons.inj h'
    have h1 : inc a.1 = b.1 := congrArg Prod.fst h0
    have h2 : a.2.1 = b.2.1 := by
      have := congrArg (fun w : WRow => w.2.1) h0
      exact this
    obtain ⟨ih1, ih2, ih3⟩ := ih b z (j + 1) hrest (by rw [← h1, ha, inc_bitsL]) (by rw [← h2, hc])
    refine ⟨?_, ?_, ih3⟩
    · intro i w hi
      cases i with
      | zero =>
        have : a = w := by simpa using hi
        rw [← this]
        exact ⟨ha, hc⟩
      | succ i =>
        have e : j + (i + 1) = j + 1 + i := by omega
        rw [e]
        exact ih1 i w (by simpa using hi)
    · rw [ih2]
      congr 1
      simp only [List.length_cons]
      omega

/-- Soundness: an instance with an accepted witness is a member of partial MCSP. -/
theorem verify_sound (x : List Bool) (u : List Sym) (h : verify x u = true) :
    x ∈ PartialMCSP := by
  rw [verify_eq_true_iff] at h
  obtain ⟨hwf, hrot, htab, hgates, hout, hsep⟩ := h
  obtain ⟨s, r, rfl⟩ := sepFlags_sound x hsep
  obtain ⟨w0, W', rfl, hg, hzero, hno⟩ := wf_sound u hwf
  rw [unaryStr_eq] at hgates
  rw [instStr_eq] at htab
  set W : List WRow := w0 :: W' with hW
  set m := w0.1.length with hm
  set c := w0.2.1 with hc
  -- the rotation, as an equation between lists of rows
  have hrot' : W.map succW = W'.map neutW ++ [neutW w0] := by
    have e1 : succStr (encWs W) = encWs (W.map succW) := succStr_encWs W hg
    have e2 : tailStr (encWs W) ++ headStr (encWs W)
        = encWs (W'.map neutW ++ [neutW w0]) := by
      rw [hW, tailStr_encWs, headStr_encWs, encWs_append, encWs_singleton]
    rw [e1, e2] at hrot
    apply encWs_inj _ _ _ _ hrot
    · intro w hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      exact hg w' hw'
    · intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
        exact hg w' (List.mem_cons_of_mem _ hw')
      · rw [List.mem_singleton.1 hw]
        exact hg w0 List.mem_cons_self
  have h0 : w0.1 = bitsL m 0 := by
    rw [bitsL_zero]
    exact List.eq_replicate_iff.2 ⟨rfl, hzero⟩
  obtain ⟨hrows, hwrap, _⟩ := chain_rows m c W' w0 w0 0 hrot' h0 rfl
  have hrows' : ∀ i w, W[i]? = some w → w.1 = bitsL m i ∧ w.2.1 = c := by
    intro i w hi
    have := hrows i w hi
    rwa [Nat.zero_add] at this
  -- the number of rows
  have hk : W.length = W'.length + 1 := rfl
  have hdvd : 2 ^ m ∣ W.length := by
    rw [← bitsL_eq_zero_iff, ← bitsL_zero, hk, ← h0, hwrap]
    congr 1
    omega
  have hpos : 0 < 2 ^ m := Nat.pos_of_ne_zero (by simp)
  have hge : 2 ^ m ≤ W.length := Nat.le_of_dvd (by omega) hdvd
  have hle : W.length ≤ 2 ^ m := by
    by_contra hcon
    have hi : 2 ^ m - 1 < W.length := by omega
    have hget : W[2 ^ m - 1]? = some W[2 ^ m - 1] := List.getElem?_eq_getElem hi
    have h1 := (hrows' _ _ hget).1
    have h2 := hno _ _ hget (by omega)
    rw [h1] at h2
    exact not_false_mem_bitsL m h2
  have hlen : W.length = 2 ^ m := le_antisymm hle hge
  -- the table
  set T : List (Option Bool) := W.map fun w => w.2.2 with hT
  have hTlen : T.length = 2 ^ m := by rw [hT, List.length_map, hlen]
  have hr : r = encodePartial T := by rw [← htab, tabStr_encWs]
  -- the size
  have hsize : c.gates.length ≤ s := by
    rw [hW, gatesStr_encWs _ _ (hg w0 List.mem_cons_self)] at hgates
    simpa using hgates
  -- the values
  set ps : List (List Bool × Option Bool) := W.map fun w => (w.1, w.2.2) with hps
  have hst : encWs W = encState (ps.map fun p => ((initRow c p.1, p.2) : Row)) := by
    rw [encWs_eq_encState, hps, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have := (hrows' i _ (List.getElem?_eq_getElem hi)).2
    show _ = ((initRow c _, _) : Row)
    rw [this]
  have hkk : ∀ p ∈ ps, p.1.length + c.gates.length
      ≤ (List.replicate s true ++ false :: r).length := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have h1 := (hrows' i _ (List.getElem?_eq_getElem hi)).1
    have := Nat.lt_two_pow_self (n := m)
    simp only [h1, length_bitsL, List.length_append, List.length_replicate, List.length_cons, hr,
      length_encodePartial, hTlen]
    omega
  have hflags := out_step_initRow c (fun g hg' => (hg w0 List.mem_cons_self g hg').1) ps _ hkk
  have hout' : (fstRun2 δout finOut OutQ.init
      ((fstRun2 δstep finStep StepQ.start)^[(List.replicate s true ++ false :: r).length]
        (encWs W))).all id = true := hout
  rw [hst, hflags, List.all_eq_true] at hout'
  have hval : ∀ j < 2 ^ m, T.getD j none = none
      ∨ T.getD j none = some (c.eval (bitsL m j)) := by
    intro j hj
    have hj' : j < W.length := by omega
    have h1 := (hrows' j _ (List.getElem?_eq_getElem hj')).1
    have hTj : T.getD j none = W[j].2.2 := by
      simp [hT, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    have hmem : (W[j].1, W[j].2.2) ∈ ps := List.mem_map.2 ⟨W[j], List.getElem_mem hj', rfl⟩
    have := hout' _ (List.mem_map.2 ⟨_, hmem, rfl⟩)
    rw [hTj, ← h1]
    simpa using this
  refine ⟨m, s, T, by rw [hr], hTlen, fun y => c.eval (List.ofFn y), ?_, c,
    fanInTwo_of_goodC (hg w0 List.mem_cons_self), hsize, fun _ => rfl⟩
  intro y b hb
  have := hval (tableIndex y) (tableIndex_lt y)
  rw [hb, bitsL_eq_ofFn, bitsOf_tableIndex] at this
  rcases this with h1 | h1
  · exact absurd h1 (by simp)
  · exact (Option.some.inj h1).symm

/-! ## The characterisation -/

/-- Partial MCSP is the set of instances with a witness of polynomial length that the
transducer verifier accepts. -/
theorem verify_iff : ∃ q : Polynomial ℕ, ∀ x : List Bool,
    x ∈ PartialMCSP ↔ ∃ u : List Sym, u.length ≤ q.eval x.length ∧ verify x u = true :=
  ⟨witnessBound, fun x =>
    ⟨verify_complete x, fun ⟨u, _, hu⟩ => verify_sound x u hu⟩⟩

end PEqualNP.MetaComplexity.Helpers
