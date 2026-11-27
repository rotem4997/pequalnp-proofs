import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A cut of L-meta-4031 (the Petersen graph needs 19 gates) by gate elimination.
-- The first child is step L-meta-4033: the Petersen graph minus the vertex 9 (pv) needs 16 gates.
-- The second child is a normal form: a least circuit of at most 18 gates for the Petersen graph
-- has an input v with three gates that read it, or read an AND or NOT gate that reads it.
-- Setting v to false makes those three gates vanish, and an automorphism of the Petersen graph
-- sending v to 9 turns what is left into a circuit of at most 15 gates for pv.
theorem PEqualNP.Outside.R_meta_4031_23
    (hPv : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
      x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
      x 5 && x 7 || x 6 && x 8 || x 8 && x 5) 15)
    (hNormal : ∀ D : Circuit, FanInTwo D → D.size ≤ 18 →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
        x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) →
      (∀ E : Circuit, FanInTwo E → E.size < D.size →
        ∃ x : Fin 10 → Bool, E.eval (List.ofFn x) ≠ D.eval (List.ofFn x)) →
      ∃ v : Fin 10, 3 ≤ {j : Fin D.gates.length |
        (↑v ∈ (D.gates.get j).inputs ∧
          ((D.gates.get j).op = GateOp.not → (D.gates.get j).inputs.head? = some ↑v)) ∨
        ∃ i : Fin D.gates.length,
          (↑v ∈ (D.gates.get i).inputs ∧
            ((D.gates.get i).op = GateOp.not → (D.gates.get i).inputs.head? = some ↑v)) ∧
          (D.gates.get i).op ≠ GateOp.or ∧
          (10 + (i : ℕ) ∈ (D.gates.get j).inputs ∧
            ((D.gates.get j).op = GateOp.not →
              (D.gates.get j).inputs.head? = some (10 + (i : ℕ))))}.ncard) :
    ¬ HasCircuitSize 10 (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
      x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
      x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18 := by
  -- GATE ELIMINATION. Every wire of the old circuit gets a symbol: a constant (`inl`) or a wire
  -- of the simplified circuit (`inr`). A gate reading a constant vanishes into a symbol.
  -- the wires after one more gate, as in `Circuit.wires`
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let val (w : List Bool) (s : Bool ⊕ ℕ) : Bool := s.elim id (w.getD · false)
  -- the value of a gate on the symbols `vs` when every wire among them carries `b`
  let probe (op : GateOp) (vs : List (Bool ⊕ ℕ)) (b : Bool) : Bool :=
    op.eval (vs.map (Sum.elim id fun _ => b))
  -- the first wire among the symbols
  let wire (vs : List (Bool ⊕ ℕ)) : ℕ :=
    (vs.find? Sum.isRight).elim 0 (Sum.elim (fun _ => 0) id)
  -- a gate reading a constant becomes a constant, a copy of its wire or the negation of it;
  -- any other gate stays, reading the wires its symbols name
  let simplify (op : GateOp) (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    if vs.any Sum.isLeft then
      if probe op vs false = probe op vs true then .inl (.inl (probe op vs false))
      else if probe op vs false then .inr ⟨.not, [wire vs]⟩ else .inl (.inr (wire vs))
    else .inr ⟨op, vs.map (Sum.elim (fun _ => 0) id)⟩
  -- with a constant among at most two symbols, a gate reads at most one wire
  have one_wire (vs : List (Bool ⊕ ℕ)) (w : List Bool) (hlen : vs.length ≤ 2)
      (hc : vs.any Sum.isLeft) :
      vs.map (val w) = vs.map (Sum.elim id fun _ => w.getD (wire vs) false) := by
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rfl
    · rcases a with a | a
      · rfl
      · cases hc
    · rcases a with a | a <;> rcases b with b | b
      · rfl
      · rfl
      · rfl
      · cases hc
    · simp at hlen
  -- a gate whose value depends on its wires reads the wire `wire vs`
  have wire_mem (op : GateOp) (vs : List (Bool ⊕ ℕ))
      (h : probe op vs false ≠ probe op vs true) : .inr (wire vs) ∈ vs := by
    cases hf : vs.find? Sum.isRight with
    | none =>
      refine absurd (congrArg op.eval (List.map_congr_left fun s hs => ?_)) h
      rcases s with c | k
      · rfl
      · exact absurd rfl (List.find?_eq_none.1 hf _ hs)
    | some s =>
      rcases s with c | k
      · cases List.find?_some hf
      · show .inr ((vs.find? Sum.isRight).elim 0 (Sum.elim (fun _ => 0) id)) ∈ vs
        rw [hf]; exact List.mem_of_find?_eq_some hf
  -- the simplified gate computes what the gate did
  have simplify_sound (op : GateOp) (vs : List (Bool ⊕ ℕ)) (w : List Bool)
      (hlen : vs.length ≤ 2) :
      (simplify op vs).elim (val w) (fun g => g.op.eval (g.inputs.map (w.getD · false))) =
        op.eval (vs.map (val w)) := by
    by_cases hc : vs.any Sum.isLeft
    · have h3 (f : Bool → Bool) (x : Bool) :
          (if f false = f true then f false else if f false then !x else x) = f x := by
        cases x <;> cases f false <;> cases f true <;> rfl
      rw [one_wire vs w hlen hc]
      show _ = probe op vs (w.getD (wire vs) false)
      rw [← h3 (probe op vs)]
      simp only [simplify, ite_eq_left hc]
      split_ifs <;> rfl
    · simp only [simplify, ite_eq_right hc, Sum.elim_inr, List.map_map]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      rcases s with c | k
      · exact absurd (List.any_eq_true.2 ⟨_, hs, rfl⟩) hc
      · rfl
  -- a gate that vanishes into a wire copies one of its own wires
  have simplify_mem (op : GateOp) (vs : List (Bool ⊕ ℕ)) (k : ℕ) :
      simplify op vs = .inl (.inr k) → .inr k ∈ vs := by
    simp only [simplify]
    split_ifs with hc hpt hpf <;> intro h <;> cases h
    exact wire_mem op vs hpt
  -- a gate that stays has fan-in at most two
  have simplify_gate (op : GateOp) (vs : List (Bool ⊕ ℕ)) (ng : Gate)
      (hop : op ∈ ({.and, .or, .not} : Set GateOp)) (hlen : vs.length ≤ 2)
      (h : simplify op vs = .inr ng) :
      ng.op ∈ ({.and, .or, .not} : Set GateOp) ∧ ng.inputs.length ≤ 2 := by
    simp only [simplify] at h
    split_ifs at h <;> cases h
    · exact ⟨by simp, by simp⟩
    · exact ⟨hop, by simpa using hlen⟩
  -- a gate reading a constant vanishes; an AND or NOT gate reading false becomes a constant
  have simplify_const (op : GateOp) (vs : List (Bool ⊕ ℕ)) (c : Bool)
      (hop : op ∈ ({.and, .or, .not} : Set GateOp)) (hlen : vs.length ≤ 2)
      (hc : .inl c ∈ vs) (hnot : op = .not → vs.head? = some (.inl c)) :
      ∃ s, simplify op vs = .inl s ∧ (op ≠ .or → c = false → ∃ b, s = .inl b) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · cases hc
    · obtain rfl : a = .inl c := by simpa [eq_comm] using hc
      rcases hop with rfl | rfl | rfl <;> cases c <;> exact ⟨_, rfl, fun _ _ => ⟨_, rfl⟩⟩
    · rcases hop with rfl | rfl | rfl
      rotate_left 2
      · obtain rfl : a = .inl c := by simpa using hnot rfl
        cases c <;> exact ⟨_, rfl, fun _ _ => ⟨_, rfl⟩⟩
      all_goals
        obtain rfl | rfl : a = .inl c ∨ b = .inl c := by simpa [eq_comm] using hc
        · rcases b with (_ | _) | b <;> cases c <;> exact ⟨_, rfl, by simp⟩
        · rcases a with (_ | _) | a <;> cases c <;> exact ⟨_, rfl, by simp⟩
    · simp at hlen
  -- simplify the gates in order; the state holds the symbol of every old wire, the new gates,
  -- and for every old gate whether it vanished
  let elimStep (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate × List Bool) (g : Gate) :
      List (Bool ⊕ ℕ) × List Gate × List Bool :=
    (simplify g.op (g.inputs.map (acc.1.getD · (.inl false)))).elim
      (fun s => (acc.1 ++ [s], acc.2.1, acc.2.2 ++ [true]))
      (fun ng => (acc.1 ++ [.inr (n + acc.2.1.length)], acc.2.1 ++ [ng], acc.2.2 ++ [false]))
  -- every old gate adds one symbol and one flag
  have elim_shape (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate × List Bool,
      ∃ t t', (gs.foldl (elimStep n) acc).1 = acc.1 ++ t ∧ t.length = gs.length ∧
        (gs.foldl (elimStep n) acc).2.2 = acc.2.2 ++ t' ∧ t'.length = gs.length := by
    induction gs with
    | nil => intro acc; exact ⟨[], [], by simp⟩
    | cons g gs ih =>
      intro acc
      obtain ⟨t, t', h1, h2, h3, h4⟩ := ih (elimStep n acc g)
      obtain ⟨x, y, hx, hy⟩ : ∃ x y, (elimStep n acc g).1 = acc.1 ++ [x] ∧
          (elimStep n acc g).2.2 = acc.2.2 ++ [y] := by
        simp only [elimStep]
        cases simplify g.op (g.inputs.map (acc.1.getD · (.inl false))) <;>
          exact ⟨_, _, rfl, rfl⟩
      exact ⟨x :: t, y :: t', by simp [h1, hx], by simp [h2], by simp [h3, hy], by simp [h4]⟩
  have wires_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append]; simp; omega
  have getD_mem (st : List (Bool ⊕ ℕ)) (i k : ℕ) (h : st.getD i (.inl false) = .inr k) :
      .inr k ∈ st := by
    rw [List.getD_eq_getElem?_getD] at h
    cases hi : st[i]? with
    | none => simp [hi] at h
    | some s => simp only [hi, Option.getD_some] at h; exact h ▸ List.mem_of_getElem? hi
  -- the simplified circuit carries, through the symbols, the values of the old wires; it has
  -- fan-in two, and as many gates as the old circuit less the vanished ones
  have elim_inv (n : ℕ) (wIn : List Bool) (hwIn : wIn.length = n) (gs : List Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      ∀ (st : List (Bool ⊕ ℕ)) (ngs : List Gate) (fl : List Bool),
        (∀ k, .inr k ∈ st → k < n + ngs.length) →
        (∀ g ∈ ngs, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        let r := gs.foldl (elimStep n) (st, ngs, fl)
        (∀ k, .inr k ∈ r.1 → k < n + r.2.1.length) ∧
        (∀ g ∈ r.2.1, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        r.2.1.length + r.2.2.count true = ngs.length + fl.count true + gs.length ∧
        r.1.map (val (r.2.1.foldl step wIn)) =
          gs.foldl step (st.map (val (ngs.foldl step wIn))) := by
    induction gs with
    | nil => intro st ngs fl hb hf; exact ⟨hb, hf, by simp, rfl⟩
    | cons g gs ih =>
      intro st ngs fl hb hf
      obtain ⟨hg, hgs⟩ := List.forall_mem_cons.1 hgs
      have hvs : (g.inputs.map (st.getD · (.inl false))).length ≤ 2 := by simpa using hg.2
      have hread (W : List Bool) : (g.inputs.map (st.getD · (.inl false))).map (val W) =
          g.inputs.map ((st.map (val W)).getD · false) := by
        simp only [List.map_map]; congr 1; funext i
        exact (List.getD_map (l := st) (d := (Sum.inl false : Bool ⊕ ℕ)) (n := i) (val W)).symm
      have hs := simplify_sound g.op _ (ngs.foldl step wIn) hvs
      simp only [List.foldl_cons]
      cases hc : simplify g.op (g.inputs.map (st.getD · (.inl false))) with
      | inl s =>
        have hE : elimStep n (st, ngs, fl) g = (st ++ [s], ngs, fl ++ [true]) := by
          simp only [elimStep, hc, Sum.elim_inl]
        rw [hc, Sum.elim_inl] at hs
        rw [hE]
        obtain ⟨h1, h2, h3, h4⟩ := ih hgs (st ++ [s]) ngs (fl ++ [true]) (fun k hk => by
          rcases List.mem_append.1 hk with hk | hk
          · exact hb k hk
          · obtain rfl := List.mem_singleton.1 hk
            obtain ⟨i, -, hi⟩ := List.mem_map.1 (simplify_mem _ _ k hc)
            exact hb k (getD_mem st i k hi)) hf
        refine ⟨h1, h2, by simp at h3 ⊢; omega, ?_⟩
        rw [h4, List.map_append, List.map_singleton, hs, hread]
      | inr ng =>
        have hE : elimStep n (st, ngs, fl) g =
            (st ++ [.inr (n + ngs.length)], ngs ++ [ng], fl ++ [false]) := by
          simp only [elimStep, hc, Sum.elim_inr]
        rw [hc, Sum.elim_inr] at hs
        rw [hE]
        have hlenW : (ngs.foldl step wIn).length = n + ngs.length := by rw [wires_len, hwIn]
        obtain ⟨h1, h2, h3, h4⟩ := ih hgs (st ++ [.inr (n + ngs.length)]) (ngs ++ [ng])
          (fl ++ [false]) (fun k hk => by
            rcases List.mem_append.1 hk with hk | hk
            · have := hb k hk; simp; omega
            · obtain rfl := Sum.inr_injective (List.mem_singleton.1 hk); simp)
          (fun a ha => by
            rcases List.mem_append.1 ha with ha | ha
            · exact hf a ha
            · obtain rfl := List.mem_singleton.1 ha
              exact simplify_gate _ _ _ hg.1 hvs hc)
        refine ⟨h1, h2, by simp at h3 ⊢; omega, ?_⟩
        rw [h4, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        have hst : st.map (val (step (ngs.foldl step wIn) ng)) =
            st.map (val (ngs.foldl step wIn)) := by
          refine List.map_congr_left fun s hs' => ?_
          rcases s with b | k
          · rfl
          · exact List.getD_append _ _ _ _ (hlenW ▸ hb k hs')
        have hnew : val (step (ngs.foldl step wIn) ng) (.inr (n + ngs.length)) =
            g.op.eval (g.inputs.map ((st.map (val (ngs.foldl step wIn))).getD · false)) := by
          rw [← hread, ← hs, ← hlenW]
          simp [val, step, List.getD_eq_getElem?_getD]
        rw [hst, hnew]
  -- gate `j` is simplified from the symbols of the wires before it; a gate that vanishes
  -- leaves its symbol on its wire and is flagged
  have elim_at (n : ℕ) (gs : List Gate) (st0 : List (Bool ⊕ ℕ)) (j : ℕ) (hj : j < gs.length) :
      let pre := (gs.take j).foldl (elimStep n) (st0, [], [])
      let r := gs.foldl (elimStep n) (st0, [], [])
      (∃ t, pre.1 = st0 ++ t ∧ t.length = j) ∧
      (∀ i < st0.length + j, r.1.getD i (.inl false) = pre.1.getD i (.inl false)) ∧
      ∀ s, simplify gs[j].op (gs[j].inputs.map (pre.1.getD · (.inl false))) = .inl s →
        r.1.getD (st0.length + j) (.inl false) = s ∧ r.2.2.getD j false = true := by
    intro pre r
    obtain ⟨t, t', h1, h2, h3, h4⟩ := elim_shape n (gs.take j) (st0, [], [])
    have hlen : pre.1.length = st0.length + j := by simp [pre, h1, h2, hj.le]
    have hlen2 : pre.2.2.length = j := by simp [pre, h3, h4, hj.le]
    have hr : r = (gs.drop (j + 1)).foldl (elimStep n) (elimStep n pre gs[j]) := by
      simp only [r, pre]
      conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
      rw [List.foldl_append, List.foldl_cons]
    obtain ⟨u, u', h5, -, h7, -⟩ := elim_shape n (gs.drop (j + 1)) (elimStep n pre gs[j])
    obtain ⟨x, y, hx, hy⟩ : ∃ x y, (elimStep n pre gs[j]).1 = pre.1 ++ [x] ∧
        (elimStep n pre gs[j]).2.2 = pre.2.2 ++ [y] := by
      simp only [elimStep]
      cases simplify gs[j].op (gs[j].inputs.map (pre.1.getD · (.inl false))) <;>
        exact ⟨_, _, rfl, rfl⟩
    have hr1 : r.1 = pre.1 ++ x :: u := by rw [hr, h5, hx]; simp
    refine ⟨⟨t, h1, by simp [h2, hj.le]⟩,
      fun i hi => by rw [hr1, List.getD_append _ _ _ _ (hlen ▸ hi)], fun s hs => ?_⟩
    have hE : elimStep n pre gs[j] = (pre.1 ++ [s], pre.2.1, pre.2.2 ++ [true]) := by
      simp only [elimStep, hs, Sum.elim_inl]
    obtain rfl : x = s := by simpa [hE] using hx.symm
    have hr2 : r.2.2 = pre.2.2 ++ true :: u' := by rw [hr, h7, hE]; simp
    constructor
    · rw [hr1, ← hlen]; simp [List.getD_eq_getElem?_getD]
    · rw [hr2, ← hlen2]; simp [List.getD_eq_getElem?_getD]
  -- MAIN ARGUMENT. Take a least circuit `D` for the Petersen graph.
  rintro ⟨C, hCfan, hCsize, hC⟩
  classical
  have hex : ∃ s, ∃ D : Circuit, FanInTwo D ∧ D.size = s ∧
      ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) :=
    ⟨_, C, hCfan, rfl, fun _ => rfl⟩
  obtain ⟨D, hDfan, hDsize, hDC⟩ := Nat.find_spec hex
  have hD18 : D.size ≤ 18 :=
    hDsize ▸ (Nat.find_min' hex ⟨C, hCfan, rfl, fun _ => rfl⟩).trans hCsize
  -- by the normal form, setting some input `v` to false makes three gates vanish
  obtain ⟨v, hv⟩ := hNormal D hDfan hD18 (fun x => (hDC x).trans (hC x)) fun E hE hlt => by
    by_contra! h
    exact Nat.find_min hex (hDsize ▸ hlt) ⟨E, hE, rfl, fun x => (h x).trans (hDC x)⟩
  -- the automorphism `σ v` of the Petersen graph sends `v` to 9 and the other inputs onto pv
  let σ : Fin 10 → Fin 10 → ℕ := ![![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
    ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
    ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
    ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
    ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  have hσ9 : ∀ v i : Fin 10, i ≠ v → σ v i < 9 := by revert σ; decide
  have hσ : ∀ (v : Fin 10) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool),
      (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
        (fun i => if i = v then false else
          [b0, b1, b2, b3, b4, b5, b6, b7, b8].getD (σ v i) false) =
      (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) ![b0, b1, b2, b3, b4, b5, b6, b7, b8] := by
    revert σ; decide +kernel
  -- the inputs of `D` once `v` is false: a constant and the nine inputs of pv
  let st0 : List (Bool ⊕ ℕ) :=
    List.ofFn fun i : Fin 10 => if i = v then .inl false else .inr (σ v i)
  have hst0 : ∀ k, .inr k ∈ st0 → k < 9 + ([] : List Gate).length := by
    intro k hk
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 hk
    by_cases h : i = v
    · simp [h] at hi
    · simp only [h, ↓reduceIte, Sum.inr.injEq] at hi; subst hi; simpa using hσ9 v i h
  let r := D.gates.foldl (elimStep 9) (st0, [], [])
  have hinv (y : Fin 9 → Bool) :=
    elim_inv 9 (List.ofFn y) (List.length_ofFn ..) D.gates hDfan st0 [] [] hst0 (by simp)
  -- gate `j` vanishes, and is flagged, when it reads a wire whose symbol before it is constant
  have hcol (j : Fin D.gates.length) (w : ℕ) (c : Bool)
      (hw : ((D.gates.take j).foldl (elimStep 9) (st0, [], [])).1.getD w (.inl false) = .inl c)
      (hR : w ∈ D.gates[(j : ℕ)].inputs ∧
        (D.gates[(j : ℕ)].op = GateOp.not → D.gates[(j : ℕ)].inputs.head? = some w)) :
      r.2.2.getD j false = true ∧ (D.gates[(j : ℕ)].op ≠ GateOp.or → c = false →
        ∃ b, r.1.getD (10 + j) (.inl false) = .inl b) := by
    have hg := hDfan _ (List.getElem_mem j.isLt)
    obtain ⟨s, hs, hsc⟩ := simplify_const _ (D.gates[(j : ℕ)].inputs.map
      (((D.gates.take j).foldl (elimStep 9) (st0, [], [])).1.getD · (.inl false))) c hg.1
      (by simpa using hg.2) (List.mem_map.2 ⟨w, hR.1, hw⟩)
      (fun hn => by rw [List.head?_map, hR.2 hn, Option.map_some, hw])
    obtain ⟨h1, h2⟩ := (elim_at 9 D.gates st0 j j.isLt).2.2 s hs
    refine ⟨h2, fun ho hc => ?_⟩
    obtain ⟨b, rfl⟩ := hsc ho hc
    exact ⟨b, by rwa [List.length_ofFn] at h1⟩
  -- before every gate, the wire `v` carries the constant false
  have hv0 (j : Fin D.gates.length) :
      ((D.gates.take j).foldl (elimStep 9) (st0, [], [])).1.getD v (.inl false) = .inl false := by
    obtain ⟨⟨t, ht, -⟩, -, -⟩ := elim_at 9 D.gates st0 j j.isLt
    have hlt : (v : ℕ) < st0.length := by simp [st0]
    rw [ht, List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
    simp
  -- so every gate of the normal form vanishes: at least three gates
  have hcount : 3 ≤ r.2.2.count true := by
    obtain ⟨-, fl, -, -, hfl, hfllen⟩ := elim_shape 9 D.gates (st0, [], [])
    have hofFn : r.2.2 = List.ofFn fun j : Fin D.gates.length => r.2.2.getD j false := by
      apply List.ext_getElem (by simp [r, hfl, hfllen]) fun k h1 _ => ?_
      rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h1]
    rw [hofFn, List.count_ofFn]
    refine hv.trans ((Set.ncard_le_ncard fun j hj => ?_).trans (Set.ncard_coe_finset _).le)
    simp only [Set.mem_ofPred_eq, List.get_eq_getElem] at hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rcases hj with hj | ⟨i, hi, hio, hj⟩
    · exact (hcol j v false (hv0 j) hj).1
    · obtain ⟨⟨t, ht, htl⟩, hagree, -⟩ := elim_at 9 D.gates st0 j j.isLt
      by_cases hij : (i : ℕ) < j
      · obtain ⟨b, hb⟩ := (hcol i v false (hv0 i) hi).2 hio rfl
        exact (hcol j _ b ((hagree (10 + i) (by simp [st0]; omega)).symm.trans hb) hj).1
      · have hlen : ((D.gates.take j).foldl (elimStep 9) (st0, [], [])).1.length ≤ 10 + i := by
          rw [ht, List.length_append, htl, List.length_ofFn]; omega
        exact (hcol j _ false (List.getD_eq_default _ _ hlen) hj).1
  -- the simplified circuit has fan-in two and at most 15 gates
  have hfan : ∀ g ∈ r.2.1, g.op ∈ ({.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    (hinv fun _ => false).2.1
  have hsize : r.2.1.length ≤ 15 := by
    have hcnt : r.2.1.length + r.2.2.count true = 0 + 0 + D.gates.length :=
      (hinv fun _ => false).2.2.1
    have : D.gates.length ≤ 18 := hD18
    omega
  -- and through the symbol of the output of `D` it computes pv
  have hsem (y : Fin 9 → Bool) :
      val (r.2.1.foldl step (List.ofFn y)) (r.1.getD D.output (.inl false)) =
        (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5) y := by
    let x : Fin 10 → Bool := fun i => if i = v then false else (List.ofFn y).getD (σ v i) false
    have hx : st0.map (val (([] : List Gate).foldl step (List.ofFn y))) = List.ofFn x := by
      simp [st0, x, apply_ite, val]
    have h : r.1.map (val (r.2.1.foldl step (List.ofFn y))) = D.gates.foldl step (List.ofFn x) := by
      rw [← hx]; exact (hinv y).2.2.2
    have hy : List.ofFn y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8] := by
      simp [List.ofFn_succ]
    have hy' : ![y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8] = y := by
      funext i; fin_cases i <;> rfl
    have hσy := hσ v (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
    rw [hy', ← hy] at hσy
    calc _ = (r.1.map (val (r.2.1.foldl step (List.ofFn y)))).getD D.output false :=
          (List.getD_map r.1 (.inl false) (val _)).symm
      _ = D.eval (List.ofFn x) := by rw [h]; rfl
      _ = _ := (hDC _).trans (hC _)
      _ = _ := hσy
  -- a constant output would make pv constant; otherwise the simplified circuit computes pv
  cases ho : r.1.getD D.output (.inl false) with
  | inl b =>
    have h0 := hsem fun _ => false
    have h1 := hsem fun _ => true
    rw [ho] at h0 h1
    exact absurd (h0.symm.trans h1) (by decide)
  | inr k =>
    exact hPv ⟨⟨r.2.1, k⟩, hfan, hsize, fun y => by have h := hsem y; rw [ho] at h; exact h⟩
