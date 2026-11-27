import Mathlib
import PEqualNP.Defs

-- A cut of L-meta-5282 into two moves on circuits, glued by a proof in this file.
-- h1 (constant move): every fan-in-two AND/OR circuit for a graph's edge function has a
--   no-larger one in which no AND gate is true at the all-false input.
-- h2 (singleton move, the core): on graphs with no triangle and no 4-cycle, a circuit whose AND
--   gates are false at the all-false input has a no-larger one whose AND gates are false at
--   every input with at most one true variable.
-- Proved here: every edge function has a fan-in-two AND/OR circuit (one AND per edge, an OR
-- chain), hence a least one; the two moves keep it least.
theorem PEqualNP.Outside.R_meta_5282_2
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
        D.size ≤ C.size ∧
        ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[k]? = some g →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (D.wires (List.ofFn (fun _ : Fin n => false))).getD (n + k) false = false)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) →
      (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (C.wires (List.ofFn (fun _ : Fin n => false))).getD (n + k) false = false) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
        D.size ≤ C.size ∧
        ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[k]? = some g →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ U : Finset (Fin n), U.card ≤ 1 →
          (D.wires (List.ofFn (fun i : Fin n => decide (i ∈ U)))).getD (n + k) false = false) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ (∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x4 x10) ∧ (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x12 : Fin x1 → Bool), x10.eval (List.ofFn x12) = x4 x12) → x9.size ≤ x10.size) ∧ x6 x9 := by
  intro n G inst
  dsimp only
  intro htri hc4
  classical
  have gA : ∀ (l l' : List Bool) (i : ℕ), i < l.length → (l ++ l').getD i false = l.getD i false := by
    intro l l' i h; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have gL : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b; simp [List.getD_eq_getElem?_getD]
  let stp : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let blk : ℕ → (ℕ × ℕ) × ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun m q =>
    [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [q.1.1, q.1.2]⟩,
     ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [m + 1 + 2 * q.2, m + 2 * q.2]⟩]
  -- folding the blocks of the edges `rest`, numbered from `t`, onto the wires `w`
  have key : ∀ (m : ℕ) (y : List Bool), y.length = m → ∀ (rest : List (ℕ × ℕ)) (t : ℕ)
      (w : List Bool), w.length = m + 1 + 2 * t → (∀ p ∈ rest, p.1 < m ∧ p.2 < m) →
      (∀ i < m, w.getD i false = y.getD i false) →
      (List.foldl stp w ((rest.zipIdx t).flatMap (blk m))).getD (m + 2 * (t + rest.length)) false =
        (w.getD (m + 2 * t) false || rest.any (fun p => y.getD p.1 false && y.getD p.2 false)) ∧
      (List.foldl stp w ((rest.zipIdx t).flatMap (blk m))).length = m + 1 + 2 * (t + rest.length) := by
    intro m y hym rest
    induction rest with
    | nil =>
      intro t w hw _ _
      simp [hw]
    | cons p rest ih =>
      intro t w hw hp hy
      obtain ⟨hp1, hp2⟩ := hp p (by simp)
      have hstep : ((p :: rest).zipIdx t).flatMap (blk m) =
          blk m (p, t) ++ (rest.zipIdx (t + 1)).flatMap (blk m) := by
        rw [List.zipIdx_cons, List.flatMap_cons]
      let w1 := stp w ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p.1, p.2]⟩
      let w2 := stp w1 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [m + 1 + 2 * t, m + 2 * t]⟩
      have hfold : List.foldl stp w (blk m (p, t)) = w2 := rfl
      have hl1 : w1.length = m + 2 + 2 * t := by simp [w1, stp, hw]; omega
      have hl2 : w2.length = m + 1 + 2 * (t + 1) := by simp [w2, stp, hl1]; omega
      have v1 : w1.getD (m + 1 + 2 * t) false = (y.getD p.1 false && y.getD p.2 false) := by
        have e : m + 1 + 2 * t = w.length := by omega
        simp only [w1, stp]
        rw [e, gL, ← hy _ hp1, ← hy _ hp2]
        change List.all (List.map (fun i => w.getD i false) [p.1, p.2]) id = _
        simp
      have v0 : w1.getD (m + 2 * t) false = w.getD (m + 2 * t) false := by
        simp only [w1, stp]; exact gA _ _ _ (by omega)
      have v2 : w2.getD (m + 2 * (t + 1)) false =
          ((y.getD p.1 false && y.getD p.2 false) || w.getD (m + 2 * t) false) := by
        have e : m + 2 * (t + 1) = w1.length := by omega
        simp only [w2, stp]
        rw [e, gL, ← v1, ← v0]
        change List.any (List.map (fun i => w1.getD i false) [m + 1 + 2 * t, m + 2 * t]) id = _
        simp
      have hy2 : ∀ i < m, w2.getD i false = y.getD i false := by
        intro i hi
        simp only [w2, stp]
        rw [gA _ _ _ (by omega)]
        simp only [w1, stp]
        rw [gA _ _ _ (by omega)]
        exact hy i hi
      obtain ⟨ihv, ihl⟩ := ih (t + 1) w2 hl2 (fun q hq => hp q (by simp [hq])) hy2
      rw [hstep, List.foldl_append, hfold]
      have e1 : m + 2 * (t + (p :: rest).length) = m + 2 * (t + 1 + rest.length) := by
        simp only [List.length_cons]; ring
      have e2 : m + 1 + 2 * (t + (p :: rest).length) = m + 1 + 2 * (t + 1 + rest.length) := by
        simp only [List.length_cons]; ring
      refine ⟨?_, ?_⟩
      · rw [e1, ihv, v2]
        simp only [List.any_cons]
        cases (y.getD p.1 false && y.getD p.2 false) <;>
          cases w.getD (m + 2 * t) false <;> simp
      · rw [e2, ihl]
  -- the circuit: a false OR gate, then for each edge an AND and an OR into the running OR
  let L : List (ℕ × ℕ) := ((Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2).toList).map
    (fun p => (p.1.val, p.2.val))
  have hLb : ∀ p ∈ L, p.1 < n ∧ p.2 < n := by
    intro p hp
    simp only [L, List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    exact ⟨q.1.2, q.2.2⟩
  let E : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :: (L.zipIdx 0).flatMap (blk n), n + 2 * L.length⟩
  have hEm : PEqualNP.MetaComplexity.Monotone2 E := by
    intro g hg
    simp only [E, List.mem_cons, List.mem_flatMap] at hg
    rcases hg with rfl | ⟨q, _, hq⟩
    · simp
    · simp only [blk, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp
  have hEc : ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
    intro x
    have hy : (List.ofFn x).length = n := List.length_ofFn
    have hgx : ∀ i : Fin n, (List.ofFn x).getD i.val false = x i := by
      intro i; simp [List.getD_eq_getElem?_getD]
    have w0 : stp (List.ofFn x) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = List.ofFn x ++ [false] := by
      rfl
    obtain ⟨kv, _⟩ := key n (List.ofFn x) hy L 0 (List.ofFn x ++ [false]) (by simp [hy]) hLb
      (fun i hi => gA _ _ _ (by omega))
    have ev : E.eval (List.ofFn x) =
        (List.foldl stp (stp (List.ofFn x) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
          ((L.zipIdx 0).flatMap (blk n))).getD (n + 2 * (0 + L.length)) false := by
      simp only [zero_add]; rfl
    rw [ev, w0, kv]
    have z : (List.ofFn x ++ [false]).getD (n + 2 * 0) false = false := by
      have h0 := gL (List.ofFn x) false
      simpa using h0
    rw [z, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    simp only [L, List.any_map, List.any_eq_true, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and, Function.comp_apply, Bool.and_eq_true, hgx, Prod.exists]
  -- a least circuit
  have hex : ∃ k : ℕ, ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) ∧ C.size = k :=
    ⟨_, E, hEm, hEc, rfl⟩
  obtain ⟨C0, hm0, hc0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) → Nat.find hex ≤ D.size :=
    fun D hm hc => Nat.find_min' hex ⟨D, hm, hc, rfl⟩
  obtain ⟨C1, hm1, hc1, hs1, hz1⟩ := h1 n G C0 hm0 hc0
  obtain ⟨C2, hm2, hc2, hs2, hp2⟩ := h2 n G htri hc4 C1 hm1 hc1 hz1
  refine ⟨C2, hm2, hc2, fun D hm hc => ?_, hp2⟩
  have := hmin D hm hc
  omega
