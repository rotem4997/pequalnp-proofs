import PEqualNP.MetaComplexity.Helpers.RunPQ2h

/-!
# The q2 side, stage I (part 1): the two-point lemma and status computations

Conjecture until the checker accepts. `pq2i_diff`: values of a clean list at two points differ
only on a set `T` closed under the readers (paper (1) of the q2-side argument, "values equal off a cone").
`pq2i_st_*`: what the cleaning at one fixed input makes of an OR, NOT or AND gate whose operands
have a given status.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- Two points whose values differ at a wire: the set `T` of differing wires is closed under
the readers (every gate reading a wire of `T` is in `T` or has equal values at the two points). -/
theorem pq2i_diff (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (x x' : Fin k → Bool)
    (T : ℕ → Prop)
    (hin : ∀ (w : ℕ), w < k → vl gs x w ≠ vl gs x' w → T w)
    (hstep : ∀ (t : ℕ) (g : Gate), gs[t]? = some g → (∃ a ∈ g.inputs, T a) →
      vl gs x (k + t) ≠ vl gs x' (k + t) → T (k + t)) :
    ∀ w, vl gs x w ≠ vl gs x' w → T w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < k
    · exact hin w hwk hw
    · obtain ⟨t, rfl⟩ : ∃ t, w = k + t := ⟨w - k, by omega⟩
      cases ht : gs[t]? with
      | none =>
        exfalso
        have hl : gs.length ≤ t := List.getElem?_eq_none_iff.1 ht
        apply hw
        rw [vl_beyond gs x _ (by omega), vl_beyond gs x' _ (by omega)]
      | some g =>
        apply hstep t g ht _ hw
        by_contra hno
        push_neg at hno
        apply hw
        rw [vl_gate gs hcl x t g ht, vl_gate gs hcl x' t g ht]
        congr 1
        apply List.map_congr_left
        intro a ha
        by_contra hne
        exact hno a ha (ih a ((hcl t g ht).lt a ha) hne)

/-- An OR gate with an operand of value true at a point has value true. -/
theorem pq2i_vl_or_true (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (x : Fin k → Bool) (t : ℕ)
    (g : Gate) (ht : gs[t]? = some g) (hop : g.op = GateOp.or) (a : ℕ) (ha : a ∈ g.inputs)
    (hv : vl gs x a = true) : vl gs x (k + t) = true := by
  rw [vl_gate gs hcl x t g ht, hop]
  rcases hcl t g ht with ⟨h1, -⟩ | ⟨-, j, l, -, -, hin⟩
  · rw [hop] at h1; cases h1
  · rw [hin] at ha ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [GateOp.eval, hv]


/-! ## Statuses -/

/-- A binary gate: the status is what `simplify` makes of the operand statuses. -/
theorem pq2i_st_bin (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∃ a a', g.inputs = [a, a'] ∧
      stF n gs i b (n + 1 + p) =
        (simplify g.op (n + pq2E n gs i b p) [stF n gs i b a, stF n gs i b a']).2 := by
  rcases hcl p g hp with ⟨h1, -⟩ | ⟨-, j, l, -, -, hin⟩
  · rcases hop with h | h <;> rw [h] at h1 <;> cases h1
  · refine ⟨j, l, hin, ?_⟩
    have := (pq2_emit n gs hcl i b p g hp).1
    rw [hin] at this
    simpa using this

/-- An OR gate with an operand of status `true` has status `true`. -/
theorem pq2i_st_or_true (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hop : g.op = GateOp.or) (a : ℕ)
    (ha : a ∈ g.inputs) (hs : stF n gs i b a = Stat.const true) :
    stF n gs i b (n + 1 + p) = Stat.const true := by
  obtain ⟨c, c', hin, hst⟩ := pq2i_st_bin n gs hcl i b p g hp (Or.inr hop)
  rw [hst, hop]
  rw [hin] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h0 | h0
  · rw [h0] at hs
    rw [hs]
    cases h : stF n gs i b c' with
    | const d => simp [simplify, simpOr]
    | wire k => simp [simplify, simpOr]
  · rw [h0] at hs
    rw [hs]
    cases h : stF n gs i b c with
    | const d => simp [simplify, simpOr]
    | wire k => simp [simplify, simpOr]

/-- An OR gate whose one operand has status `false` takes the status of the other operand. -/
theorem pq2i_st_or_false (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hop : g.op = GateOp.or) (a a' : ℕ)
    (hin : g.inputs = [a, a'] ∨ g.inputs = [a', a]) (hs : stF n gs i b a = Stat.const false) :
    stF n gs i b (n + 1 + p) = stF n gs i b a' := by
  obtain ⟨c, c', hin', hst⟩ := pq2i_st_bin n gs hcl i b p g hp (Or.inr hop)
  rw [hst, hop]
  rcases hin with h | h <;> rw [h] at hin' <;> simp only [List.cons.injEq, and_true] at hin' <;>
    obtain ⟨rfl, rfl⟩ := hin'
  · rw [hs]
    cases h : stF n gs i b a' with
    | const d => simp [simplify, simpOr]
    | wire k => simp [simplify, simpOr]
  · rw [hs]
    cases h : stF n gs i b a' with
    | const d => simp [simplify, simpOr]
    | wire k => simp [simplify, simpOr]

/-- An OR gate with an operand of wire status is not of status `false`. -/
theorem pq2i_st_or_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hop : g.op = GateOp.or) (a : ℕ)
    (ha : a ∈ g.inputs) (k : ℕ) (hs : stF n gs i b a = Stat.wire k) :
    stF n gs i b (n + 1 + p) ≠ Stat.const false := by
  obtain ⟨c, c', hin, hst⟩ := pq2i_st_bin n gs hcl i b p g hp (Or.inr hop)
  rw [hst, hop]
  rw [hin] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h0 | h0
  · rw [h0] at hs
    rw [hs]
    cases h : stF n gs i b c' with
    | const d => cases d <;> simp [simplify, simpOr]
    | wire k => simp [simplify, simpOr]
  · rw [h0] at hs
    rw [hs]
    cases h : stF n gs i b c with
    | const d => cases d <;> simp [simplify, simpOr]
    | wire k => simp [simplify, simpOr]

/-- A binary gate with both operands of constant status has constant status. -/
theorem pq2i_st_const2 (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a a' : ℕ) (hin : g.inputs = [a, a']) (c c' : Bool) (hs : stF n gs i b a = Stat.const c)
    (hs' : stF n gs i b a' = Stat.const c') : IsC n gs i b (n + 1 + p) := by
  obtain ⟨d, d', hin', hst⟩ := pq2i_st_bin n gs hcl i b p g hp hop
  rw [hin] at hin'
  simp only [List.cons.injEq, and_true] at hin'
  obtain ⟨rfl, rfl⟩ := hin'
  rcases hop with h | h
  · exact ⟨c && c', by rw [hst, hs, hs', h]; simp [simplify, simpAnd]⟩
  · exact ⟨c || c', by rw [hst, hs, hs', h]; simp [simplify, simpOr]⟩

/-- A NOT gate on an operand of constant status has constant status. -/
theorem pq2i_st_not (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hop : g.op = GateOp.not) (a : ℕ)
    (hin : g.inputs = [a]) (c : Bool) (hs : stF n gs i b a = Stat.const c) :
    IsC n gs i b (n + 1 + p) := by
  have := (pq2_emit n gs hcl i b p g hp).1
  rw [hin, hop] at this
  simp only [List.map_cons, List.map_nil, hs] at this
  exact ⟨!c, by rw [this]; simp [simplify, simpNot]⟩

/-- A gate of constant status reads a constant. -/
theorem pq2i_rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (t : ℕ) (g : Gate) (ht : gs[t]? = some g) (c : Bool)
    (hs : stF n gs i b (n + 1 + t) = Stat.const c) : RC n gs i b t := by
  by_contra hn
  have := pq2_new_wire n gs hcl i b t g ht hn
  rw [hs] at this
  cases this

/-- The input that is `i.succAbove j` has status the wire `j`. -/
theorem pq2i_st_succAbove (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (j : Fin n) :
    stF n gs i b ((i.succAbove j : Fin (n + 1)) : ℕ) = Stat.wire (j : ℕ) := by
  show (elim n gs (statAt n i b, [])).1.getD (i.succAbove j) (Stat.const false) = _
  rw [elim_getD n _ _ gs _ (by
    show ((i.succAbove j : Fin (n + 1)) : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact (i.succAbove j).isLt)]
  exact statAt_above n i b j

/-- An input wire (below `n + 1`) of constant status is the fixed input. -/
theorem pq2i_input_const (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ)
    (ha : a < n + 1) (c : Bool) (hs : stF n gs i b a = Stat.const c) : a = (i : ℕ) := by
  by_contra hne
  obtain ⟨k, -, hk⟩ := st_other n gs i b ⟨a, ha⟩ (fun h => hne (by simpa using congrArg Fin.val h))
  have : stF n gs i b a = Stat.wire k := hk
  rw [hs] at this
  cases this


/-! ## From source gates to saved gates of the emitted list -/

/-- A binary source gate that reads no constant emits, so distinct such positions land apart. -/
theorem pq2i_E_ne (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p p' : ℕ) (g g' : Gate) (hp : gs[p]? = some g) (hp' : gs[p']? = some g')
    (hn : ¬ RC n gs i b p) (hn' : ¬ RC n gs i b p')
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hop' : g'.op = GateOp.and ∨ g'.op = GateOp.or)
    (hpp : p ≠ p') : pq2E n gs i b p ≠ pq2E n gs i b p' := by
  have emits : ∀ (q : ℕ) (h : Gate), gs[q]? = some h → ¬ RC n gs i b q →
      (h.op = GateOp.and ∨ h.op = GateOp.or) →
      ∃ h', (simplify h.op (n + pq2E n gs i b q) (h.inputs.map (stF n gs i b))).1 = some h' := by
    intro q h hq hnq hoq
    obtain ⟨a, a', hin, -⟩ := pq2i_st_bin n gs hcl i b q h hq hoq
    have hw := pq2_not_rc_wire n gs i b q h hq hnq
    obtain ⟨j1, h1⟩ := hw a (by rw [hin]; simp)
    obtain ⟨j2, h2⟩ := hw a' (by rw [hin]; simp)
    rw [hin]
    simp only [List.map_cons, List.map_nil, h1, h2]
    rcases hoq with h0 | h0
    · exact ⟨⟨GateOp.and, [j1, j2]⟩, by rw [h0]; simp [simplify, simpAnd]⟩
    · exact ⟨⟨GateOp.or, [j1, j2]⟩, by rw [h0]; simp [simplify, simpOr]⟩
  rcases Nat.lt_or_gt_of_ne hpp with hlt | hlt
  · obtain ⟨h', hh'⟩ := emits p g hp hn hop
    exact (pq2_E_lt n gs hcl i b p p' g hp h' hh' hlt).ne
  · obtain ⟨h', hh'⟩ := emits p' g' hp' hn' hop'
    exact (pq2_E_lt n gs hcl i b p' p g' hp' h' hh' hlt).ne'

/-- A binary source gate that reads no constant, one of whose operands has status the wire `j`,
is a gate of the emitted list that reads the input `j`, hence reads a constant at `j := c`. -/
theorem pq2i_rc_pass (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 2) gs) (i : Fin (n + 2))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hn : ¬ RC (n + 1) gs i b p)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (a a' : ℕ) (hin : g.inputs = [a, a'])
    (j : Fin (n + 1)) (hj : stF (n + 1) gs i b a = Stat.wire (j : ℕ) ∨
      stF (n + 1) gs i b a' = Stat.wire (j : ℕ)) (c : Bool) :
    RC n (passG (n + 1) gs i b) j c (pq2E (n + 1) gs i b p) := by
  have hw := pq2_not_rc_wire (n + 1) gs i b p g hp hn
  obtain ⟨j1, h1⟩ := hw a (by rw [hin]; simp)
  obtain ⟨j2, h2⟩ := hw a' (by rw [hin]; simp)
  obtain ⟨-, hk⟩ := pq2_kept_bin (n + 1) gs hcl i b p g hp a a' hin hop j1 j2 h1 h2
  refine ⟨_, hk, (j : ℕ), ?_, c, stF_self n _ j c⟩
  rcases hj with h | h
  · rw [h1] at h; simp only [Stat.wire.injEq] at h; subst h; simp
  · rw [h2] at h; simp only [Stat.wire.injEq] at h; subst h; simp


/-! ## The double restriction is not constant, and the finish -/

theorem pq2i_nc2 {m : ℕ} (G : SimpleGraph (Fin m)) (q0 q1 q2 q3 q4 q5 : Fin m)
    (r : r4Run G q0 q1 q2 q3 q4 q5) :
    ∃ x y : Fin m → Bool,
      F G ∅ (Function.update (Function.update x q2 true) q1 false) ≠
        F G ∅ (Function.update (Function.update y q2 true) q1 false) := by
  have nd := r.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h12', h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := nd
  have A23 : G.Adj q2 q3 := (r.h2 q3).2 (Or.inr rfl)
  refine ⟨fun _ => false, fun i => decide (i = q3), ?_⟩
  have v1 : F G ∅ (Function.update (Function.update (fun _ : Fin m => false) q2 true)
      q1 false) = false := by
    apply F_false_of {q2}
    · intro i hi
      by_cases h : i = q1
      · simp [Function.update_apply, h] at hi
      · by_cases h' : i = q2
        · simp [h']
        · simp [Function.update_apply, h, h'] at hi
    · simp
    · intro i j hij hi hj
      simp at hi hj; subst hi; subst hj; exact G.loopless.irrefl _ hij
  have v2 : F G ∅ (Function.update (Function.update (fun i : Fin m => decide (i = q3))
      q2 true) q1 false) = true := by
    apply F_true_of q2 q3 A23
    · simp [Function.update_apply, Ne.symm h12']
    · simp [Function.update_apply, Ne.symm h13, Ne.symm h23]
  rw [v1, v2]; simp

/-- The finish: three saved gates at `x_q2 := 1` and two saved gates of the emitted list at
`x_q1 := 0` give outcome (q-d) shape: a circuit for the double restriction with five fewer gates. -/
theorem pq2i_finish (N : ℕ) (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (hnc1 : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q2 true) ≠ F G ∅ (Function.update y q2 true))
    (j : Fin (N + 1)) (hj : q2.succAbove j = q1) (S1 S2 : Finset ℕ)
    (hS1 : ∀ p ∈ S1, RC (N + 1) gs q2 true p)
    (hS2 : ∀ p ∈ S2, RC N (passG (N + 1) gs q2 true) j false p)
    (c1 : 3 ≤ S1.card) (c2 : 2 ≤ S2.card) :
    ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (N + 2)
      (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s' := by
  have hnc2 := pq2i_nc2 G q0 q1 q2 q3 q4 q5 r
  rw [← hj] at hnc2
  obtain ⟨s', hs', hc⟩ := pq2_save_two N (F G ∅) gs o L.hcl L.hev q2 j true false hnc1 hnc2 S1 S2 hS1 hS2
  rw [hj] at hc
  exact ⟨s', by omega, hc⟩


/-! ## The two-point argument (paper (1)) -/

/-- The output is not a wire of constant status when the restriction is not constant. -/
theorem pq2i_ne_out (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (a : ℕ) (c : Bool) (hs : stF n gs i b a = Stat.const c) : o ≠ a := by
  intro e
  obtain ⟨x, y, hxy⟩ := hnc
  rw [← e] at hs
  exact hxy ((restr_const L.hcl L.hev i b c hs x).trans (restr_const L.hcl L.hev i b c hs y).symm)

/-- Two points that differ at `q2` only, with `x_q1` true at both: F is false at the first and
true at the second; the set `T` of wires with differing values is closed under the readers. -/
theorem pq2i_cone (N : ℕ) (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (T : ℕ → Prop) (hTq2 : T (q2 : ℕ))
    (hstep : ∀ (t : ℕ) (g : Gate), gs[t]? = some g → (∃ a ∈ g.inputs, T a) →
      vl gs (fun i : Fin (N + 2) => decide (i = q1)) (N + 2 + t) ≠
        vl gs (fun i : Fin (N + 2) => decide (i = q1 ∨ i = q2)) (N + 2 + t) → T (N + 2 + t))
    (hout : ¬ T o) : False := by
  have nd := r.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h12', h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := nd
  have A12 : G.Adj q1 q2 := (r.h1 q2).2 (Or.inr rfl)
  have pt3 : F G ∅ (fun i => decide (i = q1)) = false := by
    apply F_false_of {q1}
    · intro i hi; simpa using hi
    · simp
    · intro i j hij hi hj
      simp at hi hj; subst hi; subst hj; exact G.loopless.irrefl _ hij
  have pt4 : F G ∅ (fun i => decide (i = q1 ∨ i = q2)) = true :=
    F_true_of q1 q2 A12 (by simp) (by simp)
  have hdiff : vl gs (fun i : Fin (N + 2) => decide (i = q1)) o ≠
      vl gs (fun i : Fin (N + 2) => decide (i = q1 ∨ i = q2)) o := by
    rw [L.hev, L.hev, pt3, pt4]; simp
  refine hout (pq2i_diff (N + 2) gs L.hcl _ _ T ?_ hstep o hdiff)
  intro w hw hne
  rw [vl_input gs _ w hw, vl_input gs _ w hw] at hne
  have : (⟨w, hw⟩ : Fin (N + 2)) = q2 := by
    by_contra h
    apply hne
    simp [h]
  have : w = (q2 : ℕ) := by rw [← this]
  rw [this]; exact hTq2

/-- (1) of the paper, the first form: the sole reader of `x_q2` is `OR(x_q1, x_q2)`. Empty. -/
theorem pq2i_M1 (N : ℕ) (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (hnc1 : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q2 true) ≠ F G ∅ (Function.update y q2 true))
    (o2 : ℕ) (go2 : Gate) (hg : gs[o2]? = some go2) (hop : go2.op = GateOp.or)
    (h1 : (q1 : ℕ) ∈ go2.inputs) (h2 : (q2 : ℕ) ∈ go2.inputs)
    (hrq2 : ∀ t, Reads gs t q2 → t = o2) : False := by
  refine pq2i_cone N G q0 q1 q2 q3 q4 q5 r gs o L (fun w => w = (q2 : ℕ)) rfl ?_ ?_
  · intro t g ht ⟨a, ha, hT⟩ hdiff
    have hto : t = o2 := hrq2 t ⟨g, ht, by rw [hT] at ha; exact ha⟩
    subst hto
    rw [hg] at ht; cases ht
    exfalso
    apply hdiff
    have v1 := pq2i_vl_or_true (N + 2) gs L.hcl (fun i : Fin (N + 2) => decide (i = q1)) t go2 hg hop
      q1 h1 (by rw [vl_input gs _ q1 q1.isLt]; simp)
    have v2 := pq2i_vl_or_true (N + 2) gs L.hcl (fun i : Fin (N + 2) => decide (i = q1 ∨ i = q2))
      t go2 hg hop q1 h1 (by rw [vl_input gs _ q1 q1.isLt]; simp)
    rw [v1, v2]
  · intro h
    exact pq2i_ne_out (N + 1) (F G ∅) gs o L q2 true hnc1 q2 true (stF_self _ _ _ _) h

/-- (1) of the paper, the second form: the sole reader `o2` of `x_q2` is read only by
`OR(x_q1, o2)`. Empty. -/
theorem pq2i_M2 (N : ℕ) (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (hnc1 : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q2 true) ≠ F G ∅ (Function.update y q2 true))
    (o2 : ℕ) (go2 : Gate) (hg : gs[o2]? = some go2) (hop : go2.op = GateOp.or)
    (h2 : (q2 : ℕ) ∈ go2.inputs)
    (hrq2 : ∀ t, Reads gs t q2 → t = o2)
    (p : ℕ) (gp : Gate) (hgp : gs[p]? = some gp) (hpop : gp.op = GateOp.or)
    (hp1 : (q1 : ℕ) ∈ gp.inputs) (hpo : (N + 2 + o2) ∈ gp.inputs)
    (hrd : ∀ t, Reads gs t (N + 2 + o2) → t = p) : False := by
  refine pq2i_cone N G q0 q1 q2 q3 q4 q5 r gs o L (fun w => w = (q2 : ℕ) ∨ w = N + 2 + o2)
    (Or.inl rfl) ?_ ?_
  · intro t g ht ⟨a, ha, hT⟩ hdiff
    rcases hT with hT | hT
    · have hto : t = o2 := hrq2 t ⟨g, ht, by rw [hT] at ha; exact ha⟩
      subst hto
      exact Or.inr rfl
    · have hto : t = p := hrd t ⟨g, ht, by rw [hT] at ha; exact ha⟩
      subst hto
      rw [hgp] at ht; cases ht
      exfalso
      apply hdiff
      have v1 := pq2i_vl_or_true (N + 2) gs L.hcl (fun i : Fin (N + 2) => decide (i = q1)) t gp hgp
        hpop q1 hp1 (by rw [vl_input gs _ q1 q1.isLt]; simp)
      have v2 := pq2i_vl_or_true (N + 2) gs L.hcl (fun i : Fin (N + 2) => decide (i = q1 ∨ i = q2))
        t gp hgp hpop q1 hp1 (by rw [vl_input gs _ q1 q1.isLt]; simp)
      rw [v1, v2]
  · intro h
    rcases h with h | h
    · exact pq2i_ne_out (N + 1) (F G ∅) gs o L q2 true hnc1 q2 true (stF_self _ _ _ _) h
    · refine pq2i_ne_out (N + 1) (F G ∅) gs o L q2 true hnc1 (N + 2 + o2) true ?_ h
      exact pq2i_st_or_true (N + 1) gs L.hcl q2 true o2 go2 hg hop q2 h2 (stF_self _ _ _ _)

end PEqualNP.MetaComplexity.Helpers.RunAsm
