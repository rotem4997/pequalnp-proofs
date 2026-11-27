import PEqualNP.Library.SearchHelpers.TableauDefs

/-!
# Helpers: an accepting run satisfies the tableau formula

Helper module (proofs only, no statement may use it). One direction of the correctness of
`tableau`: if the code `c`, started on the input symbols `zs` followed by a witness of at most
`m` symbols `2` or `3`, halts within `T` steps with `[1]` on its output stack, then
`tableau c zs m T` is satisfiable (`sat_of_accepts`).

The assignment makes a variable true exactly when it describes the real run (`Cpl.asg`). The
variable numbering `uvar` is injective (`Cpl.uvar_inj`), so a true variable pins down the real
configuration; every implication clause then follows from the definition of `exec`. The only
invariants of the run that are needed are the number of stacks (`Cpl.len_run`) and the height
of the stacks (`Cpl.height`). No bound on the symbols, states or counters is needed in this
direction.
-/

namespace PEqualNP.Library.SearchHelpers.Tab

open PEqualNP.Library.Universal PEqualNP.Search

namespace Cpl

/-! ### The variable numbering is injective -/

/-- A power of two times an odd number determines both. -/
theorem pow_odd_inj (a : ℕ) :
    ∀ b u v : ℕ, 2 ^ a * (2 * u + 1) = 2 ^ b * (2 * v + 1) → a = b ∧ u = v := by
  induction a with
  | zero =>
    intro b u v h
    cases b with
    | zero =>
      rw [pow_zero, one_mul, one_mul] at h
      exact ⟨rfl, by omega⟩
    | succ b =>
      exfalso
      have e : 2 ^ (b + 1) * (2 * v + 1) = 2 * (2 ^ b * (2 * v + 1)) := by ring
      rw [e, pow_zero, one_mul] at h
      generalize 2 ^ b * (2 * v + 1) = Y at h
      omega
  | succ a ih =>
    intro b u v h
    cases b with
    | zero =>
      exfalso
      have e : 2 ^ (a + 1) * (2 * u + 1) = 2 * (2 ^ a * (2 * u + 1)) := by ring
      rw [e, pow_zero, one_mul] at h
      generalize 2 ^ a * (2 * u + 1) = Y at h
      omega
    | succ b =>
      have e1 : 2 ^ (a + 1) * (2 * u + 1) = 2 * (2 ^ a * (2 * u + 1)) := by ring
      have e2 : 2 ^ (b + 1) * (2 * v + 1) = 2 * (2 ^ b * (2 * v + 1)) := by ring
      rw [e1, e2] at h
      have h' := ih b u v (Nat.eq_of_mul_eq_mul_left (by norm_num) h)
      exact ⟨by rw [h'.1], h'.2⟩

/-- `uvar` is injective on all lists. -/
theorem uvar_inj : ∀ l l' : List ℕ, uvar l = uvar l' → l = l'
  | [], [], _ => rfl
  | [], b :: s, h => by
    exfalso
    have hpos : 0 < 2 ^ b * (2 * uvar s + 1) := by positivity
    simp only [uvar] at h
    exact absurd h hpos.ne
  | a :: r, [], h => by
    exfalso
    have hpos : 0 < 2 ^ a * (2 * uvar r + 1) := by positivity
    simp only [uvar] at h
    exact absurd h hpos.ne'
  | a :: r, b :: s, h => by
    simp only [uvar] at h
    obtain ⟨h1, h2⟩ := pow_odd_inj a b _ _ h
    rw [h1, uvar_inj r s h2]

/-! ### Cells of a stack -/

/-- The value of cell `j` from the top of a stack: `0` below the bottom, `s + 1` on symbol
`s`. -/
def cellOf (st : List ℕ) (j : ℕ) : ℕ := ((st[j]?).map (· + 1)).getD 0

theorem cellOf_zero (st : List ℕ) : cellOf st 0 = topIndex st := by
  cases st <;> simp [cellOf, topIndex]

theorem cellOf_cons_zero (a : ℕ) (st : List ℕ) : cellOf (a :: st) 0 = a + 1 := by
  simp [cellOf]

theorem cellOf_cons_succ (a : ℕ) (st : List ℕ) (j : ℕ) :
    cellOf (a :: st) (j + 1) = cellOf st j := by
  simp [cellOf]

theorem cellOf_tail (st : List ℕ) (j : ℕ) : cellOf st.tail j = cellOf st (j + 1) := by
  cases st <;> simp [cellOf]

theorem cellOf_eq_zero_iff (st : List ℕ) (j : ℕ) : cellOf st j = 0 ↔ st.length ≤ j := by
  by_cases hj : j < st.length
  · simp [cellOf, List.getElem?_eq_getElem hj]
    omega
  · have hj' : st.length ≤ j := by omega
    simp [cellOf, hj']

theorem cellOf_append_left (zs ws : List ℕ) (j : ℕ) (hj : j < zs.length) :
    cellOf (zs ++ ws) j = zs.getD j 0 + 1 := by
  simp [cellOf, List.getElem?_append_left hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]

theorem cellOf_append_right (zs ws : List ℕ) (j : ℕ) :
    cellOf (zs ++ ws) (zs.length + j) = cellOf ws j := by
  simp [cellOf, List.getElem?_append_right]

theorem cellOf_witness (w : List Bool) (j : ℕ) :
    cellOf (w.map fun b => cond b 3 2) j = 0 ∨ cellOf (w.map fun b => cond b 3 2) j = 3 ∨
      cellOf (w.map fun b => cond b 3 2) j = 4 := by
  unfold cellOf
  rw [List.getElem?_map]
  cases w[j]? with
  | none => simp
  | some b => cases b <;> simp

/-! ### Reading a list of stacks -/

theorem getD_of_le (S : List (List ℕ)) (k : ℕ) (h : S.length ≤ k) : S.getD k [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_set (S : List (List ℕ)) (k k' : ℕ) (x : List ℕ) :
    (S.set k x).getD k' [] = if k = k' ∧ k < S.length then x else S.getD k' [] := by
  by_cases hk : k = k'
  · subst hk
    by_cases hl : k < S.length
    · simp [List.getD_eq_getElem?_getD, hl]
    · have hl' : S.length ≤ k := by omega
      rw [ite_eq_right (by tauto), List.set_eq_of_length_le hl']
  · rw [ite_eq_right (by tauto)]
    simp [List.getD_eq_getElem?_getD, hk]

theorem getD_replicate (n k : ℕ) : (List.replicate n ([] : List ℕ)).getD k [] = [] := by
  by_cases hk : k < n
  · simp [List.getD_eq_getElem?_getD, hk]
  · exact getD_of_le _ _ (by simp; omega)

/-! ### One step of the machine -/

/-- A step runs the instruction at the code of the program counter. -/
theorem step_eq (P : List Instr) (cfg : Cfg) :
    step P cfg = exec (instrAt P (pcCode cfg.pc)) cfg.state cfg.stk := by
  obtain ⟨pc, v, S⟩ := cfg
  cases pc with
  | none => simp [step, pcCode, instrAt, exec]
  | some n =>
    simp only [step, pcCode, instrAt, List.getD_eq_getElem?_getD]
    cases P[n]? with
    | none => simp [exec]
    | some i => simp

theorem run_zero (c : Code) (input : List ℕ) : c.run input 0 = c.init input := rfl

theorem run_succ (c : Code) (input : List ℕ) (t : ℕ) :
    c.run input (t + 1) = exec (instrAt c.prog (pcCode (c.run input t).pc))
      (c.run input t).state (c.run input t).stk := by
  rw [← step_eq]
  exact Function.iterate_succ_apply' _ _ _

theorem pcCode_exec (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    pcCode (exec i v S).pc = nextCode i v := by
  cases i <;> rfl

theorem state_exec (i : Instr) (v : ℕ) (S : List (List ℕ)) (a : ℕ)
    (h : ∀ k, rdStack i = some k → a = topIndex (S.getD k [])) :
    (exec i v S).state = newState i v a := by
  cases i <;> simp_all [exec, newState, rdStack]

theorem exec_len (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    (exec i v S).stk.length = S.length := by
  cases i <;> simp [exec]

theorem stk_exec_keep (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ)
    (h : stackOp i k = .keep) : (exec i v S).stk.getD k [] = S.getD k [] := by
  cases i with
  | push k' tbl next =>
    have hk : k' ≠ k := by
      intro e
      simp [stackOp, e] at h
    simp [exec, hk]
  | pop k' tbl w next =>
    have hk : k' ≠ k := by
      intro e
      simp [stackOp, e] at h
    simp [exec, hk]
  | _ => rfl

theorem stk_exec_push (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ) (tbl : List ℕ)
    (hk : k < S.length) (h : stackOp i k = .push tbl) :
    (exec i v S).stk.getD k [] = tbl.getD v 0 :: S.getD k [] := by
  cases i with
  | push k' tbl' next =>
    by_cases e : k' = k
    · subst e
      simp only [stackOp, ite_true, Op.push.injEq] at h
      subst h
      simp [exec, hk]
    · simp [stackOp, e] at h
  | pop k' tbl' w next =>
    by_cases e : k' = k <;> simp [stackOp, e] at h
  | _ => simp [stackOp] at h

theorem stk_exec_pop (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ)
    (hk : k < S.length) (h : stackOp i k = .pop) :
    (exec i v S).stk.getD k [] = (S.getD k []).tail := by
  cases i with
  | push k' tbl' next =>
    by_cases e : k' = k <;> simp [stackOp, e] at h
  | pop k' tbl' w next =>
    by_cases e : k' = k
    · subst e
      simp [exec, hk]
    · simp [stackOp, e] at h
  | _ => simp [stackOp] at h

theorem exec_height (i : Instr) (v : ℕ) (S : List (List ℕ)) (n : ℕ)
    (h : ∀ k, (S.getD k []).length ≤ n) (k : ℕ) :
    ((exec i v S).stk.getD k []).length ≤ n + 1 := by
  have hk := h k
  cases i with
  | push k' tbl next =>
    have hk' := h k'
    simp only [exec]
    rw [getD_set]
    split_ifs <;> (try simp only [List.length_cons]) <;> omega
  | pop k' tbl w next =>
    have hk' := h k'
    simp only [exec]
    rw [getD_set]
    split_ifs <;> (try simp only [List.length_tail]) <;> omega
  | _ => exact Nat.le_succ_of_le hk

/-! ### Invariants of the run -/

theorem len_run (c : Code) (input : List ℕ) (t : ℕ) : (c.run input t).stk.length = c.nstk := by
  induction t with
  | zero => simp [run_zero, Code.init]
  | succ t ih => rw [run_succ, exec_len, ih]

theorem stk_init (c : Code) (input : List ℕ) (k : ℕ) :
    (c.run input 0).stk.getD k [] = if c.kin = k ∧ c.kin < c.nstk then input else [] := by
  rw [run_zero]
  simp only [Code.init]
  rw [getD_set, getD_replicate, List.length_replicate]

theorem height (c : Code) (input : List ℕ) (t k : ℕ) :
    ((c.run input t).stk.getD k []).length ≤ input.length + t := by
  induction t generalizing k with
  | zero =>
    rw [stk_init]
    split_ifs <;> simp
  | succ t ih =>
    rw [run_succ]
    exact exec_height _ _ _ _ ih k

/-! ### The assignment that describes the run -/

/-- The variable `x` describes the real run of `c` on `input`. -/
def Holds (c : Code) (input : List ℕ) (x : ℕ) : Prop :=
  ∃ t, x = vP t (pcCode (c.run input t).pc) ∨ x = vQ t (c.run input t).state ∨
    ∃ k j, x = vC t k j (cellOf ((c.run input t).stk.getD k []) j)

/-- The assignment: a variable is true exactly when it describes the real run. -/
noncomputable def asg (c : Code) (input : List ℕ) : Assignment :=
  fun x => @decide (Holds c input x) (Classical.propDecidable _)

theorem asg_iff (c : Code) (input : List ℕ) (x : ℕ) : asg c input x = true ↔ Holds c input x := by
  unfold asg
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem asg_vP (c : Code) (input : List ℕ) (t q : ℕ) :
    asg c input (vP t q) = true ↔ q = pcCode (c.run input t).pc := by
  rw [asg_iff]
  constructor
  · rintro ⟨t', h | h | ⟨k, j, h⟩⟩
    · simp only [vP] at h
      have h' := uvar_inj _ _ h
      simp only [List.cons.injEq, and_true, true_and] at h'
      obtain ⟨h1, rfl⟩ := h'
      exact h1
    · simp only [vP, vQ] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vP, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
  · rintro rfl
    exact ⟨t, Or.inl rfl⟩

theorem asg_vQ (c : Code) (input : List ℕ) (t v : ℕ) :
    asg c input (vQ t v) = true ↔ v = (c.run input t).state := by
  rw [asg_iff]
  constructor
  · rintro ⟨t', h | h | ⟨k, j, h⟩⟩
    · simp only [vP, vQ] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vQ] at h
      have h' := uvar_inj _ _ h
      simp only [List.cons.injEq, and_true, true_and] at h'
      obtain ⟨h1, rfl⟩ := h'
      exact h1
    · simp only [vQ, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
  · rintro rfl
    exact ⟨t, Or.inr (Or.inl rfl)⟩

theorem asg_vC (c : Code) (input : List ℕ) (t k j x : ℕ) :
    asg c input (vC t k j x) = true ↔ x = cellOf ((c.run input t).stk.getD k []) j := by
  rw [asg_iff]
  constructor
  · rintro ⟨t', h | h | ⟨k', j', h⟩⟩
    · simp only [vP, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vQ, vC] at h
      have h' := uvar_inj _ _ h
      simp at h'
    · simp only [vC] at h
      have h' := uvar_inj _ _ h
      simp only [List.cons.injEq, and_true, true_and] at h'
      obtain ⟨rfl, h1, rfl, rfl⟩ := h'
      exact h1
  · rintro rfl
    exact ⟨t, Or.inr (Or.inr ⟨k, j, rfl⟩)⟩

/-! ### Evaluating clauses -/

theorem eval_imp (σ : Assignment) (prem : List ℕ) (concl : ℕ)
    (h : (∀ x ∈ prem, σ x = true) → σ concl = true) : Clause.eval σ (imp prem concl) = true := by
  unfold Clause.eval imp
  rw [List.any_append, Bool.or_eq_true]
  by_cases hp : ∀ x ∈ prem, σ x = true
  · right
    simp [Literal.eval, h hp]
  · left
    push Not at hp
    obtain ⟨x, hx, hx'⟩ := hp
    rw [List.any_eq_true]
    refine ⟨(x, false), List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    simpa [Literal.eval] using hx'

theorem eval_neg (σ : Assignment) (x : ℕ) (h : ¬ σ x = true) :
    Clause.eval σ [(x, false)] = true := by
  simpa [Clause.eval, Literal.eval] using h

theorem eval_pos (σ : Assignment) (cl : Clause) (x : ℕ) (hx : (x, true) ∈ cl)
    (h : σ x = true) : Clause.eval σ cl = true := by
  unfold Clause.eval
  rw [List.any_eq_true]
  exact ⟨(x, true), hx, by simp [Literal.eval, h]⟩

/-! ### The three groups of clauses -/

theorem reads_ok (c : Code) (input : List ℕ) (t B : ℕ) (o : Option ℕ) (r : List ℕ × ℕ)
    (hr : r ∈ reads c.nstk B t o) (h3 : ∀ x ∈ r.1, asg c input x = true) (k : ℕ)
    (hk : o = some k) : r.2 = topIndex ((c.run input t).stk.getD k []) := by
  subst hk
  simp only [reads] at hr
  split_ifs at hr with hlt
  · simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨x, -, rfl⟩ := hr
    have h := (asg_vC c input t k 0 x).1 (h3 _ (by simp))
    rw [cellOf_zero] at h
    exact h
  · rw [List.mem_singleton] at hr
    subst hr
    rw [getD_of_le _ _ (by rw [len_run]; omega)]
    rfl

theorem step_ok (c : Code) (input : List ℕ) (t H B : ℕ) (hH : input.length + t ≤ H) :
    ∀ cl ∈ stepClauses c.nstk H B c.prog t, Clause.eval (asg c input) cl = true := by
  intro cl hcl
  simp only [stepClauses, List.mem_flatMap, List.mem_append, List.mem_range] at hcl
  obtain ⟨q, -, (hcl | hcl) | ⟨k, hk, hcl⟩⟩ := hcl
  · simp only [pcClauses, List.mem_map, List.mem_range] at hcl
    obtain ⟨v, -, rfl⟩ := hcl
    apply eval_imp
    intro hp
    have h1 := (asg_vP c input t q).1 (hp _ (by simp))
    have h2 := (asg_vQ c input t v).1 (hp _ (by simp))
    rw [asg_vP, run_succ, pcCode_exec, ← h1, ← h2]
  · simp only [stateClauses, List.mem_flatMap, List.mem_map, List.mem_range] at hcl
    obtain ⟨v, -, r, hr, rfl⟩ := hcl
    apply eval_imp
    intro hp
    have h1 := (asg_vP c input t q).1 (hp _ (by simp))
    have h2 := (asg_vQ c input t v).1 (hp _ (by simp))
    have h3 : ∀ x ∈ r.1, asg c input x = true := fun x hx => hp x (by simp [hx])
    rw [asg_vQ, run_succ, ← h1, ← h2]
    symm
    apply state_exec
    intro k hk
    exact reads_ok c input t B _ r hr h3 k hk
  · have hkS : k < (c.run input t).stk.length := by rw [len_run]; exact hk
    cases hop : stackOp (instrAt c.prog q) k with
    | keep =>
      rw [hop] at hcl
      simp only [cellClauses, List.mem_flatMap, List.mem_map, List.mem_range] at hcl
      obtain ⟨j, -, x, -, rfl⟩ := hcl
      apply eval_imp
      intro hp
      have h1 := (asg_vP c input t q).1 (hp _ (by simp))
      have h2 := (asg_vC c input t k j x).1 (hp _ (by simp))
      rw [asg_vC, run_succ, ← h1, stk_exec_keep _ _ _ _ hop]
      exact h2
    | push tbl =>
      rw [hop] at hcl
      simp only [cellClauses, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range] at hcl
      rcases hcl with ⟨v, -, rfl⟩ | ⟨j, -, x, -, rfl⟩
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        have h2 := (asg_vQ c input t v).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, ← h2, stk_exec_push _ _ _ _ _ hkS hop, cellOf_cons_zero]
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        have h2 := (asg_vC c input t k j x).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, stk_exec_push _ _ _ _ _ hkS hop, cellOf_cons_succ]
        exact h2
    | pop =>
      rw [hop] at hcl
      simp only [cellClauses, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range, List.mem_singleton] at hcl
      rcases hcl with ⟨j, -, x, -, rfl⟩ | rfl
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        have h2 := (asg_vC c input t k (j + 1) x).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, stk_exec_pop _ _ _ _ hkS hop, cellOf_tail]
        exact h2
      · apply eval_imp
        intro hp
        have h1 := (asg_vP c input t q).1 (hp _ (by simp))
        rw [asg_vC, run_succ, ← h1, stk_exec_pop _ _ _ _ hkS hop, eq_comm, cellOf_eq_zero_iff,
          List.length_tail]
        have hh := height c input t k
        omega

theorem init_ok (c : Code) (zs : List ℕ) (w : List Bool) (m H : ℕ) (hw : w.length ≤ m) :
    ∀ cl ∈ initClauses c zs m H,
      Clause.eval (asg c (zs ++ w.map fun b => cond b 3 2)) cl = true := by
  intro cl hcl
  simp only [initClauses, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with ((rfl | rfl) | ⟨k, hk, hcl⟩) | hcl
  · apply eval_imp
    intro _
    rw [asg_vP]
    rfl
  · apply eval_imp
    intro _
    rw [asg_vQ]
    rfl
  · split_ifs at hcl with hkin
    · simp at hcl
    · simp only [List.mem_map, List.mem_range] at hcl
      obtain ⟨j, -, rfl⟩ := hcl
      apply eval_imp
      intro _
      rw [asg_vC, stk_init, ite_eq_right (fun e => hkin e.1.symm)]
      simp [cellOf]
  · split_ifs at hcl with hkin
    · have hin : (c.run (zs ++ w.map fun b => cond b 3 2) 0).stk.getD c.kin [] =
          zs ++ w.map fun b => cond b 3 2 := by
        rw [stk_init, ite_eq_left ⟨rfl, hkin⟩]
      simp only [List.mem_append, List.mem_map, List.mem_range] at hcl
      rcases hcl with ((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
      · apply eval_imp
        intro _
        rw [asg_vC, hin, cellOf_append_left _ _ _ hj]
      · have hcell := cellOf_append_right zs (w.map fun b => cond b 3 2) j
        rcases cellOf_witness w j with h0 | h0 | h0
        · refine eval_pos _ _ (vC 0 c.kin (zs.length + j) 0) (by simp) ?_
          rw [asg_vC, hin, hcell, h0]
        · refine eval_pos _ _ (vC 0 c.kin (zs.length + j) 3) (by simp) ?_
          rw [asg_vC, hin, hcell, h0]
        · refine eval_pos _ _ (vC 0 c.kin (zs.length + j) 4) (by simp) ?_
          rw [asg_vC, hin, hcell, h0]
      · apply eval_imp
        intro hp
        have h1 := (asg_vC c _ 0 c.kin (zs.length + j) 0).1 (hp _ (by simp))
        rw [hin, eq_comm, cellOf_eq_zero_iff] at h1
        rw [asg_vC, hin, eq_comm, cellOf_eq_zero_iff]
        omega
      · apply eval_imp
        intro _
        rw [asg_vC, hin, eq_comm, cellOf_eq_zero_iff]
        simp only [List.length_append, List.length_map]
        omega
    · simp at hcl

theorem final_ok (c : Code) (input : List ℕ) (B T : ℕ) (h : c.outputsWithin input T [1]) :
    ∀ cl ∈ finalClauses c B T, Clause.eval (asg c input) cl = true := by
  obtain ⟨hpc, hout⟩ := h
  intro cl hcl
  simp only [finalClauses, List.mem_append, List.mem_map, List.mem_range] at hcl
  rcases hcl with ⟨p, -, rfl⟩ | hcl
  · apply eval_neg
    rw [asg_vP, hpc]
    simp [pcCode]
  · split_ifs at hcl with hk
    · simp only [List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_map,
        List.mem_range] at hcl
      rcases hcl with (rfl | ⟨x, -, hx⟩) | ⟨x, -, rfl⟩
      · apply eval_neg
        rw [asg_vC, hout]
        simp [cellOf]
      · split_ifs at hx with hx1
        · simp at hx
        · rw [List.mem_singleton] at hx
          subst hx
          apply eval_neg
          rw [asg_vC, hout]
          simp [cellOf, hx1]
      · apply eval_neg
        rw [asg_vC, hout]
        simp [cellOf]
    · exfalso
      rw [getD_of_le _ _ (by rw [len_run]; omega)] at hout
      simp at hout

end Cpl

/-- An accepting run gives a satisfying assignment of the tableau formula. The hypothesis `hz`
is not used in this direction. -/
theorem sat_of_accepts (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4)
    (w : List Bool) (hw : w.length ≤ m)
    (h : c.outputsWithin (zs ++ w.map (fun b => cond b 3 2)) T [1]) :
    PEqualNP.Search.Satisfiable (tableau c zs m T) := by
  refine ⟨Cpl.asg c (zs ++ w.map (fun b => cond b 3 2)), ?_⟩
  unfold CNF.eval tableau
  rw [List.all_eq_true]
  intro cl hcl
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hcl
  rcases hcl with (hcl | ⟨t, ht, hcl⟩) | hcl
  · exact Cpl.init_ok c zs w m _ hw cl hcl
  · refine Cpl.step_ok c _ t _ _ ?_ cl hcl
    have _ := hz
    have hl : (zs ++ w.map (fun b => cond b 3 2)).length = zs.length + w.length := by simp
    rw [hl]
    unfold cellsOf
    omega
  · exact Cpl.final_ok c _ _ T h cl hcl

end PEqualNP.Library.SearchHelpers.Tab
