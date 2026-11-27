import PEqualNP.Library.SearchHelpers.TableauDefs

/-!
# Helpers: a satisfying assignment of the tableau formula gives an accepting run

Helper module (proofs only, no statement may use it). The direction "satisfiable implies an
accepting run" of the tableau formula of `TableauDefs.lean` (`accepts_of_sat`).

The proof. Take a satisfying assignment. The clauses of time `0` on the witness cells give a
witness: the cells before the first blank one, each read as a bit. Then, by induction on the
time, every variable that describes the real configuration of the run on that witness is true
(`Snd.Inv`, kept by `Snd.step_inv`); the same invariant carries the bounds on the real run
that the clauses need (counter codes, states and symbols below the bound, stack heights). The
negative unit clauses of the last time then force the real run to be halted with `[1]` on the
output stack (`Snd.final_out`). The numbering `uvar` is never unfolded.
-/

namespace PEqualNP.Library.SearchHelpers.Tab

open PEqualNP.Library.Universal PEqualNP.Search

namespace Snd

/-! ### Cell values -/

/-- The value of cell `j` from the top of a stack: `0` below the bottom, `s + 1` for `s`. -/
def cellVal (st : List ℕ) (j : ℕ) : ℕ :=
  match st[j]? with
  | none => 0
  | some s => s + 1

theorem cellVal_nil (j : ℕ) : cellVal [] j = 0 := by simp [cellVal]

theorem cellVal_cons_zero (a : ℕ) (st : List ℕ) : cellVal (a :: st) 0 = a + 1 := by
  simp [cellVal]

theorem cellVal_cons_succ (a : ℕ) (st : List ℕ) (j : ℕ) :
    cellVal (a :: st) (j + 1) = cellVal st j := by
  simp [cellVal]

theorem cellVal_tail (st : List ℕ) (j : ℕ) : cellVal st.tail j = cellVal st (j + 1) := by
  cases st <;> simp [cellVal]

theorem cellVal_of_le {st : List ℕ} {j : ℕ} (h : st.length ≤ j) : cellVal st j = 0 := by
  simp [cellVal, List.getElem?_eq_none h]

theorem cellVal_zero (st : List ℕ) : cellVal st 0 = topIndex st := by
  cases st <;> simp [cellVal, topIndex]

theorem cellVal_le {st : List ℕ} {B : ℕ} (h : ∀ s ∈ st, s < B) (j : ℕ) : cellVal st j ≤ B := by
  rcases hj : st[j]? with _ | s
  · simp [cellVal, hj]
  · simp only [cellVal, hj]
    exact Nat.succ_le_of_lt (h s (List.mem_of_getElem? hj))

theorem cellVal_append_left {zs r : List ℕ} {j : ℕ} (h : j < zs.length) :
    cellVal (zs ++ r) j = zs.getD j 0 + 1 := by
  simp [cellVal, List.getElem?_append_left h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]

theorem cellVal_append_right (zs r : List ℕ) (j : ℕ) :
    cellVal (zs ++ r) (zs.length + j) = cellVal r j := by
  simp [cellVal, List.getElem?_append_right]

/-! ### Sums bound entries -/

theorem getD_le_sum (tbl : List ℕ) (v : ℕ) : tbl.getD v 0 ≤ tbl.sum := by
  induction tbl generalizing v with
  | nil => simp
  | cons a r ih =>
    cases v with
    | zero => simp
    | succ v =>
      simp only [List.getD_cons_succ, List.sum_cons]
      exact (ih v).trans (Nat.le_add_left _ _)

theorem le_sum_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b r ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simp only [List.sum_cons]
      exact (ih h).trans (Nat.le_add_left _ _)

/-! ### Evaluating clauses -/

theorem eval_all {σ : Assignment} {φ : CNF} (h : CNF.eval σ φ = true) {cl : Clause}
    (hc : cl ∈ φ) : Clause.eval σ cl = true := by
  unfold CNF.eval at h
  exact List.all_eq_true.1 h cl hc

theorem imp_true {σ : Assignment} {prem : List ℕ} {concl : ℕ}
    (h : Clause.eval σ (imp prem concl) = true) (hp : ∀ x ∈ prem, σ x = true) :
    σ concl = true := by
  unfold Clause.eval imp at h
  rcases List.any_eq_true.1 h with ⟨l, hl, he⟩
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    have := hp x hx
    simp [Literal.eval, this] at he
  · rw [List.mem_singleton] at hl
    subst hl
    simpa [Literal.eval] using he

theorem imp0 {σ : Assignment} {a : ℕ} (h : Clause.eval σ (imp [] a) = true) : σ a = true :=
  imp_true h (by simp)

theorem imp1 {σ : Assignment} {x a : ℕ} (h : Clause.eval σ (imp [x] a) = true)
    (hx : σ x = true) : σ a = true :=
  imp_true h (by simpa using hx)

theorem imp2 {σ : Assignment} {x y a : ℕ} (h : Clause.eval σ (imp [x, y] a) = true)
    (hx : σ x = true) (hy : σ y = true) : σ a = true :=
  imp_true h (by simp [hx, hy])

theorem unit_false {σ : Assignment} {x : ℕ} (h : Clause.eval σ [(x, false)] = true) :
    σ x = false := by
  simpa [Clause.eval, Literal.eval] using h

/-! ### One step of the machine, in the words of the tableau -/

theorem step_eq (P : List Instr) (cfg : Cfg) :
    step P cfg = exec (instrAt P (pcCode cfg.pc)) cfg.state cfg.stk := by
  rcases cfg with ⟨pc, v, S⟩
  cases pc with
  | none => rfl
  | some n =>
    simp only [step, pcCode, instrAt, List.getD_eq_getElem?_getD]
    cases P[n]? <;> rfl

theorem exec_pc (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    pcCode (exec i v S).pc = nextCode i v := by
  cases i <;> rfl

theorem exec_state (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    (exec i v S).state =
      newState i v (match rdStack i with
        | none => 0
        | some k => topIndex (S.getD k [])) := by
  cases i <;> rfl

theorem exec_len (i : Instr) (v : ℕ) (S : List (List ℕ)) :
    (exec i v S).stk.length = S.length := by
  cases i <;> simp [exec]

theorem exec_stk (i : Instr) (v : ℕ) (S : List (List ℕ)) (k : ℕ) (hk : k < S.length) :
    (exec i v S).stk.getD k [] =
      match stackOp i k with
      | .keep => S.getD k []
      | .push tbl => tbl.getD v 0 :: S.getD k []
      | .pop => (S.getD k []).tail := by
  cases i with
  | push k' tbl nx =>
    by_cases h : k' = k
    · subst h
      simp [exec, stackOp, List.getD_eq_getElem?_getD, hk]
    · simp [exec, stackOp, List.getD_eq_getElem?_getD, h, List.getElem?_set_ne h]
  | pop k' tbl w nx =>
    by_cases h : k' = k
    · subst h
      simp [exec, stackOp, List.getD_eq_getElem?_getD, hk]
    · simp [exec, stackOp, List.getD_eq_getElem?_getD, h, List.getElem?_set_ne h]
  | _ => rfl

theorem stackOp_push_bd {i : Instr} {k : ℕ} {tbl : List ℕ} (h : stackOp i k = .push tbl) :
    tbl.sum ≤ Instr.bd i := by
  cases i with
  | push k' tbl' nx =>
    simp only [stackOp] at h
    split_ifs at h
    cases h
    simp [Instr.bd]
  | pop k' tbl' w nx =>
    simp only [stackOp] at h
    split_ifs at h
  | _ => cases h

theorem nextCode_le {i : Instr} {B : ℕ} (h : Instr.bd i < B) (v : ℕ) : nextCode i v ≤ B := by
  cases i with
  | branch tbl a b =>
    simp only [nextCode, Instr.bd] at *
    split_ifs <;> omega
  | goto tbl =>
    simp only [nextCode, Instr.bd] at *
    have := getD_le_sum tbl v
    omega
  | halt => exact Nat.zero_le _
  | _ =>
    simp only [nextCode, Instr.bd] at *
    omega

theorem exec_state_lt {i : Instr} {B v : ℕ} (h : Instr.bd i < B) (hv : v < B)
    (S : List (List ℕ)) : (exec i v S).state < B := by
  cases i with
  | pop k tbl w nx =>
    simp only [exec, Instr.bd] at *
    have := getD_le_sum tbl (v * w + topIndex (S.getD k []))
    omega
  | peek k tbl w nx =>
    simp only [exec, Instr.bd] at *
    have := getD_le_sum tbl (v * w + topIndex (S.getD k []))
    omega
  | load tbl nx =>
    simp only [exec, Instr.bd] at *
    have := getD_le_sum tbl v
    omega
  | _ => exact hv

theorem instrAt_bd {P : List Instr} {B : ℕ} (hP : ∀ i ∈ P, Instr.bd i < B) (hB : 0 < B)
    (q : ℕ) : Instr.bd (instrAt P q) < B := by
  cases q with
  | zero => exact hB
  | succ n =>
    simp only [instrAt, List.getD_eq_getElem?_getD]
    rcases hn : P[n]? with _ | i
    · exact hB
    · exact hP i (List.mem_of_getElem? hn)

/-! ### Reading the clauses of one step -/

theorem mem_step {K H B t q : ℕ} {P : List Instr} {cl : Clause} (hq : q ≤ B)
    (h : cl ∈ pcClauses B t q (instrAt P q) ∨ cl ∈ stateClauses K B t q (instrAt P q) ∨
      ∃ k < K, cl ∈ cellClauses H B t q k (stackOp (instrAt P q) k)) :
    cl ∈ stepClauses K H B P t := by
  simp only [stepClauses, List.mem_flatMap, List.mem_range, List.mem_append]
  refine ⟨q, Nat.lt_succ_of_le hq, ?_⟩
  rcases h with h | h | ⟨k, hk, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨k, hk, h⟩

theorem keep_cl {σ : Assignment} {H B t q k : ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k .keep, Clause.eval σ cl = true) {j x : ℕ}
    (hj : j < H) (hx : x ≤ B) (hp : σ (vP t q) = true) (hc : σ (vC t k j x) = true) :
    σ (vC (t + 1) k j x) = true :=
  imp2 (hcl _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
    List.mem_map.2 ⟨x, List.mem_range.2 (Nat.lt_succ_of_le hx), rfl⟩⟩)) hp hc

theorem push_cl_top {σ : Assignment} {H B t q k : ℕ} {tbl : List ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k (.push tbl), Clause.eval σ cl = true) {v : ℕ}
    (hv : v < B) (hp : σ (vP t q) = true) (hq : σ (vQ t v) = true) :
    σ (vC (t + 1) k 0 (tbl.getD v 0 + 1)) = true :=
  imp2 (hcl _ (List.mem_append_left _ (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩))) hp hq

theorem push_cl_shift {σ : Assignment} {H B t q k : ℕ} {tbl : List ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k (.push tbl), Clause.eval σ cl = true) {j x : ℕ}
    (hj : j < H - 1) (hx : x ≤ B) (hp : σ (vP t q) = true) (hc : σ (vC t k j x) = true) :
    σ (vC (t + 1) k (j + 1) x) = true :=
  imp2 (hcl _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
    List.mem_map.2 ⟨x, List.mem_range.2 (Nat.lt_succ_of_le hx), rfl⟩⟩))) hp hc

theorem pop_cl_shift {σ : Assignment} {H B t q k : ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k .pop, Clause.eval σ cl = true) {j x : ℕ}
    (hj : j < H - 1) (hx : x ≤ B) (hp : σ (vP t q) = true)
    (hc : σ (vC t k (j + 1) x) = true) : σ (vC (t + 1) k j x) = true :=
  imp2 (hcl _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
    List.mem_map.2 ⟨x, List.mem_range.2 (Nat.lt_succ_of_le hx), rfl⟩⟩))) hp hc

theorem pop_cl_last {σ : Assignment} {H B t q k : ℕ}
    (hcl : ∀ cl ∈ cellClauses H B t q k .pop, Clause.eval σ cl = true)
    (hp : σ (vP t q) = true) : σ (vC (t + 1) k (H - 1) 0) = true :=
  imp1 (hcl _ (List.mem_append_right _ (List.mem_singleton.2 rfl))) hp

/-! ### The invariant -/

/-- The invariant at time `t`: the variables that describe the configuration `cfg` are true
under `σ`, and `cfg` is within the bounds: `K` stacks, counter code at most `B`, state and
symbols below `B`, heights at most `h`. -/
structure Inv (σ : Assignment) (K H B h t : ℕ) (cfg : Cfg) : Prop where
  pc : σ (vP t (pcCode cfg.pc)) = true
  st : σ (vQ t cfg.state) = true
  cell : ∀ k < K, ∀ j < H, σ (vC t k j (cellVal (cfg.stk.getD k []) j)) = true
  len : cfg.stk.length = K
  pcB : pcCode cfg.pc ≤ B
  stB : cfg.state < B
  symB : ∀ k < K, ∀ s ∈ cfg.stk.getD k [], s < B
  ht : ∀ k < K, (cfg.stk.getD k []).length ≤ h

theorem reads_ok {σ : Assignment} {K H B t : ℕ} {S : List (List ℕ)} (hlen : S.length = K)
    (hcell : ∀ k < K, ∀ j < H, σ (vC t k j (cellVal (S.getD k []) j)) = true) (hH : 0 < H)
    (hsym : ∀ k < K, ∀ s ∈ S.getD k [], s < B) (o : Option ℕ) :
    ∃ r ∈ reads K B t o, (∀ x ∈ r.1, σ x = true) ∧
      r.2 = (match o with
        | none => 0
        | some k => topIndex (S.getD k [])) := by
  cases o with
  | none => exact ⟨([], 0), by simp [reads], by simp, rfl⟩
  | some k =>
    by_cases hk : k < K
    · refine ⟨([vC t k 0 (cellVal (S.getD k []) 0)], cellVal (S.getD k []) 0), ?_, ?_,
        cellVal_zero _⟩
      · simp only [reads, hk, ↓reduceIte]
        exact List.mem_map.2 ⟨_, List.mem_range.2
          (Nat.lt_succ_of_le (cellVal_le (hsym k hk) 0)), rfl⟩
      · intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact hcell k hk 0 hH
    · refine ⟨([], 0), by simp [reads, hk], by simp, ?_⟩
      have : S.getD k [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      show 0 = topIndex (S.getD k [])
      rw [this]
      rfl

theorem step_inv {σ : Assignment} {K H B h t : ℕ} {P : List Instr} {cfg : Cfg}
    (hI : Inv σ K H B h t cfg) (hH : h < H) (hP : ∀ i ∈ P, Instr.bd i < B)
    (hc : ∀ cl ∈ stepClauses K H B P t, Clause.eval σ cl = true) :
    Inv σ K H B (h + 1) (t + 1) (step P cfg) := by
  obtain ⟨hpc, hst, hcell, hlen, hpcB, hstB, hsymB, hht⟩ := hI
  rw [step_eq]
  have hbd : Instr.bd (instrAt P (pcCode cfg.pc)) < B :=
    instrAt_bd hP (Nat.lt_of_le_of_lt (Nat.zero_le _) hstB) _
  have hcl : ∀ k < K, ∀ cl ∈ cellClauses H B t (pcCode cfg.pc) k
      (stackOp (instrAt P (pcCode cfg.pc)) k), Clause.eval σ cl = true :=
    fun k hk cl hm => hc cl (mem_step hpcB (Or.inr (Or.inr ⟨k, hk, hm⟩)))
  have hstk := fun k (hk : k < K) =>
    exec_stk (instrAt P (pcCode cfg.pc)) cfg.state cfg.stk k (hlen ▸ hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_pc]
    exact imp2 (hc _ (mem_step hpcB (Or.inl
      (List.mem_map.2 ⟨cfg.state, List.mem_range.2 hstB, rfl⟩)))) hpc hst
  · rw [exec_state]
    obtain ⟨r, hr, hprem, hr2⟩ := reads_ok (σ := σ) (B := B) (t := t) hlen hcell
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hH) hsymB (rdStack (instrAt P (pcCode cfg.pc)))
    rw [← hr2]
    refine imp_true (hc _ (mem_step hpcB (Or.inr (Or.inl
      (List.mem_flatMap.2 ⟨cfg.state, List.mem_range.2 hstB,
        List.mem_map.2 ⟨r, hr, rfl⟩⟩))))) ?_
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hpc
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hst
    · exact hprem x hx
  · intro k hk j hj
    have hs := hstk k hk
    have hcl' := hcl k hk
    cases hop : stackOp (instrAt P (pcCode cfg.pc)) k with
    | keep =>
      rw [hop] at hs hcl'
      simp only at hs
      rw [hs]
      exact keep_cl hcl' hj (cellVal_le (hsymB k hk) j) hpc (hcell k hk j hj)
    | push tbl =>
      rw [hop] at hs hcl'
      simp only at hs
      rw [hs]
      cases j with
      | zero =>
        rw [cellVal_cons_zero]
        exact push_cl_top hcl' hstB hpc hst
      | succ j =>
        rw [cellVal_cons_succ]
        exact push_cl_shift hcl' (by omega) (cellVal_le (hsymB k hk) j) hpc
          (hcell k hk j (by omega))
    | pop =>
      rw [hop] at hs hcl'
      simp only at hs
      rw [hs, cellVal_tail]
      by_cases hj' : j < H - 1
      · exact pop_cl_shift hcl' hj' (cellVal_le (hsymB k hk) (j + 1)) hpc
          (hcell k hk (j + 1) (by omega))
      · have h0 : cellVal (cfg.stk.getD k []) (j + 1) = 0 :=
          cellVal_of_le (by have := hht k hk; omega)
        have hjH : j = H - 1 := by omega
        rw [h0, hjH]
        exact pop_cl_last hcl' hpc
  · exact (exec_len _ _ _).trans hlen
  · rw [exec_pc]
    exact nextCode_le hbd _
  · exact exec_state_lt hbd hstB _
  · intro k hk s hs'
    have hs := hstk k hk
    cases hop : stackOp (instrAt P (pcCode cfg.pc)) k with
    | keep =>
      rw [hop] at hs
      simp only at hs
      rw [hs] at hs'
      exact hsymB k hk s hs'
    | push tbl =>
      rw [hop] at hs
      simp only at hs
      rw [hs] at hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · have h1 := getD_le_sum tbl cfg.state
        have h2 := stackOp_push_bd hop
        omega
      · exact hsymB k hk s hs'
    | pop =>
      rw [hop] at hs
      simp only at hs
      rw [hs] at hs'
      exact hsymB k hk s (List.mem_of_mem_tail hs')
  · intro k hk
    have hs := hstk k hk
    have hl := hht k hk
    cases hop : stackOp (instrAt P (pcCode cfg.pc)) k with
    | keep =>
      rw [hop] at hs
      simp only at hs
      rw [hs]
      omega
    | push tbl =>
      rw [hop] at hs
      simp only at hs
      rw [hs, List.length_cons]
      omega
    | pop =>
      rw [hop] at hs
      simp only at hs
      rw [hs, List.length_tail]
      omega

/-! ### Time zero: the witness and the invariant -/

theorem wit_exists (f : ℕ → ℕ → Bool) (m : ℕ)
    (h1 : ∀ j < m, f j 0 = true ∨ f j 3 = true ∨ f j 4 = true)
    (h2 : ∀ j, j + 1 < m → f j 0 = true → f (j + 1) 0 = true) :
    ∃ w : List Bool, w.length ≤ m ∧
      ∀ j < m, f j (cellVal (w.map (fun b => cond b 3 2)) j) = true := by
  induction m generalizing f with
  | zero => exact ⟨[], Nat.le_refl _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    by_cases h0 : f 0 0 = true
    · refine ⟨[], Nat.zero_le _, fun j hj => ?_⟩
      simp only [List.map_nil, cellVal_nil]
      induction j with
      | zero => exact h0
      | succ j ihj => exact h2 j hj (ihj (by omega))
    · obtain ⟨w, hw, hwj⟩ := ih (fun j => f (j + 1)) (fun j hj => h1 (j + 1) (by omega))
        (fun j hj => h2 (j + 1) (by omega))
      rcases h1 0 (Nat.succ_pos _) with h | h | h
      · exact absurd h h0
      · refine ⟨false :: w, by simpa using hw, fun j hj => ?_⟩
        cases j with
        | zero => simpa [cellVal_cons_zero] using h
        | succ j => simpa [cellVal_cons_succ] using hwj j (by omega)
      · refine ⟨true :: w, by simpa using hw, fun j hj => ?_⟩
        cases j with
        | zero => simpa [cellVal_cons_zero] using h
        | succ j => simpa [cellVal_cons_succ] using hwj j (by omega)

theorem wit {σ : Assignment} (c : Code) (zs : List ℕ) (m H : ℕ)
    (hinit : ∀ cl ∈ initClauses c zs m H, Clause.eval σ cl = true) :
    ∃ w : List Bool, w.length ≤ m ∧ (c.kin < c.nstk → ∀ j < m,
      σ (vC 0 c.kin (zs.length + j) (cellVal (w.map (fun b => cond b 3 2)) j)) = true) := by
  by_cases hk : c.kin < c.nstk
  · unfold initClauses at hinit
    simp only [hk, ↓reduceIte] at hinit
    have h1 : ∀ j < m, σ (vC 0 c.kin (zs.length + j) 0) = true ∨
        σ (vC 0 c.kin (zs.length + j) 3) = true ∨ σ (vC 0 c.kin (zs.length + j) 4) = true := by
      intro j hj
      have := hinit _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))))
      simpa [Clause.eval, Literal.eval] using this
    have h2 : ∀ j, j + 1 < m → σ (vC 0 c.kin (zs.length + j) 0) = true →
        σ (vC 0 c.kin (zs.length + (j + 1)) 0) = true := by
      intro j hj h0
      exact imp1 (hinit _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩))))) h0
    obtain ⟨w, hw, hj⟩ := wit_exists (fun j x => σ (vC 0 c.kin (zs.length + j) x)) m h1 h2
    exact ⟨w, hw, fun _ => hj⟩
  · exact ⟨[], Nat.zero_le _, fun h => absurd h hk⟩

theorem init_stk_kin (c : Code) (inp : List ℕ) (hk : c.kin < c.nstk) :
    (c.init inp).stk.getD c.kin [] = inp := by
  simp [Code.init, List.getD_eq_getElem?_getD, hk]

theorem init_stk_ne (c : Code) (inp : List ℕ) {k : ℕ} (hne : k ≠ c.kin) :
    (c.init inp).stk.getD k [] = [] := by
  simp only [Code.init]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne), List.getElem?_replicate]
  split_ifs <;> rfl

theorem init_inv {σ : Assignment} (c : Code) (zs : List ℕ) (m H : ℕ) (w : List Bool)
    (hz : ∀ z ∈ zs, z < 4) (hw : w.length ≤ m)
    (hinit : ∀ cl ∈ initClauses c zs m H, Clause.eval σ cl = true)
    (hwit : c.kin < c.nstk → ∀ j < m,
      σ (vC 0 c.kin (zs.length + j) (cellVal (w.map (fun b => cond b 3 2)) j)) = true) :
    Inv σ c.nstk H (bound c) (zs.length + m) 0
      (c.init (zs ++ w.map (fun b => cond b 3 2))) := by
  unfold initClauses at hinit
  have hB : 4 ≤ bound c := by unfold bound; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact imp0 (hinit _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons.2 (Or.inl rfl)))))
  · exact imp0 (hinit _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))
  · intro k hk j hj
    by_cases hkin : k = c.kin
    · subst hkin
      simp only [hk, ↓reduceIte] at hinit
      rw [init_stk_kin c _ hk]
      rcases Nat.lt_or_ge j zs.length with h1 | h1
      · rw [cellVal_append_left h1]
        exact imp0 (hinit _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map.2 ⟨j, List.mem_range.2 h1, rfl⟩))))))
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h1
        rw [cellVal_append_right]
        rcases Nat.lt_or_ge j' m with h2 | h2
        · exact hwit hk j' h2
        · obtain ⟨j'', rfl⟩ := Nat.exists_eq_add_of_le h2
          rw [cellVal_of_le (by rw [List.length_map]; omega)]
          have := imp0 (hinit _ (List.mem_append_right _ (List.mem_append_right _
            (List.mem_map.2 ⟨j'', List.mem_range.2 (by omega), rfl⟩))))
          rwa [Nat.add_assoc] at this
    · rw [init_stk_ne c _ hkin, cellVal_nil]
      exact imp0 (hinit _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by
          simp only [hkin, ↓reduceIte]
          exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩))))
  · simp [Code.init]
  · show c.pc₀ + 1 ≤ bound c
    unfold bound
    omega
  · show c.state₀ < bound c
    unfold bound
    omega
  · intro k hk s hs
    by_cases hkin : k = c.kin
    · subst hkin
      rw [init_stk_kin c _ hk] at hs
      rcases List.mem_append.1 hs with hs | hs
      · exact Nat.lt_of_lt_of_le (hz s hs) hB
      · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
        cases b <;> simp <;> omega
    · rw [init_stk_ne c _ hkin] at hs
      simp at hs
  · intro k hk
    by_cases hkin : k = c.kin
    · subst hkin
      rw [init_stk_kin c _ hk, List.length_append, List.length_map]
      omega
    · rw [init_stk_ne c _ hkin]
      exact Nat.zero_le _

theorem prog_bd (c : Code) : ∀ i ∈ c.prog, Instr.bd i < bound c := by
  intro i hi
  have := le_sum_of_mem (List.mem_map_of_mem (f := Instr.bd) hi)
  unfold bound
  omega

/-! ### The last time -/

theorem final_out {σ : Assignment} {c : Code} {H B h T : ℕ} {cfg : Cfg}
    (hI : Inv σ c.nstk H B h T cfg) (hH : 2 ≤ H)
    (hf : ∀ cl ∈ finalClauses c B T, Clause.eval σ cl = true) :
    cfg.pc = none ∧ cfg.stk.getD c.kout [] = [1] := by
  unfold finalClauses at hf
  constructor
  · rcases hpc : cfg.pc with _ | n
    · rfl
    · have h1 := hI.pc
      have h2 := hI.pcB
      rw [hpc] at h1 h2
      have h3 := unit_false (hf _ (List.mem_append_left _
        (List.mem_map.2 ⟨n, List.mem_range.2 h2, rfl⟩)))
      rw [show pcCode (some n) = n + 1 from rfl, h3] at h1
      cases h1
  · by_cases hk : c.kout < c.nstk
    · simp only [hk, ↓reduceIte] at hf
      have h0 := hI.cell c.kout hk 0 (by omega)
      have h1 := hI.cell c.kout hk 1 (by omega)
      have hsym := hI.symB c.kout hk
      have hA : σ (vC T c.kout 0 0) = false :=
        unit_false (hf _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_singleton.2 rfl)))))
      have hBx : ∀ x < B, x ≠ 1 → σ (vC T c.kout 0 (x + 1)) = false := fun x hx hne =>
        unit_false (hf _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, List.mem_range.2 hx, by
            simp only [hne, ↓reduceIte]
            exact List.mem_singleton.2 rfl⟩)))))
      have hCx : ∀ x < B, σ (vC T c.kout 1 (x + 1)) = false := fun x hx =>
        unit_false (hf _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩))))
      rcases hO : cfg.stk.getD c.kout [] with _ | ⟨a, r⟩
      · rw [hO, cellVal_nil, hA] at h0
        cases h0
      · rw [hO] at h0 h1 hsym
        rw [cellVal_cons_zero] at h0
        have ha : a = 1 := by
          by_contra hne
          rw [hBx a (hsym a (by simp)) hne] at h0
          cases h0
        subst ha
        rcases r with _ | ⟨b, r'⟩
        · rfl
        · rw [cellVal_cons_succ, cellVal_cons_zero, hCx b (hsym b (by simp))] at h1
          cases h1
    · have := hf [] (List.mem_append_right _ (by
        simp only [hk, ↓reduceIte]
        exact List.mem_singleton.2 rfl))
      simp [Clause.eval] at this

end Snd

/-- If the tableau formula is satisfiable then the code, on the input followed by some witness
of at most `m` symbols `2` or `3`, halts within `T` steps with `[1]` on its output stack. -/
theorem accepts_of_sat (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4)
    (h : PEqualNP.Search.Satisfiable (tableau c zs m T)) :
    ∃ w : List Bool, w.length ≤ m ∧
      c.outputsWithin (zs ++ w.map (fun b => cond b 3 2)) T [1] := by
  obtain ⟨σ, hσ⟩ := h
  have hall : ∀ cl ∈ tableau c zs m T, Clause.eval σ cl = true :=
    fun cl hcl => Snd.eval_all hσ hcl
  have hinit : ∀ cl ∈ initClauses c zs m (cellsOf zs.length m T), Clause.eval σ cl = true :=
    fun cl hcl => hall cl (List.mem_append_left _ (List.mem_append_left _ hcl))
  have hstep : ∀ t < T, ∀ cl ∈ stepClauses c.nstk (cellsOf zs.length m T) (bound c) c.prog t,
      Clause.eval σ cl = true :=
    fun t ht cl hcl => hall cl (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, hcl⟩)))
  have hfin : ∀ cl ∈ finalClauses c (bound c) T, Clause.eval σ cl = true :=
    fun cl hcl => hall cl (List.mem_append_right _ hcl)
  obtain ⟨w, hw, hwit⟩ := Snd.wit c zs m (cellsOf zs.length m T) hinit
  refine ⟨w, hw, ?_⟩
  have hrun : ∀ t ≤ T, Snd.Inv σ c.nstk (cellsOf zs.length m T) (bound c)
      (zs.length + m + t) t (c.run (zs ++ w.map (fun b => cond b 3 2)) t) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact Snd.init_inv c zs m _ w hz hw hinit hwit
    | succ t ih =>
      intro ht
      have hlt : zs.length + m + t < cellsOf zs.length m T := by
        show zs.length + m + t < zs.length + m + T + 2
        omega
      have := Snd.step_inv (ih (by omega)) hlt (Snd.prog_bd c) (hstep t (by omega))
      rw [Code.run, Function.iterate_succ_apply']
      exact this
  exact Snd.final_out (hrun T (Nat.le_refl _))
    (by show 2 ≤ zs.length + m + T + 2; omega) hfin

end PEqualNP.Library.SearchHelpers.Tab
