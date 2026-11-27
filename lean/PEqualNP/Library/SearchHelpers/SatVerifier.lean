import PEqualNP.Library.SearchHelpers.SatVerifierDefs

/-!
# The string verifier `SV` characterizes SAT

Helper module (proofs only, no statement may use it). Pure mathematics on bit strings: no
machine appears here. The main results are `SV_iff` (the verifier accepts `(x, w)` exactly when
`x` encodes a formula that the assignment denoted by `w` satisfies), `SV_spec` (membership in
SAT with witnesses no longer than the input) and `SAT_in_NP_of` (SAT is in NP as soon as `SV` is
computable in polynomial time). The length bounds `memStep_length` and `evStep_length` hold on
all strings.
-/

namespace PEqualNP.Library.SearchHelpers.SatV

open PEqualNP.Search PEqualNP.Library.Universal PEqualNP.Library.Machines

/-! ### Items -/

theorem headI_dropI : ∀ s : List Bool, headI s ++ dropI s = s
  | [] => rfl
  | [_] => rfl
  | true :: d :: r => by simp [headI, dropI, headI_dropI r]
  | false :: d :: r => by simp [headI, dropI]

theorem dropI_length (s : List Bool) : (dropI s).length ≤ s.length := by
  have h := congrArg List.length (headI_dropI s)
  simp only [List.length_append] at h
  omega

theorem headI_digits (ds : List Bool) (b : Bool) (r : List Bool) :
    headI ((ds.flatMap fun d => [true, d]) ++ false :: b :: r) =
      (ds.flatMap fun d => [true, d]) ++ [false, b] := by
  induction ds with
  | nil => simp [headI]
  | cons d ds ih => simpa [headI] using ih

theorem dropI_digits (ds : List Bool) (b : Bool) (r : List Bool) :
    dropI ((ds.flatMap fun d => [true, d]) ++ false :: b :: r) = r := by
  induction ds with
  | nil => simp [dropI]
  | cons d ds ih => simpa [dropI] using ih

theorem headI_vcode (i : ℕ) (r : List Bool) : headI (vcode i ++ r) = vcode i := by
  simpa [vcode] using headI_digits i.bits true r

theorem dropI_vcode (i : ℕ) (r : List Bool) : dropI (vcode i ++ r) = r := by
  simpa [vcode] using dropI_digits i.bits true r

theorem encodeLiteral_eq (l : Literal) : encodeLiteral l = true :: l.2 :: vcode l.1 := by
  simp [encodeLiteral, vcode]

theorem headI_lit (l : Literal) (r : List Bool) :
    headI (encodeLiteral l ++ r) = encodeLiteral l := by
  simp [encodeLiteral_eq, headI, headI_vcode]

theorem dropI_lit (l : Literal) (r : List Bool) : dropI (encodeLiteral l ++ r) = r := by
  simp [encodeLiteral_eq, dropI, dropI_vcode]

theorem vcode_ne_nil (i : ℕ) : vcode i ≠ [] := by simp [vcode]

theorem vcode_length_pos (i : ℕ) : 1 ≤ (vcode i).length := by simp [vcode]

theorem vcode_injective : Function.Injective vcode := by
  intro i j h
  have h' : (i.bits.flatMap fun d => [true, d]) ++ (false :: true :: []) =
      (j.bits.flatMap fun d => [true, d]) ++ (false :: true :: []) := h
  exact bits_injective (digits_append_inj _ _ true true [] [] h').1

theorem vcode_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    vcode (Nat.bit b n) = true :: b :: vcode n := by
  simp [vcode, Nat.bits_append_bit n b h]

theorem vcode_zero : vcode 0 = [false, true] := by simp [vcode]

/-! ### Length bounds on all strings -/

theorem bflag_length (b : Bool) : (bflag b).length ≤ 1 := by cases b <;> simp [bflag]

/-- The membership step lengthens no string by more than 3 symbols. -/
theorem memStep_length (s : List Bool) : (memStep s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := dropI_length (unpairB (unpairB s).2).1
  have h4 := bflag_length (decide (headI (unpairB (unpairB s).2).1 = (unpairB s).1))
  simp only [memStep, pairB_length, List.length_append]
  omega

/-- The evaluation step lengthens no string by more than 5 symbols. -/
theorem evStep_length (s : List Bool) : (evStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have h4 := dropI_length (stR s)
  have h5 := bflag_length (litB (headI (stR s)) (stW s))
  have h6 := bflag_length (stC s).isEmpty
  have h7 := sel_length (bflag (isEnd (stR s)))
    (pairB (stC s ++ bflag (litB (headI (stR s)) (stW s))) (stB s))
    (pairB [] (stB s ++ bflag (stC s).isEmpty)) (2 * (stC s).length + (stB s).length + 3)
    (by simp only [pairB_length, List.length_append]; omega)
    (by simp only [pairB_length, List.length_append, List.length_nil]; omega)
  simp only [evStep, pairB_length]
  simp only [stW, stR, stC, stB] at h4 h7 ⊢
  omega

/-! ### Membership of an item in the witness -/

theorem memStep_pair (c r fl : List Bool) :
    memStep (pairB c (pairB r fl)) =
      pairB c (pairB (dropI r) (fl ++ bflag (decide (headI r = c)))) := by
  simp [memStep, unpairB_pairB]

theorem memStep_iter (c : List Bool) (k : ℕ) : ∀ r fl : List Bool, ∃ fl' : List Bool,
    memStep^[k] (pairB c (pairB r fl)) = pairB c (pairB (dropI^[k] r) fl') ∧
      (fl' = [] ↔ fl = [] ∧ ∀ j < k, headI (dropI^[j] r) ≠ c) := by
  induction k with
  | zero => intro r fl; exact ⟨fl, rfl, by simp⟩
  | succ k ih =>
    intro r fl
    obtain ⟨fl', h1, h2⟩ := ih (dropI r) (fl ++ bflag (decide (headI r = c)))
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, memStep_pair, h1, Function.iterate_succ_apply]
    · rw [h2, List.append_eq_nil_iff, bflag_eq_nil, Nat.forall_lt_succ_left, and_assoc]
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply,
        decide_eq_false_iff_not]

/-- `memB c w` holds exactly when `c` is one of the first `w.length` items of `w`. -/
theorem memB_iff (c w : List Bool) :
    memB c w = true ↔ ∃ j < w.length, headI (dropI^[j] w) = c := by
  obtain ⟨fl', h1, h2⟩ := memStep_iter c w.length w []
  rw [memB, h1]
  simp only [unpairB_pairB, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, h2, true_and,
    not_forall, not_not, exists_prop]

/-- The assignment denoted by a witness: the variable `i` is true exactly when its code is one
of the first `w.length` items of `w`. -/
def asg (w : List Bool) : Assignment := fun i => memB (vcode i) w

theorem litB_lit (l : Literal) (w : List Bool) :
    litB (encodeLiteral l) w = Literal.eval (asg w) l := by
  obtain ⟨i, b⟩ := l
  simp only [litB, encodeLiteral_eq, List.tail_cons, polB, Literal.eval, asg]
  cases memB (vcode i) w <;> cases b <;> rfl

/-! ### The evaluation loop -/

theorem isEnd_lit (l : Literal) (r : List Bool) : isEnd (encodeLiteral l ++ r) = false := by
  simp [encodeLiteral_eq, isEnd]

theorem evStep_lit (w : List Bool) (l : Literal) (r cl bad : List Bool) :
    evStep (pairB w (pairB (encodeLiteral l ++ r) (pairB cl bad))) =
      pairB w (pairB r (pairB (cl ++ bflag (Literal.eval (asg w) l)) bad)) := by
  simp [evStep, stW, stR, stC, stB, unpairB_pairB, isEnd_lit, headI_lit, dropI_lit, litB_lit,
    bflag]

theorem evStep_end (w r cl bad : List Bool) :
    evStep (pairB w (pairB (false :: false :: r) (pairB cl bad))) =
      pairB w (pairB r (pairB [] (bad ++ bflag cl.isEmpty))) := by
  simp [evStep, stW, stR, stC, stB, unpairB_pairB, isEnd, dropI, bflag]

theorem evStep_nil (w cl bad : List Bool) :
    evStep (pairB w (pairB [] (pairB cl bad))) =
      pairB w (pairB [] (pairB (cl ++ bflag (litB [] w)) bad)) := by
  simp [evStep, stW, stR, stC, stB, unpairB_pairB, isEnd, dropI, headI, bflag]

theorem evStep_nil_iter (w bad : List Bool) (k : ℕ) : ∀ cl : List Bool, ∃ cl' : List Bool,
    evStep^[k] (pairB w (pairB [] (pairB cl bad))) = pairB w (pairB [] (pairB cl' bad)) := by
  induction k with
  | zero => intro cl; exact ⟨cl, rfl⟩
  | succ k ih =>
    intro cl
    obtain ⟨cl', h⟩ := ih (cl ++ bflag (litB [] w))
    exact ⟨cl', by rw [Function.iterate_succ_apply, evStep_nil, h]⟩

/-- A clause takes one step per literal and one for its end; the bad flag stays empty exactly
when it was empty and the clause is true. -/
theorem evStep_clause (w : List Bool) : ∀ (c : Clause) (r cl bad : List Bool),
    ∃ bad' : List Bool,
      evStep^[c.length + 1] (pairB w (pairB (encodeClause c ++ r) (pairB cl bad))) =
        pairB w (pairB r (pairB [] bad')) ∧
      (bad' = [] ↔ bad = [] ∧ (cl ≠ [] ∨ Clause.eval (asg w) c = true)) := by
  intro c
  induction c with
  | nil =>
    intro r cl bad
    refine ⟨bad ++ bflag cl.isEmpty, ?_, ?_⟩
    · simp [encodeClause, evStep_end]
    · simp [bflag_eq_nil, Clause.eval]
  | cons l c ih =>
    intro r cl bad
    obtain ⟨bad', h1, h2⟩ := ih r (cl ++ bflag (Literal.eval (asg w) l)) bad
    refine ⟨bad', ?_, ?_⟩
    · have e : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
        simp [encodeClause]
      rw [List.length_cons, Function.iterate_succ_apply, e, evStep_lit, h1]
    · rw [h2]
      simp only [ne_eq, List.append_eq_nil_iff, bflag_eq_nil, Clause.eval, List.any_cons,
        Bool.or_eq_true]
      cases Literal.eval (asg w) l <;> simp

/-- The number of steps that the evaluation of a formula takes. -/
def nIt : CNF → ℕ
  | [] => 0
  | c :: φ => nIt φ + (c.length + 1)

theorem evStep_cnf (w : List Bool) : ∀ (φ : CNF) (bad : List Bool), ∃ bad' : List Bool,
    evStep^[nIt φ] (pairB w (pairB (encodeCNF φ) (pairB [] bad))) =
        pairB w (pairB [] (pairB [] bad')) ∧
      (bad' = [] ↔ bad = [] ∧ CNF.eval (asg w) φ = true) := by
  intro φ
  induction φ with
  | nil => intro bad; exact ⟨bad, rfl, by simp [CNF.eval]⟩
  | cons c φ ih =>
    intro bad
    obtain ⟨bad1, h1, h2⟩ := evStep_clause w c (encodeCNF φ) [] bad
    obtain ⟨bad', h3, h4⟩ := ih bad1
    refine ⟨bad', ?_, ?_⟩
    · have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
      rw [nIt, Function.iterate_add_apply, e, h1, h3]
    · rw [h4, h2]
      simp [CNF.eval, and_assoc]

theorem length_le_flatMap_lit (c : Clause) : c.length ≤ (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih => simp [encodeLiteral_eq]; omega

theorem nIt_le (φ : CNF) : nIt φ ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [nIt]
  | cons c φ ih =>
    have := length_le_flatMap_lit c
    simp only [nIt, encodeCNF, encodeClause, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at ih ⊢
    omega

/-- On the encoding of a formula, `evalB` is the value of the formula under the assignment
denoted by the witness. -/
theorem evalB_enc (φ : CNF) (w : List Bool) :
    evalB (encodeCNF φ) w = CNF.eval (asg w) φ := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le' (nIt_le φ)
  obtain ⟨bad', h1, h2⟩ := evStep_cnf w φ []
  obtain ⟨cl', h3⟩ := evStep_nil_iter w bad' e []
  rw [evalB, he, Function.iterate_add_apply, h1, h3]
  simp only [stB, unpairB_pairB]
  rw [Bool.eq_iff_iff, List.isEmpty_iff, h2]
  simp

/-! ### Well-formedness -/

theorem foldl_dead (s : List Bool) : s.foldl wfD .dead = .dead := by
  induction s with
  | nil => rfl
  | cons x s ih => simpa [wfD] using ih

/-- Reading a canonical variable code from inside a literal. -/
theorem foldl_vcode (n : ℕ) : ∀ r : List Bool,
    (vcode n ++ r).foldl wfD .c = r.foldl wfD .b ∧
      (n ≠ 0 → (vcode n ++ r).foldl wfD .d = r.foldl wfD .b) := by
  induction n using Nat.binaryRec' with
  | zero => intro r; simp [vcode_zero, wfD]
  | bit b n h ih =>
    intro r
    obtain ⟨ih1, ih2⟩ := ih r
    rw [vcode_bit b n h]
    cases b
    · have hn : n ≠ 0 := fun h0 => by simpa using h h0
      simp [wfD, ih2 hn]
    · simp [wfD, ih1]

theorem foldl_lit (l : Literal) (r : List Bool) :
    (encodeLiteral l ++ r).foldl wfD .a = r.foldl wfD .b ∧
      (encodeLiteral l ++ r).foldl wfD .b = r.foldl wfD .b := by
  simp [encodeLiteral_eq, wfD, (foldl_vcode l.1 r).1]

theorem foldl_clause (c : Clause) (r : List Bool) :
    (encodeClause c ++ r).foldl wfD .a = r.foldl wfD .a ∧
      (encodeClause c ++ r).foldl wfD .b = r.foldl wfD .a := by
  induction c with
  | nil => simp [encodeClause, wfD]
  | cons l c ih =>
    have e : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
      simp [encodeClause]
    rw [e, (foldl_lit l _).1, (foldl_lit l _).2, ih.2]
    exact ⟨rfl, rfl⟩

theorem foldl_cnf (φ : CNF) : (encodeCNF φ).foldl wfD .a = .a := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
    rw [e, (foldl_clause c _).1, ih]

/-- What a string accepted from a state at a pair boundary looks like. -/
def Good : WS → List Bool → Prop
  | .a, s => ∃ φ : CNF, s = encodeCNF φ
  | .b, s => ∃ (c : Clause) (φ : CNF), s = encodeClause c ++ encodeCNF φ
  | .c, s => ∃ (n : ℕ) (c : Clause) (φ : CNF), s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | .d, s => ∃ (n : ℕ) (c : Clause) (φ : CNF),
      n ≠ 0 ∧ s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | _, _ => True

theorem enc_cons_cons (n : ℕ) (p : Bool) (c : Clause) (φ : CNF) :
    true :: p :: (vcode n ++ (encodeClause c ++ encodeCNF φ)) =
      encodeClause ((n, p) :: c) ++ encodeCNF φ := by
  simp [encodeClause, encodeLiteral_eq]

theorem good_of_accept : ∀ (s : List Bool) (q : WS), s.foldl wfD q = .a → Good q s
  | [], q, h => by
    cases q <;> first | trivial | exact ⟨[], rfl⟩
  | [x], q, h => by
    cases q <;> first | trivial | (cases x <;> simp [wfD] at h)
  | x :: y :: r, q, h => by
    have ih := good_of_accept r
    cases q
    case abT | abF | cT | cF | dead => trivial
    case a =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h
          exact ⟨[] :: φ, by simp [encodeCNF, encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨((n, y) :: c) :: φ, by rw [enc_cons_cons]; simp [encodeCNF]⟩
    case b =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h
          exact ⟨[], φ, by simp [encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨(n, y) :: c, φ, enc_cons_cons _ _ _ _⟩
    case c =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · obtain ⟨c, φ, rfl⟩ := ih _ h
        exact ⟨0, c, φ, by simp [vcode_zero]⟩
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩
    case d =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by simp [hn],
          by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by simp,
          by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩

/-- `wfB` accepts exactly the encodings of CNF formulas. -/
theorem wfB_iff (x : List Bool) : wfB x = true ↔ ∃ φ : CNF, encodeCNF φ = x := by
  rw [wfB, decide_eq_true_iff]
  constructor
  · intro h
    obtain ⟨φ, rfl⟩ := good_of_accept x .a h
    exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact foldl_cnf φ

/-- `wfB` as a finite-state transducer that writes one symbol at the end. -/
theorem wfB_eq_fstRun (x : List Bool) :
    bflag (wfB x) =
      fstRun (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
        (fun q => if q = WS.a then some true else none) WS.a x := by
  have key : ∀ (s : List Bool) (q : WS),
      fstRun (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
        (fun q => if q = WS.a then some true else none) q s =
      bflag (decide (s.foldl wfD q = .a)) := by
    intro s
    induction s with
    | nil => intro q; by_cases hq : q = .a <;> simp [fstRun, bflag, hq]
    | cons a s ih =>
      intro q
      simp only [fstRun, Option.toList_none, List.nil_append, List.foldl_cons]
      exact ih _
  rw [key, wfB]

/-! ### The verifier -/

/-- The verifier accepts `(x, w)` exactly when `x` encodes a formula that the assignment denoted
by `w` satisfies. -/
theorem SV_iff (x w : List Bool) :
    SV (x, w) = true ↔ ∃ φ : CNF, encodeCNF φ = x ∧ CNF.eval (asg w) φ = true := by
  simp only [SV, Bool.and_eq_true, wfB_iff]
  constructor
  · rintro ⟨⟨φ, rfl⟩, h⟩
    exact ⟨φ, rfl, by rw [← evalB_enc]; exact h⟩
  · rintro ⟨φ, rfl, h⟩
    exact ⟨⟨φ, rfl⟩, by rw [evalB_enc]; exact h⟩

/-! ### Witnesses -/

theorem dropI_iter_nil (j : ℕ) : dropI^[j] [] = [] := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact ih

theorem dropI_iter_codes (j : ℕ) : ∀ vs : List ℕ,
    dropI^[j] (vs.flatMap vcode) = (vs.drop j).flatMap vcode := by
  induction j with
  | zero => intro vs; rfl
  | succ j ih =>
    intro vs
    cases vs with
    | nil => simpa using dropI_iter_nil (j + 1)
    | cons v vs =>
      rw [Function.iterate_succ_apply, List.flatMap_cons, dropI_vcode, ih]
      rfl

theorem length_le_flatMap_vcode (vs : List ℕ) : vs.length ≤ (vs.flatMap vcode).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have := vcode_length_pos v
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- The witness that lists the variables `vs` denotes the assignment "is in `vs`". -/
theorem asg_codes (vs : List ℕ) (i : ℕ) : asg (vs.flatMap vcode) i = true ↔ i ∈ vs := by
  rw [asg, memB_iff]
  constructor
  · rintro ⟨j, -, h⟩
    rw [dropI_iter_codes] at h
    cases hd : vs.drop j with
    | nil =>
      rw [hd] at h
      exact absurd h.symm (vcode_ne_nil i)
    | cons v t =>
      rw [hd, List.flatMap_cons, headI_vcode] at h
      have hv : v ∈ vs.drop j := by rw [hd]; exact List.mem_cons_self
      rw [← vcode_injective h]
      exact List.mem_of_mem_drop hv
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    refine ⟨j, lt_of_lt_of_le hj (length_le_flatMap_vcode vs), ?_⟩
    rw [dropI_iter_codes, List.drop_eq_getElem_cons hj, List.flatMap_cons, headI_vcode]

/-- The true variables of a formula under an assignment, in order of occurrence. -/
def trueVars (σ : Assignment) (φ : CNF) : List ℕ :=
  ((φ.flatMap id).map Prod.fst).filter σ

/-- The witness for a formula and an assignment. -/
def wit (σ : Assignment) (φ : CNF) : List Bool := (trueVars σ φ).flatMap vcode

theorem length_filter_flatMap {α : Type} (p : α → Bool) (f : α → List Bool) (l : List α) :
    ((l.filter p).flatMap f).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons]
    split
    · simp only [List.flatMap_cons, List.length_append]; omega
    · simp only [List.flatMap_cons, List.length_append]; omega

theorem length_codes_clause (c : Clause) :
    ((c.map Prod.fst).flatMap vcode).length ≤ (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, encodeLiteral_eq,
      List.length_cons]
    omega

theorem length_codes_cnf (φ : CNF) :
    (((φ.flatMap id).map Prod.fst).flatMap vcode).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
    have := length_codes_clause c
    simp only [List.flatMap_cons, id_eq, List.map_append, List.flatMap_append,
      List.length_append, encodeCNF, encodeClause, List.length_cons, List.length_nil] at ih ⊢
    omega

/-- The witness is no longer than the encoding of the formula. -/
theorem wit_length (σ : Assignment) (φ : CNF) : (wit σ φ).length ≤ (encodeCNF φ).length :=
  (length_filter_flatMap _ _ _).trans (length_codes_cnf φ)

/-- The witness denotes an assignment with the same value on the formula. -/
theorem eval_wit (σ : Assignment) (φ : CNF) :
    CNF.eval (asg (wit σ φ)) φ = CNF.eval σ φ := by
  have key : ∀ c ∈ φ, ∀ l ∈ c, Literal.eval (asg (wit σ φ)) l = Literal.eval σ l := by
    intro c hc l hl
    have hmem : l.1 ∈ (φ.flatMap id).map Prod.fst :=
      List.mem_map.2 ⟨l, List.mem_flatMap.2 ⟨c, hc, hl⟩, rfl⟩
    have : asg (wit σ φ) l.1 = σ l.1 := by
      rw [Bool.eq_iff_iff, wit, asg_codes, trueVars, List.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
    simp [Literal.eval, this]
  rw [Bool.eq_iff_iff]
  simp only [CNF.eval, Clause.eval, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h c hc
    obtain ⟨l, hl, hv⟩ := h c hc
    exact ⟨l, hl, by rw [← key c hc l hl]; exact hv⟩
  · intro h c hc
    obtain ⟨l, hl, hv⟩ := h c hc
    exact ⟨l, hl, by rw [key c hc l hl]; exact hv⟩

/-! ### SAT -/

/-- `SV` characterizes SAT with witnesses no longer than the input. -/
theorem SV_spec (x : List Bool) :
    x ∈ PEqualNP.Search.SAT ↔ ∃ w : List Bool, w.length ≤ x.length ∧ SV (x, w) = true := by
  constructor
  · rintro ⟨φ, rfl, σ, hσ⟩
    exact ⟨wit σ φ, wit_length σ φ, (SV_iff _ _).2 ⟨φ, rfl, by rw [eval_wit]; exact hσ⟩⟩
  · rintro ⟨w, -, h⟩
    obtain ⟨φ, hφ, hv⟩ := (SV_iff _ _).1 h
    exact ⟨φ, hφ, asg w, hv⟩

/-- SAT is in NP as soon as the verifier `SV` is computable in polynomial time. -/
theorem SAT_in_NP_of (h : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
    Computability.encodeBool SV) : PEqualNP.Search.SAT ∈ PEqualNP.Library.NP := by
  refine ⟨{p | SV p = true}, Polynomial.X, ⟨SV, fun _ => Iff.rfl, h⟩, fun x => ?_⟩
  rw [SV_spec]
  simp

end PEqualNP.Library.SearchHelpers.SatV
