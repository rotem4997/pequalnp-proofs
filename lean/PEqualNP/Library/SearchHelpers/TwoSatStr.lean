import PEqualNP.Library.SearchHelpers.TwoSat
import PEqualNP.Library.SearchHelpers.SatVerifier

/-!
# Helpers: the criterion for 2-SAT as a function on encodings

Helper module (proofs only, no statement may use it).

It defines a total decision function `dec` on bit strings from small named total functions and
proves `dec x = true` exactly when `x` is in 2-SAT (`dec_iff`). No machine appears here.

The string is read in items (`headI`, `dropI` of the verifier of SAT): an item is a literal or
the end-of-clause pair. A list of literals is the concatenation of its literal items (`encL`).
`stepS` is one rotation of `TwoSat.lean` on the packed state `pairB formula list`; `closS` runs
it `|x| * |x|` times; `chkStep` walks along the items of the input and records in a flag every
literal item that has its negation in its closure and itself in the closure of its negation.
`w2` is the width test: every clause has one or two literals.
-/

namespace PEqualNP.Library.SearchHelpers.TwoSat

open PEqualNP.Search PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV

/-! ### Lists of literals -/

/-- The code of a list of literals: its literal items in order. -/
def encL (L : List Literal) : List Bool := L.flatMap encodeLiteral

theorem encL_append (L L' : List Literal) : encL (L ++ L') = encL L ++ encL L' := by
  simp [encL]

/-- The literal item of the negation. -/
def negI (it : List Bool) : List Bool :=
  sel (bflag (polB it)) (true :: true :: it.tail.tail) (true :: false :: it.tail.tail)

theorem negI_lit (l : Literal) : negI (encodeLiteral l) = encodeLiteral (neg l) := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [negI, encodeLiteral_eq, polB, bflag, neg]

theorem negI_length (it : List Bool) : (negI it).length ≤ it.length + 2 := by
  unfold negI sel
  split <;> simp <;> omega

theorem dropI_iter_encL (j : ℕ) : ∀ L : List Literal,
    dropI^[j] (encL L) = encL (L.drop j) := by
  induction j with
  | zero => intro L; rfl
  | succ j ih =>
    intro L
    cases L with
    | nil => simpa [encL] using dropI_iter_nil (j + 1)
    | cons l L =>
      rw [Function.iterate_succ_apply, encL, List.flatMap_cons, dropI_lit]
      exact ih L

theorem length_le_encL (L : List Literal) : L.length ≤ (encL L).length :=
  length_le_flatMap_lit L

theorem encodeLiteral_injective : Function.Injective encodeLiteral := by
  intro l l' h
  have h' : encodeLiteral l ++ [] = encodeLiteral l' ++ [] := by simpa using h
  exact (literal_append_inj l l' [] [] h').1

theorem encodeLiteral_ne_nil (l : Literal) : encodeLiteral l ≠ [] := by
  simp [encodeLiteral_eq]

theorem memB_encL (l : Literal) (L : List Literal) :
    memB (encodeLiteral l) (encL L) = true ↔ l ∈ L := by
  rw [memB_iff]
  constructor
  · rintro ⟨j, -, h⟩
    rw [dropI_iter_encL] at h
    cases hd : L.drop j with
    | nil =>
      rw [hd] at h
      exact absurd h.symm (encodeLiteral_ne_nil l)
    | cons v t =>
      rw [hd, encL, List.flatMap_cons, headI_lit] at h
      have hv : v ∈ L.drop j := by rw [hd]; exact List.mem_cons_self
      rw [← encodeLiteral_injective h]
      exact List.mem_of_mem_drop hv
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    refine ⟨j, lt_of_lt_of_le hj (length_le_encL L), ?_⟩
    rw [dropI_iter_encL, List.drop_eq_getElem_cons hj, encL, List.flatMap_cons, headI_lit]

theorem memB_encL_eq (l : Literal) (L : List Literal) :
    memB (encodeLiteral l) (encL L) = decide (l ∈ L) := by
  rw [Bool.eq_iff_iff, memB_encL, decide_eq_true_iff]

/-! ### One rotation -/

/-- The item `g` when the negation of the item `h` is in the list `L`, else nothing. -/
def fw (h g L : List Bool) : List Bool := sel (bflag (memB (negI h) L)) [] g

theorem fw_lit (a b : Literal) (L : List Literal) :
    fw (encodeLiteral a) (encodeLiteral b) (encL L) = encL (if neg a ∈ L then [b] else []) := by
  rw [fw, negI_lit, memB_encL_eq]
  by_cases h : neg a ∈ L <;> simp [h, bflag, encL]

theorem fw_length (h g L : List Bool) : (fw h g L).length ≤ g.length := by
  unfold fw sel
  split <;> simp

/-- The rotation when the clause in front has two literals. -/
def binP (F L : List Bool) : List Bool :=
  pairB (dropI (dropI (dropI F)) ++ (headI F ++ (headI (dropI F) ++ headI (dropI (dropI F)))))
    (L ++ (fw (headI F) (headI (dropI F)) L ++ fw (headI (dropI F)) (headI F) L))

/-- The rotation when the clause in front has one literal. -/
def unitP (F L : List Bool) : List Bool :=
  pairB (dropI (dropI F) ++ (headI F ++ headI (dropI F))) (L ++ fw (headI F) (headI F) L)

/-- One rotation, on the code `F` of the formula and the code `L` of the list. -/
def stepP (F L : List Bool) : List Bool :=
  sel (bflag (isEnd (dropI F))) (binP F L) (unitP F L)

/-- One rotation on the packed state `pairB F L`. -/
def stepS (s : List Bool) : List Bool := stepP (unpairB s).1 (unpairB s).2

theorem enc_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by
  simp [encodeCNF]

theorem enc_append (φ ψ : CNF) : encodeCNF (φ ++ ψ) = encodeCNF φ ++ encodeCNF ψ := by
  simp [encodeCNF]

theorem headI_end (r : List Bool) : headI (false :: false :: r) = [false, false] := rfl

theorem dropI_end (r : List Bool) : dropI (false :: false :: r) = r := rfl

theorem stepP_nil (L : List Bool) : stepP [] L = pairB [] L := by
  simp [stepP, binP, dropI, headI, isEnd, bflag, fw, sel]

theorem stepP_unit (a : Literal) (F : CNF) (L : List Literal) :
    stepP (encodeCNF ([a] :: F)) (encL L) =
      pairB (encodeCNF (F ++ [[a]])) (encL (L ++ forced [a] L)) := by
  have e : encodeCNF ([a] :: F) = encodeLiteral a ++ (false :: false :: encodeCNF F) := by
    simp [encodeCNF, encodeClause]
  have e2 : encodeCNF (F ++ [[a]]) = encodeCNF F ++ (encodeLiteral a ++ [false, false]) := by
    simp [encodeCNF, encodeClause]
  rw [stepP, unitP, e, dropI_lit, headI_lit, headI_end, dropI_end, fw_lit, e2, encL_append]
  simp [isEnd, bflag, forced]

theorem stepP_bin (a b : Literal) (F : CNF) (L : List Literal) :
    stepP (encodeCNF ([a, b] :: F)) (encL L) =
      pairB (encodeCNF (F ++ [[a, b]])) (encL (L ++ forced [a, b] L)) := by
  have e : encodeCNF ([a, b] :: F) =
      encodeLiteral a ++ (encodeLiteral b ++ (false :: false :: encodeCNF F)) := by
    simp [encodeCNF, encodeClause]
  have e2 : encodeCNF (F ++ [[a, b]]) =
      encodeCNF F ++ (encodeLiteral a ++ (encodeLiteral b ++ [false, false])) := by
    simp [encodeCNF, encodeClause]
  rw [stepP, binP, e, dropI_lit, headI_lit, isEnd_lit, dropI_lit, headI_lit, headI_end,
    dropI_end, fw_lit, fw_lit, e2, encL_append, forced, encL_append]
  simp [bflag]

theorem stepS_rot (F : CNF) (hw : ∀ c ∈ F, c.length = 1 ∨ c.length = 2) (L : List Literal) :
    stepS (pairB (encodeCNF F) (encL L)) =
      pairB (encodeCNF (rot (F, L)).1) (encL (rot (F, L)).2) := by
  rw [stepS, unpairB_pairB]
  match F, hw with
  | [], _ => exact stepP_nil _
  | [] :: _, h => simpa using h [] List.mem_cons_self
  | [a] :: F, _ => exact stepP_unit a F L
  | [a, b] :: F, _ => exact stepP_bin a b F L
  | (_ :: _ :: _ :: _) :: _, h => simpa using h _ List.mem_cons_self

theorem rot_width (s : CNF × List Literal) (hw : ∀ c ∈ s.1, c.length = 1 ∨ c.length = 2) :
    ∀ c ∈ (rot s).1, c.length = 1 ∨ c.length = 2 := by
  obtain ⟨F, L⟩ := s
  cases F with
  | nil => exact hw
  | cons c F =>
    intro c' hc'
    simp only [rot, List.mem_append, List.mem_singleton] at hc'
    rcases hc' with hc' | rfl
    · exact hw c' (List.mem_cons_of_mem _ hc')
    · exact hw c' List.mem_cons_self

theorem stepS_iter (N : ℕ) : ∀ (s : CNF × List Literal),
    (∀ c ∈ s.1, c.length = 1 ∨ c.length = 2) →
    stepS^[N] (pairB (encodeCNF s.1) (encL s.2)) =
      pairB (encodeCNF (rot^[N] s).1) (encL (rot^[N] s).2) := by
  induction N with
  | zero => intro s _; rfl
  | succ N ih =>
    intro s hw
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepS_rot s.1 hw s.2]
    exact ih (rot s) (rot_width s hw)

/-- The closure of the literal item `a` in the formula coded by `x`. -/
def closS (x a : List Bool) : List Bool :=
  (unpairB (stepS^[(mulU x x).length] (pairB x a))).2

theorem closS_enc (φ : CNF) (hw : ∀ c ∈ φ, c.length = 1 ∨ c.length = 2) (a : Literal) :
    closS (encodeCNF φ) (encodeLiteral a) =
      encL (clos ((encodeCNF φ).length * (encodeCNF φ).length) φ a) := by
  have e : encodeLiteral a = encL [a] := by simp [encL]
  have h := stepS_iter ((encodeCNF φ).length * (encodeCNF φ).length) (φ, [a]) hw
  rw [closS, e]
  simp only [mulU, un_length]
  rw [h, unpairB_pairB]
  rfl

/-! ### The check along the items -/

/-- The literal item `it` has its negation in its closure and itself in the closure of its
negation. -/
def badI (x it : List Bool) : Bool :=
  memB (negI it) (closS x it) && memB it (closS x (negI it))

theorem badI_enc (φ : CNF) (hw : ∀ c ∈ φ, c.length = 1 ∨ c.length = 2) (l : Literal) :
    badI (encodeCNF φ) (encodeLiteral l) = true ↔
      (neg l ∈ clos ((encodeCNF φ).length * (encodeCNF φ).length) φ l ∧
        l ∈ clos ((encodeCNF φ).length * (encodeCNF φ).length) φ (neg l)) := by
  rw [badI, negI_lit, closS_enc φ hw, closS_enc φ hw, Bool.and_eq_true, memB_encL, memB_encL]

/-- One step of the check on the packed state `pairB x (pairB rest flag)`: the first item of
the rest is dropped, and the flag grows when that item is a literal item that is bad. -/
def chkStep (s : List Bool) : List Bool :=
  pairB (unpairB s).1 (pairB (dropI (unpairB (unpairB s).2).1)
    ((unpairB (unpairB s).2).2 ++ sel (unpairB (unpairB s).2).1 []
      (sel (bflag (isEnd (unpairB (unpairB s).2).1))
        (bflag (badI (unpairB s).1 (headI (unpairB (unpairB s).2).1))) [])))

theorem chkStep_lit (x : List Bool) (l : Literal) (r b : List Bool) :
    chkStep (pairB x (pairB (encodeLiteral l ++ r) b)) =
      pairB x (pairB r (b ++ bflag (badI x (encodeLiteral l)))) := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [chkStep, unpairB_pairB, dropI_lit, headI_lit, isEnd_lit]
  simp [sel, bflag, hne]

theorem chkStep_end (x r b : List Bool) :
    chkStep (pairB x (pairB (false :: false :: r) b)) = pairB x (pairB r b) := by
  simp [chkStep, unpairB_pairB, dropI, isEnd, bflag, sel]

theorem chkStep_nil (x b : List Bool) :
    chkStep (pairB x (pairB [] b)) = pairB x (pairB [] b) := by
  simp [chkStep, unpairB_pairB, dropI, sel]

theorem chkStep_nil_iter (x b : List Bool) (k : ℕ) :
    chkStep^[k] (pairB x (pairB [] b)) = pairB x (pairB [] b) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, chkStep_nil, ih]

theorem chkStep_clause (x : List Bool) : ∀ (c : Clause) (r b : List Bool), ∃ b' : List Bool,
    chkStep^[c.length + 1] (pairB x (pairB (encodeClause c ++ r) b)) = pairB x (pairB r b') ∧
      (b' = [] ↔ b = [] ∧ ∀ l ∈ c, badI x (encodeLiteral l) = false) := by
  intro c
  induction c with
  | nil =>
    intro r b
    refine ⟨b, ?_, by simp⟩
    simp [encodeClause, chkStep_end]
  | cons l c ih =>
    intro r b
    obtain ⟨b', h1, h2⟩ := ih r (b ++ bflag (badI x (encodeLiteral l)))
    refine ⟨b', ?_, ?_⟩
    · have e : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
        simp [encodeClause]
      rw [List.length_cons, Function.iterate_succ_apply, e, chkStep_lit, h1]
    · rw [h2]
      simp only [List.append_eq_nil_iff, bflag_eq_nil, List.mem_cons, forall_eq_or_imp,
        and_assoc]

theorem chkStep_cnf (x : List Bool) : ∀ (ψ : CNF) (b : List Bool), ∃ b' : List Bool,
    chkStep^[nIt ψ] (pairB x (pairB (encodeCNF ψ) b)) = pairB x (pairB [] b') ∧
      (b' = [] ↔ b = [] ∧ ∀ c ∈ ψ, ∀ l ∈ c, badI x (encodeLiteral l) = false) := by
  intro ψ
  induction ψ with
  | nil => intro b; exact ⟨b, rfl, by simp⟩
  | cons c ψ ih =>
    intro b
    obtain ⟨b1, h1, h2⟩ := chkStep_clause x c (encodeCNF ψ) b
    obtain ⟨b', h3, h4⟩ := ih b1
    refine ⟨b', ?_, ?_⟩
    · rw [nIt, Function.iterate_add_apply, enc_cons, h1, h3]
    · rw [h4, h2]
      simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-- No literal item of `x` is bad (on a well-formed `x`). -/
def chkB (x : List Bool) : Bool :=
  (unpairB (unpairB (chkStep^[x.length] (pairB x (pairB x [])))).2).2.isEmpty

theorem chkB_enc (φ : CNF) :
    chkB (encodeCNF φ) = true ↔
      ∀ c ∈ φ, ∀ l ∈ c, badI (encodeCNF φ) (encodeLiteral l) = false := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le' (nIt_le φ)
  obtain ⟨b', h1, h2⟩ := chkStep_cnf (encodeCNF φ) φ []
  rw [chkB, he, Function.iterate_add_apply, h1, chkStep_nil_iter]
  simp only [unpairB_pairB]
  rw [List.isEmpty_iff, h2]
  simp

/-! ### The width test -/

/-- The width test, with `n` literals already closed in the current clause: every clause has
one or two literals. -/
def w2 : ℕ → List Bool → Bool
  | _, [] => true
  | _, [_] => false
  | n, true :: _ :: r => w2 n r
  | n, false :: false :: r => decide (0 < n) && w2 0 r
  | n, false :: true :: r => decide (n < 2) && w2 (n + 1) r

theorem w2_digits (n : ℕ) (ds r : List Bool) :
    w2 n ((ds.flatMap fun d => [true, d]) ++ r) = w2 n r := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [w2, ih]

theorem w2_literal (n : ℕ) (l : Literal) (r : List Bool) :
    w2 n (encodeLiteral l ++ r) = (decide (n < 2) && w2 (n + 1) r) := by
  have h : encodeLiteral l ++ r =
      true :: l.2 :: ((l.1.bits.flatMap fun d => [true, d]) ++ false :: true :: r) := by
    simp [encodeLiteral]
  rw [h, w2, w2_digits, w2]

theorem w2_clause (r : List Bool) : ∀ (c : Clause) (n : ℕ), n ≤ 2 →
    w2 n (encodeClause c ++ r) =
      (decide (0 < n + c.length ∧ n + c.length ≤ 2) && w2 0 r)
  | [], n, hn => by
    have h : encodeClause [] ++ r = false :: false :: r := by simp [encodeClause]
    rw [h, w2]
    simp [hn]
  | l :: c, n, hn => by
    have h : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
      simp [encodeClause]
    rw [h, w2_literal]
    by_cases h2 : n < 2
    · rw [w2_clause r c (n + 1) (by omega)]
      have e : (0 < n + 1 + c.length ∧ n + 1 + c.length ≤ 2) ↔
          (0 < n + (l :: c).length ∧ n + (l :: c).length ≤ 2) := by
        simp only [List.length_cons]; omega
      rw [decide_eq_true h2, Bool.true_and, decide_eq_decide.2 e]
    · have e : ¬ (0 < n + (l :: c).length ∧ n + (l :: c).length ≤ 2) := by
        simp only [List.length_cons]; omega
      rw [decide_eq_false h2, decide_eq_false e]
      rfl

theorem w2_cnf : ∀ φ : CNF,
    w2 0 (encodeCNF φ) = true ↔ ∀ c ∈ φ, c.length = 1 ∨ c.length = 2
  | [] => by simp [encodeCNF, w2]
  | c :: φ => by
    rw [enc_cons, w2_clause _ c 0 (by omega)]
    have e : (0 < 0 + c.length ∧ 0 + c.length ≤ 2) ↔ (c.length = 1 ∨ c.length = 2) := by omega
    rw [Bool.and_eq_true, decide_eq_true_iff, w2_cnf φ, e]
    simp

/-! ### The decision -/

theorem size_le (φ : CNF) :
    (φ.flatMap id).length + 2 * φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
    have := length_le_flatMap_lit c
    simp only [encodeCNF, encodeClause, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil, id_eq] at ih ⊢
    omega

theorem rounds_le (φ : CNF) :
    φ.length * ((φ.flatMap id).length + 1) ≤ (encodeCNF φ).length * (encodeCNF φ).length := by
  have h := size_le φ
  rcases Nat.eq_zero_or_pos φ.length with h0 | h0
  · rw [h0]; simp
  · exact Nat.mul_le_mul (by omega) (by omega)

/-- The decision: `x` encodes a formula, every clause of it has one or two literals, and no
literal item of it is bad. -/
def dec (x : List Bool) : Bool := wfB x && (w2 0 x && chkB x)

theorem dec_enc (φ : CNF) (hw : ∀ c ∈ φ, c.length = 1 ∨ c.length = 2) :
    chkB (encodeCNF φ) = true ↔ Satisfiable φ := by
  rw [chkB_enc, sat_iff hw (rounds_le φ)]
  refine forall_congr' (fun c => forall_congr' (fun _ => forall_congr' (fun l =>
    forall_congr' (fun _ => ?_))))
  rw [← badI_enc φ hw l]
  simp

theorem dec_iff (x : List Bool) : dec x = true ↔ x ∈ KSAT 2 := by
  simp only [dec, Bool.and_eq_true]
  constructor
  · rintro ⟨hwf, hw, hc⟩
    obtain ⟨φ, rfl⟩ := (wfB_iff x).1 hwf
    have hw' := (w2_cnf φ).1 hw
    refine ⟨φ, fun c hc => ?_, rfl, (dec_enc φ hw').1 hc⟩
    rcases hw' c hc with h | h <;> omega
  · rintro ⟨φ, hk, rfl, hs⟩
    have hw' : ∀ c ∈ φ, c.length = 1 ∨ c.length = 2 := by
      intro c hc
      have h1 := hk c hc
      have h2 : c ≠ [] := by
        rintro rfl
        obtain ⟨σ, hσ⟩ := hs
        have := List.all_eq_true.1 hσ [] hc
        simp [Clause.eval] at this
      have h3 : 0 < c.length := List.length_pos_iff.2 h2
      omega
    exact ⟨(wfB_iff _).2 ⟨φ, rfl⟩, (w2_cnf φ).2 hw', (dec_enc φ hw').2 hs⟩

end PEqualNP.Library.SearchHelpers.TwoSat
