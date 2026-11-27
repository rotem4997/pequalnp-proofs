import PEqualNP.CircuitLowerBounds.Helpers.SatSlice

/-!
# The SAT slice at length `4 k + 2`: witness strings

Helper module (proofs only, no statement may use it). The string of length `4 k + 2` is read
as `k` blocks of four bits and a last pair. The standard string of `α` (a list of `k` bits) is
`[1, α_0, 0, 1] ... [1, α_(k-1), 0, 1] [0, 0]`: one clause of the literals `x0` with
polarities `α`. The bits at positions `4 r + 1` are the `α_r`. Every witness here is in SAT,
and the string with one bit flipped is not:

* (A), `r = 0`: the formula `(x0) (x0) (x0 ∨ ... ∨ x0)` against `(¬ x0) (x0) (...)`.
* (A), `r ≥ 1`: block `r - 1` and block `r` form the literal `(3, α_(r-1))`; flipping
  position `4 r + 1` leaves the last digit `0`, a leading zero.
* (C): the standard string, except for the bit `4 r + 2` when `α_(r+1) = 1`, where blocks `r`
  and `r + 1` form the literal `(2, α_r)`; the flipped bit then ends a clause inside a literal.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.SatFive

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.CircuitLowerBounds.Helpers.SatSlice

/-- The block of one literal `x0` with polarity `b`. -/
def blk (b : Bool) : List Bool := [true, b, false, true]

/-- The blocks of a list of polarities. -/
def fm (A : List Bool) : List Bool := A.flatMap blk

theorem fm_nil : fm [] = [] := rfl

theorem fm_cons (b : Bool) (A : List Bool) : fm (b :: A) = blk b ++ fm A := by
  simp [fm]

theorem fm_length (A : List Bool) : (fm A).length = 4 * A.length := by
  induction A with
  | nil => rfl
  | cons b A ih => rw [fm_cons, List.length_append, ih]; simp [blk]; omega

theorem fm_eq (A : List Bool) :
    fm A = (A.map fun b => ((0 : ℕ), b)).flatMap encodeLiteral := by
  induction A with
  | nil => rfl
  | cons b A ih => rw [fm_cons, ih]; simp [blk, encodeLiteral]

theorem getD_fm (A rest : List Bool) : ∀ r : ℕ, r < A.length →
    (fm A ++ rest).getD (4 * r + 1) false = A.getD r false := by
  induction A with
  | nil => intro r h; simp at h
  | cons b A ih =>
    intro r h
    rw [fm_cons, List.append_assoc]
    cases r with
    | zero => simp [blk]
    | succ r =>
      have e : 4 * (r + 1) + 1 = 4 * r + 1 + 4 := by omega
      rw [e, List.getD_append_right _ _ _ _ (by simp [blk])]
      simp only [blk, List.length_cons, List.length_nil]
      rw [show 4 * r + 1 + 4 - (0 + 1 + 1 + 1 + 1) = 4 * r + 1 by omega, ih r (by simpa using h)]
      simp

theorem getD_fm_shift (A rest : List Bool) (j : ℕ) :
    (fm A ++ rest).getD (4 * A.length + j) false = rest.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by rw [fm_length]; omega), fm_length]
  congr 1; omega

/-- The bits at positions `4 r + 1` of `fm A ++ m ++ fm B ++ z`, `m` of length 4 with bit `b`
at position 1, are those of `A ++ b :: B`. -/
theorem agree (A B z m : List Bool) (b : Bool) (hm : m.length = 4) (hb : m.getD 1 false = b) :
    ∀ j : ℕ, j < A.length + 1 + B.length →
      (fm A ++ (m ++ (fm B ++ z))).getD (4 * j + 1) false = (A ++ b :: B).getD j false := by
  intro j hj
  rcases Nat.lt_trichotomy j A.length with h | h | h
  · rw [getD_fm _ _ j h, List.getD_append _ _ _ _ h]
  · subst h
    rw [getD_fm_shift, List.getD_append _ _ _ _ (by omega), hb]
    simp
  · obtain ⟨t, rfl⟩ : ∃ t, j = A.length + 1 + t := ⟨j - A.length - 1, by omega⟩
    rw [show 4 * (A.length + 1 + t) + 1 = 4 * A.length + (4 + (4 * t + 1)) by omega,
      getD_fm_shift, List.getD_append_right _ _ _ _ (by omega), hm,
      show 4 + (4 * t + 1) - 4 = 4 * t + 1 by omega, getD_fm _ _ t (by omega),
      List.getD_append_right _ _ _ _ (by omega),
      show A.length + 1 + t - A.length = t + 1 by omega]
    simp

/-- A single clause with the literal `l` among literals `x0` is in SAT. -/
theorem mem_one (A B : List Bool) (l : Literal) :
    fm A ++ (encodeLiteral l ++ (fm B ++ [false, false])) ∈ SAT := by
  refine ⟨[(A.map fun b => ((0 : ℕ), b)) ++ l :: (B.map fun b => ((0 : ℕ), b))], ?_,
    fun _ => l.2, ?_⟩
  · simp [encodeCNF, encodeClause, fm_eq]
  · simp [CNF.eval, Clause.eval, Literal.eval]

/-- The run of the acceptor over blocks: from the start state it ends in `a` or `b`. -/
theorem fold_fm (A S : List Bool) :
    ∃ q, (q = WS.a ∨ q = WS.b) ∧ (fm A ++ S).foldl wfD .a = S.foldl wfD q := by
  induction A generalizing S with
  | nil => exact ⟨.a, Or.inl rfl, rfl⟩
  | cons b A ih =>
    refine ⟨.b, Or.inr rfl, ?_⟩
    rw [fm_cons, List.append_assoc, List.foldl_append]
    have : (blk b).foldl wfD .a = .b := by simp [blk, wfD]
    rw [this]
    clear ih
    induction A generalizing S with
    | nil => rfl
    | cons c A ih =>
      rw [fm_cons, List.append_assoc, List.foldl_append]
      have : (blk c).foldl wfD .b = .b := by simp [blk, wfD]
      rw [this, ih]

theorem not_sat_of (x : List Bool) (h : x.foldl wfD .a ≠ .a) : x ∉ SAT := by
  rintro ⟨φ, rfl, _⟩
  exact h (foldl_cnf φ)

/-- A string of blocks followed by a part that kills the acceptor from `a` and from `b`. -/
theorem not_sat_dead (A M R : List Bool) (ha : M.foldl wfD .a = .dead)
    (hb : M.foldl wfD .b = .dead) : fm A ++ (M ++ R) ∉ SAT := by
  apply not_sat_of
  obtain ⟨q, hq, e⟩ := fold_fm A (M ++ R)
  rw [e, List.foldl_append]
  rcases hq with rfl | rfl
  · rw [ha, foldl_dead]; simp
  · rw [hb, foldl_dead]; simp

theorem not_sat_end (A M : List Bool) (ha : M.foldl wfD .a ≠ .a)
    (hb : M.foldl wfD .b ≠ .a) : fm A ++ M ∉ SAT := by
  apply not_sat_of
  obtain ⟨q, hq, e⟩ := fold_fm A M
  rw [e]
  rcases hq with rfl | rfl
  · exact ha
  · exact hb

theorem exists_split (α : List Bool) (r : ℕ) (h : r < α.length) :
    ∃ A b B, α = A ++ b :: B ∧ A.length = r :=
  ⟨α.take r, α[r], α.drop (r + 1), by rw [List.getElem_cons_drop, List.take_append_drop],
    by simp; omega⟩

theorem flip_mid (P M R : List Bool) (j : ℕ) (hj : j < M.length) :
    (P ++ (M ++ R)).set (P.length + j) (!(P ++ (M ++ R)).getD (P.length + j) false)
      = P ++ (M.set j (!M.getD j false) ++ R) := by
  have e : (P ++ (M ++ R)).getD (P.length + j) false = M.getD j false := by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ hj]
  rw [e, ← List.append_assoc, set_mid _ _ _ _ _ hj, List.append_assoc]

theorem blk_eq (b : Bool) : blk b = encodeLiteral (0, b) := by
  simp [blk, encodeLiteral]

theorem lit2_eq (b : Bool) :
    encodeLiteral (2, b) = [true, b, true, false, true, true, false, true] := by
  have : Nat.bits 2 = [false, true] := by
    rw [show (2 : ℕ) = Nat.bit false 1 from rfl, Nat.bits_append_bit _ _ (by simp)]
    simp
  simp [encodeLiteral, this]

theorem lit3_eq (b : Bool) :
    encodeLiteral (3, b) = [true, b, true, true, true, true, false, true] := by
  have : Nat.bits 3 = [true, true] := by
    rw [show (3 : ℕ) = Nat.bit true 1 from rfl, Nat.bits_append_bit _ _ (by simp)]
    simp
  simp [encodeLiteral, this]

theorem std_mem (α : List Bool) (h : α ≠ []) : fm α ++ [false, false] ∈ SAT := by
  obtain ⟨b, B, rfl⟩ := List.exists_cons_of_ne_nil h
  have := mem_one [] B (0, b)
  rw [fm_cons, List.append_assoc, blk_eq]
  simpa [fm_nil] using this

/-- (C) at the level of strings: every bit outside the positions `4 r + 1` (but the last bit)
matters, whatever the bits at those positions. -/
theorem condC (α : List Bool) (hα : α ≠ []) (i : ℕ) (hi : i < 4 * α.length + 2)
    (h1 : i % 4 ≠ 1 ∨ i = 4 * α.length + 1) :
    ∃ l : List Bool, l.length = 4 * α.length + 2 ∧
      (∀ j, j < α.length → l.getD (4 * j + 1) false = α.getD j false) ∧
      l ∈ SAT ∧ l.set i (!l.getD i false) ∉ SAT := by
  by_cases hbig : 4 * α.length ≤ i
  · refine ⟨fm α ++ ([false, false] ++ []), by simp [fm_length], fun j hj => ?_,
      by simpa using std_mem α hα, ?_⟩
    · exact getD_fm _ _ j hj
    · obtain ⟨j, rfl, hj⟩ : ∃ j, i = (fm α).length + j ∧ j < 2 :=
        ⟨i - 4 * α.length, by rw [fm_length]; omega, by omega⟩
      rw [flip_mid _ _ _ _ (by simpa using hj)]
      apply not_sat_end
      · interval_cases j <;> simp [wfD]
      · interval_cases j <;> simp [wfD]
  · obtain ⟨A, b, B, rfl, hA⟩ := exists_split α (i / 4) (by simp at hbig ⊢; omega)
    have hlen : (A ++ b :: B).length = A.length + 1 + B.length := by simp; omega
    have hj : (i % 4 = 0 ∨ i % 4 = 3) ∨ i % 4 = 2 := by
      rcases h1 with h | h
      · omega
      · omega
    have hi4 : i = (fm A).length + i % 4 := by rw [fm_length, hA]; omega
    rcases hj with hj | hj
    · refine ⟨fm A ++ (blk b ++ (fm B ++ [false, false])), ?_, ?_, ?_, ?_⟩
      · simp [fm_length, blk]; omega
      · rw [hlen]; exact agree A B _ _ b (by simp [blk]) (by simp [blk])
      · rw [blk_eq]; exact mem_one A B _
      · rw [hi4]
        rcases hj with hj | hj <;> rw [hj, flip_mid _ _ _ _ (by simp [blk])] <;>
          apply not_sat_dead <;> cases b <;> simp [blk, wfD]
    · cases B with
      | nil =>
        refine ⟨fm A ++ (blk b ++ (fm [] ++ [false, false])), ?_, ?_, ?_, ?_⟩
        · simp [fm_length, blk]; omega
        · rw [hlen]; exact agree A [] _ _ b (by simp [blk]) (by simp [blk])
        · rw [blk_eq]; exact mem_one A [] _
        · have e : fm A ++ (blk b ++ (fm [] ++ [false, false]))
              = fm A ++ ((blk b ++ [false, false]) ++ []) := by simp [fm_nil]
          rw [e, hi4, hj, flip_mid _ _ _ _ (by simp [blk])]
          apply not_sat_dead <;> cases b <;> simp [blk, wfD]
      | cons c B =>
        cases c with
        | false =>
          refine ⟨fm A ++ (blk b ++ (fm (false :: B) ++ [false, false])), ?_, ?_, ?_, ?_⟩
          · simp [fm_length, blk]; omega
          · rw [hlen]; exact agree A _ _ _ b (by simp [blk]) (by simp [blk])
          · rw [blk_eq]; exact mem_one A _ _
          · have e : fm A ++ (blk b ++ (fm (false :: B) ++ [false, false]))
                = fm A ++ ((blk b ++ blk false) ++ (fm B ++ [false, false])) := by
              simp [fm_cons]
            rw [e, hi4, hj, flip_mid _ _ _ _ (by simp [blk])]
            apply not_sat_dead <;> cases b <;> simp [blk, wfD]
        | true =>
          refine ⟨fm A ++ ([true, b, true, false] ++ (fm (true :: B) ++ [false, false])),
            ?_, ?_, ?_, ?_⟩
          · simp [fm_length]; omega
          · rw [hlen]; exact agree A _ _ _ b (by simp) (by simp)
          · have e : fm A ++ ([true, b, true, false] ++ (fm (true :: B) ++ [false, false]))
                = fm A ++ (encodeLiteral (2, b) ++ (fm B ++ [false, false])) := by
              rw [lit2_eq, fm_cons]; simp [blk]
            rw [e]; exact mem_one A B _
          · rw [hi4, hj, flip_mid _ _ _ _ (by simp)]
            apply not_sat_dead <;> cases b <;> simp [wfD]

theorem getD_split_prefix (A X Y : List Bool) (c : Bool) (j : ℕ) (hj : j < A.length + 1) :
    (A ++ c :: X).getD j false = (A ++ c :: Y).getD j false := by
  rcases Nat.lt_or_ge j A.length with h | h
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_append_right _ _ _ _ h,
      show j - A.length = 0 by omega]
    simp

/-- (A) at the level of strings, for `r ≥ 1`: whatever the bits at positions `4 j + 1` for
`j < r`, the bit at `4 r + 1` matters. -/
theorem condA (α : List Bool) (r : ℕ) (h1 : 1 ≤ r) (hr : r < α.length) :
    ∃ l : List Bool, l.length = 4 * α.length + 2 ∧
      (∀ j, j < r → l.getD (4 * j + 1) false = α.getD j false) ∧
      l ∈ SAT ∧ l.set (4 * r + 1) (!l.getD (4 * r + 1) false) ∉ SAT := by
  obtain ⟨A, c, B, rfl, hA⟩ := exists_split α (r - 1) (by omega)
  cases B with
  | nil => simp at hr; omega
  | cons b B =>
    refine ⟨fm A ++ ([true, c, true, true] ++ (fm (true :: B) ++ [false, false])),
      ?_, ?_, ?_, ?_⟩
    · simp [fm_length]; omega
    · intro j hj
      rw [agree A _ _ _ c (by simp) (by simp) j (by simp; omega)]
      exact getD_split_prefix A _ _ c j (by omega)
    · have e : fm A ++ ([true, c, true, true] ++ (fm (true :: B) ++ [false, false]))
          = fm A ++ (encodeLiteral (3, c) ++ (fm B ++ [false, false])) := by
        rw [lit3_eq, fm_cons]; simp [blk]
      rw [e]; exact mem_one A B _
    · have e : fm A ++ ([true, c, true, true] ++ (fm (true :: B) ++ [false, false]))
          = fm A ++ ([true, c, true, true, true, true, false, true] ++ (fm B ++ [false, false])) := by
        rw [fm_cons]; simp [blk]
      have hi : 4 * r + 1 = (fm A).length + 5 := by rw [fm_length]; omega
      rw [e, hi, flip_mid _ _ _ _ (by simp)]
      apply not_sat_dead <;> cases c <;> simp [wfD]

/-- (A) at the level of strings, for `r = 0` and `k ≥ 4`: the formula
`(x0) (x0) (x0 ∨ ... ∨ x0)` is satisfiable, and with the first polarity flipped it is not. -/
theorem condA0 (k : ℕ) (hk : 4 ≤ k) :
    ∃ l : List Bool, l.length = 4 * k + 2 ∧ l ∈ SAT ∧ l.set 1 (!l.getD 1 false) ∉ SAT := by
  set R := encodeCNF [[((0 : ℕ), true)], List.replicate (k - 3) ((0 : ℕ), true)] with hR
  have hRl : R.length = 4 * k - 4 := by
    have : (List.replicate (k - 3) ((0 : ℕ), true)).flatMap encodeLiteral
        = fm (List.replicate (k - 3) true) := by
      rw [fm_eq]; simp
    simp [hR, encodeCNF, encodeClause, encodeLiteral, this, fm_length]
    omega
  refine ⟨encodeCNF ([((0 : ℕ), true)] :: [[((0 : ℕ), true)],
    List.replicate (k - 3) ((0 : ℕ), true)]), ?_, ?_, ?_⟩
  · rw [show encodeCNF ([((0 : ℕ), true)] :: [[((0 : ℕ), true)],
      List.replicate (k - 3) ((0 : ℕ), true)]) = [true, true, false, true, false, false] ++ R by
      simp [hR, encodeCNF, encodeClause, encodeLiteral]]
    simp [hRl]; omega
  · refine ⟨_, rfl, fun _ => true, ?_⟩
    simp [CNF.eval, Clause.eval, Literal.eval]
    omega
  · rintro ⟨φ, hφ, σ, hσ⟩
    have e : (encodeCNF ([((0 : ℕ), true)] :: [[((0 : ℕ), true)],
        List.replicate (k - 3) ((0 : ℕ), true)])).set 1 (!(encodeCNF ([((0 : ℕ), true)] ::
          [[((0 : ℕ), true)], List.replicate (k - 3) ((0 : ℕ), true)])).getD 1 false)
        = encodeCNF ([((0 : ℕ), false)] :: [[((0 : ℕ), true)],
          List.replicate (k - 3) ((0 : ℕ), true)]) := by
      simp [encodeCNF, encodeClause, encodeLiteral]
    rw [e] at hφ
    have := PEqualNP.Library.SearchHelpers.encodeCNF_injective hφ
    subst this
    simp [CNF.eval, Clause.eval, Literal.eval] at hσ
    obtain ⟨h1, h2, _⟩ := hσ
    rw [h1] at h2
    exact absurd h2 (by decide)

end PEqualNP.CircuitLowerBounds.Helpers.SatFive
