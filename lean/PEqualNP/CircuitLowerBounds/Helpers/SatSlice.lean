import PEqualNP.Library.SearchHelpers.SatVerifier
import PEqualNP.MetaComplexity.L011

/-!
# Every input bit of the SAT slice at length `6 * q` matters

Helper module (proofs only, no statement may use it). The base point is the encoding of the
formula with `q` copies of the unit clause `¬ x0`: the block `[1,0, 0,1, 0,0]` written `q`
times. It is satisfiable. Flipping the sign bit (offset 1) of one block gives a formula with
both `x0` and `¬ x0` as unit clauses (`q ≥ 2`), which is unsatisfiable. Flipping any other bit
gives a string that the well-formedness acceptor `wfD` of the SAT verifier rejects, so it
encodes no formula. Then a circuit for the slice depends on all inputs and has at least
`6 * q - 1` gates (`L011`), and no linear size with slope below one decides SAT.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.SatSlice

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV

/-- The unit clause `¬ x0`. -/
def c0 : Clause := [(0, false)]

/-- The unit clause `x0`. -/
def c1 : Clause := [(0, true)]

/-- The base string: `q` copies of the code of `c0`. -/
def base (q : ℕ) : List Bool := encodeCNF (List.replicate q c0)

theorem enc_c0 : encodeClause c0 = [true, false, false, true, false, false] := by
  simp [encodeClause, c0, encodeLiteral]

theorem enc_c1 : encodeClause c1 = [true, true, false, true, false, false] := by
  simp [encodeClause, c1, encodeLiteral]

theorem base_succ (m : ℕ) : base (m + 1) = [true, false, false, true, false, false] ++ base m := by
  simp [base, encodeCNF, List.replicate_succ, enc_c0]

theorem base_add (k m : ℕ) : base (k + m) = base k ++ base m := by
  unfold base encodeCNF
  rw [List.replicate_add, List.flatMap_append]

theorem base_length (q : ℕ) : (base q).length = 6 * q := by
  induction q with
  | zero => rfl
  | succ m ih => rw [base_succ, List.length_append, ih]; simp; omega

theorem base_sat (q : ℕ) : base q ∈ SAT := by
  refine ⟨List.replicate q c0, rfl, fun _ => false, ?_⟩
  simp [CNF.eval, c0, Clause.eval, Literal.eval]

theorem set_mid (A B C : List Bool) (r : ℕ) (v : Bool) (hr : r < B.length) :
    (A ++ B ++ C).set (A.length + r) v = A ++ B.set r v ++ C := by
  rw [List.append_assoc, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.set_append_left _ _ hr, List.append_assoc]

theorem getElem_mid (A B C : List Bool) (r : ℕ) (hr : r < B.length) (h) :
    (A ++ B ++ C)[A.length + r]'h = B[r] := by
  simp only [List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp [List.getElem_append_left hr]

/-- The string with one bit flipped is not in SAT. -/
theorem flip_not_sat (q : ℕ) (hq : 2 ≤ q) (i : ℕ) (hi : i < 6 * q) :
    (base q).set i (!((base q)[i]'(by rw [base_length]; exact hi))) ∉ SAT := by
  obtain ⟨k, r, m, hr, rfl, rfl⟩ : ∃ k r m, r < 6 ∧ i = 6 * k + r ∧ q = k + 1 + m :=
    ⟨i / 6, i % 6, q - i / 6 - 1, Nat.mod_lt _ (by omega), (Nat.div_add_mod i 6).symm,
      by omega⟩
  have e : base (k + 1 + m) = base k ++ [true, false, false, true, false, false] ++ base m := by
    have b0 : base 0 = [] := rfl
    rw [base_add, base_add, base_succ, b0]; simp
  have hk : (base k).length = 6 * k := base_length k
  simp only [e]
  simp only [← hk]
  rw [getElem_mid _ _ _ r (by simpa using hr), set_mid _ _ _ r _ (by simpa using hr)]
  rintro ⟨φ, hφ, hsat⟩
  have hacc := foldl_cnf φ
  rw [hφ, List.foldl_append, List.foldl_append] at hacc
  have h0 : (base k).foldl wfD .a = .a := foldl_cnf _
  rw [h0] at hacc
  interval_cases r <;>
    simp only [List.set_cons_succ, List.set_cons_zero, List.getElem_cons_succ,
      List.getElem_cons_zero, Bool.not_true, Bool.not_false] at hφ hacc
  · simp [wfD, foldl_dead] at hacc
  · -- the sign bit: the formula has both unit clauses
    have e1 : base k ++ [true, true, false, true, false, false] ++ base m =
        encodeCNF (List.replicate k c0 ++ c1 :: List.replicate m c0) := by
      simp [base, encodeCNF, enc_c1]
    rw [e1] at hφ
    have := PEqualNP.Library.SearchHelpers.encodeCNF_injective hφ
    subst this
    obtain ⟨σ, hσ⟩ := hsat
    have hc1 : Clause.eval σ c1 = true := by
      simp only [CNF.eval, List.all_eq_true] at hσ; exact hσ c1 (by simp)
    have hc0 : Clause.eval σ c0 = true := by
      simp only [CNF.eval, List.all_eq_true] at hσ
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · exact hσ c0 (by simp; omega)
      · exact hσ c0 (by simp; omega)
    simp [Clause.eval, Literal.eval, c0, c1] at hc0 hc1
    simp [hc1] at hc0
  · simp [wfD, foldl_dead] at hacc
  · simp [wfD, foldl_dead] at hacc
  · cases m with
    | zero => simp [wfD, base, encodeCNF] at hacc
    | succ m => simp [wfD, base_succ, foldl_dead] at hacc
  · simp [wfD, foldl_dead] at hacc

theorem ofFn_update {n : ℕ} (x : Fin n → Bool) (i : Fin n) (v : Bool) :
    List.ofFn (Function.update x i v) = (List.ofFn x).set i v := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply]
  by_cases hij : (i : ℕ) = j
  · have : (⟨j, by simpa using h1⟩ : Fin n) = i := Fin.ext hij.symm
    simp [this, hij]
  · have : (⟨j, by simpa using h1⟩ : Fin n) ≠ i := fun h => hij (by rw [← h])
    simp [this, hij]

/-- S1: every input bit of the SAT slice at length `6 * q` matters. -/
theorem s1 : ∀ q : ℕ, 2 ≤ q → ∀ i : Fin (6 * q), ∃ x : Fin (6 * q) → Bool,
    (List.ofFn (Function.update x i (!x i)) ∈ PEqualNP.Search.SAT ↔
      List.ofFn x ∉ PEqualNP.Search.SAT) := by
  intro q hq i
  have hl : (base q).length = 6 * q := base_length q
  refine ⟨fun j => (base q)[j.1]'(by rw [hl]; exact j.2), ?_⟩
  have hx : List.ofFn (fun j : Fin (6 * q) => (base q)[j.1]'(by rw [hl]; exact j.2)) = base q :=
    List.ext_getElem (by simp [hl]) (fun j _ _ => by simp)
  rw [ofFn_update, hx]
  have := flip_not_sat q hq i i.2
  constructor
  · intro h; exact absurd h this
  · intro h; exact absurd (base_sat q) h

/-- S2 from S1: a fan-in two circuit for the SAT slice at length `6 * q` has at least
`6 * q - 1` gates. -/
theorem s2_of (h1 : ∀ q : ℕ, 2 ≤ q → ∀ i : Fin (6 * q), ∃ x : Fin (6 * q) → Bool,
    (List.ofFn (Function.update x i (!x i)) ∈ PEqualNP.Search.SAT ↔
      List.ofFn x ∉ PEqualNP.Search.SAT)) :
    ∀ q : ℕ, 2 ≤ q → ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      D.Decides PEqualNP.Search.SAT (6 * q) → 6 * q ≤ D.size + 1 := by
  intro q hq D hD hdec
  refine PEqualNP.MetaComplexity.L011 (6 * q) (fun x => D.eval (List.ofFn x)) ?_ D.size
    ⟨D, hD, le_rfl, fun _ => rfl⟩
  intro i
  obtain ⟨x, hx⟩ := h1 q hq i
  refine ⟨x, fun heq => ?_⟩
  have ha := hdec (List.ofFn (Function.update x i (!x i))) (by simp)
  have hb := hdec (List.ofFn x) (by simp)
  have heq' : D.eval (List.ofFn (Function.update x i (!x i))) = D.eval (List.ofFn x) := heq
  rw [heq'] at ha
  rw [← ha, ← hb] at hx
  simp at hx

/-- S3 from S2: no size `s` with `100 * s n ≤ 99 * n + c` puts SAT in `SIZE s`. -/
theorem s3_of (h2 : ∀ q : ℕ, 2 ≤ q → ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      D.Decides PEqualNP.Search.SAT (6 * q) → 6 * q ≤ D.size + 1) :
    ¬ ∃ (s : ℕ → ℕ) (c : ℕ), (∀ n : ℕ, 100 * s n ≤ 99 * n + c) ∧
      PEqualNP.Search.SAT ∈ PEqualNP.CircuitLowerBounds.SIZE s := by
  rintro ⟨s, c, hs, hS⟩
  obtain ⟨D, hD, hsz, hdec⟩ := hS (6 * (c + 100))
  have := h2 (c + 100) (by omega) D hD hdec
  have := hs (6 * (c + 100))
  omega

end PEqualNP.CircuitLowerBounds.Helpers.SatSlice
