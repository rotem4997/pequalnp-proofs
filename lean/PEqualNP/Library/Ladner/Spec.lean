import PEqualNP.Library.Ladner.Defs
import PEqualNP.Library.Universal.Lazy

/-!
# The string functions of the delayed diagonal against their meaning

Helper module (proofs only, no statement may use it). No machines here: the capped power has
the stated length, the history has the prefix property, and the witness bit of the history of
length `n` is `true` exactly when the three budget conditions hold and the decider number
`stage n` differs from the language on the candidate string. From this: the stage moves by the
witness bit, the witness bit is sound, and a wrong decider is caught at arbitrarily late steps.
-/

namespace PEqualNP.Library.Ladner

open PEqualNP.Library.Universal

/-! ### Dropping and counting -/

theorem iterate_tail (k : ℕ) (l : List Bool) : List.tail^[k] l = l.drop k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l <;> simp

theorem dropU_eq (c a : List Bool) : dropU c a = a.drop c.length := iterate_tail _ _

theorem dropU_length (c a : List Bool) : (dropU c a).length = a.length - c.length := by
  rw [dropU_eq, List.length_drop]

theorem ones_append (a b : List Bool) : ones (a ++ b) = ones a ++ ones b :=
  List.filter_append ..

/-! ### The capped power -/

theorem tpAcc_length (s : List Bool) : (tpAcc s).length =
    min ((unpairB (unpairB s).2).1.length * (unpairB (unpairB s).2).2.length)
      (tpTot s).length := by
  have hm : (mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).2).length =
      (unpairB (unpairB s).2).1.length * (unpairB (unpairB s).2).2.length := by
    simp [mulU]
  unfold tpAcc leFlag sel
  rw [hm]
  by_cases h : (unpairB (unpairB s).2).1.length * (unpairB (unpairB s).2).2.length ≤
      (tpTot s).length
  · simp [h, hm]
  · simp [h]
    omega

theorem tpStep_pair (rest acc zz : List Bool) : ∃ rest' acc' : List Bool,
    tpStep (pairB rest (pairB acc zz)) = pairB rest' (pairB acc' zz) ∧
      acc'.length = min (acc.length * zz.length) (rest.length + acc.length) ∧
      rest'.length + acc'.length = rest.length + acc.length := by
  refine ⟨dropU (tpAcc (pairB rest (pairB acc zz))) (tpTot (pairB rest (pairB acc zz))),
    tpAcc (pairB rest (pairB acc zz)), ?_, ?_, ?_⟩
  · simp [tpStep, unpairB_pairB]
  · rw [tpAcc_length]
    simp [tpTot, unpairB_pairB]
  · rw [dropU_length, tpAcc_length]
    simp only [tpTot, unpairB_pairB, List.length_append]
    omega

theorem min_mul_min (a T p : ℕ) (hp : 1 ≤ p) : min (min a T * p) T = min (a * p) T := by
  rcases le_total a T with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    have h1 : T ≤ T * p := Nat.le_mul_of_pos_right _ hp
    have h2 : T ≤ a * p := h.trans (Nat.le_mul_of_pos_right _ hp)
    rw [min_eq_right h1, min_eq_right h2]

theorem tpStep_iter (zz : List Bool) (hz : 1 ≤ zz.length) (j : ℕ) :
    ∀ rest acc : List Bool, ∃ rest' acc' : List Bool,
      tpStep^[j] (pairB rest (pairB acc zz)) = pairB rest' (pairB acc' zz) ∧
        acc'.length = min (acc.length * zz.length ^ j) (rest.length + acc.length) := by
  induction j with
  | zero =>
    intro rest acc
    refine ⟨rest, acc, rfl, ?_⟩
    rw [pow_zero, mul_one]
    exact (min_eq_left (Nat.le_add_left _ _)).symm
  | succ j ih =>
    intro rest acc
    obtain ⟨r1, a1, h1, h2, h3⟩ := tpStep_pair rest acc zz
    obtain ⟨r2, a2, h4, h5⟩ := ih r1 a1
    refine ⟨r2, a2, by rw [Function.iterate_succ_apply, h1, h4], ?_⟩
    rw [h5, h3, h2, min_mul_min _ _ _ (Nat.one_le_pow _ _ hz)]
    have e : acc.length * zz.length * zz.length ^ j = acc.length * zz.length ^ (j + 1) := by
      rw [pow_succ]
      ring
    rw [e]

/-- The length of the capped power. -/
theorem tpw_length (zz k N : List Bool) (hz : 1 ≤ zz.length) :
    (tpw zz k N).length = min (zz.length ^ k.length) (N.length + 1) := by
  obtain ⟨r, a, h1, h2⟩ := tpStep_iter zz hz k.length N [true]
  rw [tpw, h1]
  simp only [unpairB_pairB]
  rw [h2]
  simp

/-! ### The history -/

section History

variable (cA : List Bool) (q : Polynomial ℕ)

theorem Hs_succ (n : ℕ) : Hs cA q (n + 1) = Hs cA q n ++ [Wb cA q (Hs cA q n)] := by
  rw [Hs, Function.iterate_succ_apply']
  rfl

theorem Hs_length (n : ℕ) : (Hs cA q n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Hs_succ, List.length_append, ih]; rfl

theorem Hs_take (n m : ℕ) (h : m ≤ n) : (Hs cA q n).take m = Hs cA q m := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with e | hlt
    · subst e
      rw [List.take_of_length_le (by rw [Hs_length])]
    · rw [Hs_succ, List.take_append_of_le_length (by rw [Hs_length]; omega), ih (by omega)]

/-- The stage moves by the witness bit. -/
theorem stage_succ (n : ℕ) : stage cA q (n + 1) =
    stage cA q n + (if Wb cA q (Hs cA q n) = true then 1 else 0) := by
  simp only [stage, Hs_succ, ones_append, List.length_append]
  cases Wb cA q (Hs cA q n) <;> rfl

theorem stg_length (n : ℕ) (u : List Bool) (hu : u.length ≤ n) :
    (stg u (Hs cA q n)).length = stage cA q u.length := by
  have e : ones (Hs cA q n) =
      ones ((Hs cA q n).take u.length) ++ ones ((Hs cA q n).drop u.length) := by
    rw [← ones_append, List.take_append_drop]
  rw [stg, dropU_length, dropU_eq, e, List.length_append, Hs_take _ _ _ _ hu,
    Nat.add_sub_cancel]
  rfl

theorem cz_Hs (n : ℕ) : cz (Hs cA q n) = (unpairB (cand n)).1 := by
  rw [cz, Hs_length]
  rfl

end History

theorem base_length (z : List Bool) : (base z).length = z.length + 2 := rfl

theorem rq_len (st : List Bool) : rq st = rq (un st.length) := by simp [rq]

theorem length_le_idx (s : List Bool) : s.length ≤ idx s := by
  induction s with
  | nil => simp [idx]
  | cons b r ih => cases b <;> simp [idx] <;> omega

/-! ### The exhaustive search -/

theorem srch_sound (F n : List Bool) (h : (!(srch F n).isEmpty) = true) :
    ∃ w, V (F, w) = true := by
  have e : ¬ srch F n = [] := by
    intro e
    rw [e] at h
    simp at h
  rw [srch_eq_nil] at e
  by_contra hc
  exact e (fun j _ => by
    cases hv : V (F, cand j) with
    | false => rfl
    | true => exact absurd ⟨cand j, hv⟩ hc)

theorem srch_complete (F n : List Bool) (hb : ∀ w, V (F, w) = true → idx w < n.length)
    (h : ∃ w, V (F, w) = true) : (!(srch F n).isEmpty) = true := by
  obtain ⟨w, hw⟩ := h
  have e : ¬ srch F n = [] := by
    rw [srch_eq_nil]
    intro h
    have h3 := h (idx w) (hb w hw)
    rw [cand_idx, hw] at h3
    exact Bool.noConfusion h3
  cases hs : srch F n with
  | nil => exact absurd hs e
  | cons a l => rfl

section Witness

variable (cA : List Bool) (q : Polynomial ℕ)

theorem qry_length (x : List Bool) : (qry cA q x).length =
    2 * cA.length + (2 * x.length + q.eval x.length + 1) + 1 := by
  simp [qry, pairB_length]

theorem qry_witness (x w : List Bool) (h : V (qry cA q x, w) = true) :
    idx w + 2 ≤ 2 ^ (qry cA q x).length := by
  have h1 : w.length ≤ q.eval x.length := by
    have := V_length _ _ _ _ h
    simpa using this
  have h2 := idx_bound w
  have h3 : 2 ^ (w.length + 1) ≤ 2 ^ (qry cA q x).length :=
    Nat.pow_le_pow_right (by norm_num) (by rw [qry_length]; omega)
  omega

theorem clk_length (n : ℕ) : (clk (Hs cA q n)).length =
    min (((cz (Hs cA q n)).length + 2) ^ stage cA q n) (n + 1) := by
  rw [clk, tpw_length _ _ _ (by simp [base]), Hs_length]
  simp [base, stage]

theorem lg_length (n : ℕ) : (lgU (mulU (Hs cA q n) [true])).length = Nat.size n := by
  simp [mulU, Hs_length, lgU_length]

theorem bne_and_iff (a b c : Bool) :
    ((a != (b && c)) = true) ↔ ¬ (a = true ↔ (b = true ∧ c = true)) := by
  cases a <;> cases b <;> cases c <;> simp

/-- Under the budget conditions the last conjunct of the witness bit says that the current
decider differs from the language on the candidate. -/
theorem body_iff (n : ℕ) (g0 : (psi (cz (Hs cA q n))).length ≤ n)
    (g1 : ((cz (Hs cA q n)).length + 2) ^ stage cA q n ≤ n)
    (g3 : (qry cA q (psi (cz (Hs cA q n)))).length + 2 ≤ Nat.size n) :
    (V (pairB (rq (ones (Hs cA q n))) (pairB (cz (Hs cA q n)) (clk (Hs cA q n))), []) !=
      (!(srch (qry cA q (psi (cz (Hs cA q n)))) (Hs cA q n)).isEmpty &&
        decide ((padOf (cz (Hs cA q n)) (Hs cA q n)).length ≤ (cz (Hs cA q n)).length))) = true ↔
      ¬ (Dd (stage cA q n) (cz (Hs cA q n)) = true ↔ cz (Hs cA q n) ∈ LL cA q) := by
  have hck : (clk (Hs cA q n)).length = ((cz (Hs cA q n)).length + 2) ^ stage cA q n := by
    rw [clk_length, min_eq_left (by omega)]
  have hD : V (pairB (rq (ones (Hs cA q n))) (pairB (cz (Hs cA q n)) (clk (Hs cA q n))), []) =
      Dd (stage cA q n) (cz (Hs cA q n)) := by
    rw [V_budget, hck, rq_len]
    rfl
  have hA : (!(srch (qry cA q (psi (cz (Hs cA q n)))) (Hs cA q n)).isEmpty) = true ↔
      psi (cz (Hs cA q n)) ∈ Acq cA q := by
    constructor
    · exact srch_sound _ _
    · refine srch_complete _ _ (fun w hw => ?_)
      have h1 := qry_witness cA q _ w hw
      have h2 := Nat.lt_size.1
        (show (qry cA q (psi (cz (Hs cA q n)))).length + 1 < Nat.size n by omega)
      rw [pow_succ] at h2
      rw [Hs_length]
      omega
  have hG : decide ((padOf (cz (Hs cA q n)) (Hs cA q n)).length ≤ (cz (Hs cA q n)).length) =
      true ↔ Gp cA q (cz (Hs cA q n)) := by
    rw [decide_eq_true_eq, padOf, tpw_length _ _ _ (by simp [base]), stg_length cA q n _ g0]
    unfold Gp
    rw [base_length]
    omega
  rw [hD, bne_and_iff, hA, hG]
  exact Iff.rfl

/-- The witness bit of the history of length `n`. -/
theorem Wb_Hs (n : ℕ) : Wb cA q (Hs cA q n) = true ↔
    ((psi (cz (Hs cA q n))).length ≤ n ∧ ((cz (Hs cA q n)).length + 2) ^ stage cA q n ≤ n ∧
      (qry cA q (psi (cz (Hs cA q n)))).length + 2 ≤ Nat.size n ∧
      ¬ (Dd (stage cA q n) (cz (Hs cA q n)) = true ↔ cz (Hs cA q n) ∈ LL cA q)) := by
  have e0 : (psi (cz (Hs cA q n))).length ≤ (Hs cA q n).length ↔
      (psi (cz (Hs cA q n))).length ≤ n := by rw [Hs_length]
  have e1 : (clk (Hs cA q n)).length ≤ (Hs cA q n).length ↔
      ((cz (Hs cA q n)).length + 2) ^ stage cA q n ≤ n := by
    rw [clk_length, Hs_length]
    omega
  have e3 : (qry cA q (psi (cz (Hs cA q n))) ++ [true, true]).length ≤
      (lgU (mulU (Hs cA q n) [true])).length ↔
      (qry cA q (psi (cz (Hs cA q n)))).length + 2 ≤ Nat.size n := by
    rw [lg_length, List.length_append]
    rfl
  unfold Wb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq, decide_eq_true_eq, e0, e1, e3]
  constructor
  · rintro ⟨g0, g1, g3, h⟩
    exact ⟨g0, g1, g3, (body_iff cA q n g0 g1 g3).1 h⟩
  · rintro ⟨g0, g1, g3, h⟩
    exact ⟨g0, g1, g3, (body_iff cA q n g0 g1 g3).2 h⟩

/-- Soundness of the witness bit. -/
theorem sound (n : ℕ) (hw : Wb cA q (Hs cA q n) = true) :
    ∃ z, ¬ (Dd (stage cA q n) z = true ↔ z ∈ LL cA q) :=
  ⟨_, ((Wb_Hs cA q n).1 hw).2.2.2⟩

/-- Liveness of the witness bit. -/
theorem live (i : ℕ) (z : List Bool) (hz : ¬ (Dd i z = true ↔ z ∈ LL cA q)) (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ (stage cA q n = i → Wb cA q (Hs cA q n) = true) := by
  obtain ⟨P2, hP2⟩ : ∃ P2, P2 = 2 ^ ((qry cA q (psi z)).length + 1) := ⟨_, rfl⟩
  obtain ⟨k, hk0⟩ : ∃ k, k = n₀ + (psi z).length + (z.length + 2) ^ i + P2 := ⟨_, rfl⟩
  have hk : k ≤ idx (pairB z (un k)) :=
    le_trans (by rw [pairB_length, un_length]; omega) (length_le_idx _)
  have hcz : cz (Hs cA q (idx (pairB z (un k)))) = z := by
    rw [cz_Hs, cand_idx, unpairB_pairB]
  refine ⟨idx (pairB z (un k)), by omega, fun hi => ?_⟩
  rw [Wb_Hs, hcz, hi]
  refine ⟨by omega, by omega, ?_, hz⟩
  have h1 := Nat.lt_size.2
    (show 2 ^ ((qry cA q (psi z)).length + 1) ≤ idx (pairB z (un k)) by rw [← hP2]; omega)
  omega

end Witness

end PEqualNP.Library.Ladner
