import PEqualNP.Library.Universal.Lazy
import PEqualNP.Library.Universal.LazyCPT
import PEqualNP.Library.Universal.ExpHierarchy
import PEqualNP.Library.Machines.ReduceNP
import PEqualNP.Library.L055

/-!
# NP is contained in exponential time, by brute-force search

Helper module (proofs only, no statement may use it). For a language in NP, recognized by a code
under the interpreter `V` with a polynomial budget, the decider pads the query exponentially and
then searches all candidate witnesses with the polynomial-time search `srch` of `LazyDefs.lean`.
The running time is at most `2 ^ (n ^ k) + k` for some `k`.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Machines.ExpPad

local notation "CPTb" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

theorem bf_cptl {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### The bounded search is polynomial time -/

theorem bf_cpt_succB : CPTb succB :=
  fst_polyTime _ _ _ succD succFin true (fun _ => rfl)

theorem bf_succD_length (q : Bool) (s : List Bool) :
    (fstRun succD succFin q s).length ≤ s.length + 1 := by
  induction s generalizing q with
  | nil => cases q <;> simp [fstRun, succFin]
  | cons b l ih =>
    have h1 := ih b
    have h2 := ih false
    cases q <;> simp [fstRun, succD] <;> omega

theorem bf_succB_length (s : List Bool) : (succB s).length ≤ s.length + 1 :=
  bf_succD_length true s

theorem bf_bflag_length (b : Bool) : (bflag b).length ≤ 1 := by
  cases b <;> simp [bflag]

theorem bf_srchStep_length (s : List Bool) : (srchStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := bf_succB_length (unpairB (unpairB s).2).1
  have h4 := bf_bflag_length (V ((unpairB s).1, (unpairB (unpairB s).2).1))
  unfold srchStep
  rw [pairB_length, pairB_length, List.length_append]
  omega

theorem bf_cpt_srchStep : CPTb srchStep := by
  have hF : CPTb (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : CPTb (fun s => (unpairB s).2) := cpt_unpairB2
  have hc : CPTb (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hfl : CPTb (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V ((unpairB s).1, (unpairB (unpairB s).2).1)) :=
    cpt_comp (cpt_pair hF hc) (cpt_V cpt_sstep)
  have hb : CPTb (fun s => bflag (V ((unpairB s).1, (unpairB (unpairB s).2).1))) :=
    bf_cptl (cpt_bitFlag hV) (fun _ => rfl)
  have hs : CPTb (fun s => succB (unpairB (unpairB s).2).1) := cpt_comp hc bf_cpt_succB
  exact bf_cptl (cpt_pairB2 hF (cpt_pairB2 hs (cpt_app2 hfl hb))) (fun _ => rfl)

theorem bf_cpt_srch {F n : List Bool → List Bool} (hF : CPTb F) (hn : CPTb n) :
    CPTb (fun s => srch (F s) (n s)) :=
  bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_iterGrow bf_cpt_srchStep 5 bf_srchStep_length hn
    (cpt_pairB2 hF (cpt_pairB2 (cpt_const []) (cpt_const [])))))) (fun _ => rfl)

theorem bf_neL_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

theorem bf_cpt_neL :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, bf_neL_true, Computability.encodeBool])

/-- The brute-force test on a padded string: search the candidates counted by the padding. -/
def bfG (s : List Bool) : Bool := !(srch (dropN s) (hd s)).isEmpty

theorem cpt_bfG :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool bfG :=
  bf_cptl (cpt_comp (bf_cpt_srch cpt_dropN cpt_hd) bf_cpt_neL) (fun _ => rfl)

/-- The test on a padded query accepts exactly when some witness is accepted, provided every
accepted witness is shorter than the query. -/
theorem bfG_expPad (F : List Bool) (hlen : ∀ w, V (F, w) = true → w.length + 1 ≤ F.length) :
    bfG (expPad F) = true ↔ ∃ w, V (F, w) = true := by
  have e : bfG (expPad F) = true ↔ ¬ srch F (un (2 ^ F.length)) = [] := by
    simp [bfG, hd_expPad, dropN_expPad]
  rw [e, srch_eq_nil, un_length]
  constructor
  · intro h
    by_contra hc
    exact h (fun j _ => by
      cases hv : V (F, cand j) with
      | false => rfl
      | true => exact absurd ⟨cand j, hv⟩ hc)
  · rintro ⟨w, hw⟩ h
    have h1 := idx_bound w
    have h2 : (2 : ℕ) ^ (w.length + 1) ≤ 2 ^ F.length :=
      Nat.pow_le_pow_right (by norm_num) (hlen w hw)
    have h3 := h (idx w) (by omega)
    rw [cand_idx, hw] at h3
    exact Bool.noConfusion h3

/-! ### The query map -/

/-- The query map is polynomial-time computable. -/
theorem bf_cpt_query (a : List Bool) (q : Polynomial ℕ) :
    CPTb (fun x : List Bool => pairB a (pairB x (un (q.eval x.length)))) :=
  cpt_pairB2 (cpt_const a) (cpt_pairB2 cpt_id (L055 q))

/-! ### Arithmetic -/

/-- A function bounded by `2 ^ (n ^ M)` from `2` on is bounded by `2 ^ (n ^ k) + k` for some
`k`. -/
theorem exp_pow_le (b : ℕ → ℕ) (M : ℕ) (hb : ∀ n, 2 ≤ n → b n ≤ 2 ^ (n ^ M)) :
    ∃ k, ∀ n, b n ≤ 2 ^ (n ^ k) + k := by
  refine ⟨M + b 0 + b 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact le_trans (by omega : b 0 ≤ M + b 0 + b 1) (Nat.le_add_left _ _)
    · exact le_trans (by omega : b 1 ≤ M + b 0 + b 1) (Nat.le_add_left _ _)
  · have h6 : n ^ M ≤ n ^ (M + b 0 + b 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h7 : (2 : ℕ) ^ (n ^ M) ≤ 2 ^ (n ^ (M + b 0 + b 1)) :=
      Nat.pow_le_pow_right (by norm_num) h6
    have := hb n h
    omega

/-- The arithmetic bound for the brute-force decider. -/
theorem bf_time_bound (p₁ r p₂ : Polynomial ℕ) :
    ∃ k, ∀ n : ℕ, p₁.eval n + (2 * r.eval n + 2) +
        (8 * 2 ^ r.eval n + 8 * r.eval n + 8) +
        (2 * (2 ^ r.eval n + r.eval n + 1) + 2) + p₂.eval (2 ^ r.eval n + r.eval n + 1) ≤
      2 ^ (n ^ k) + k := by
  obtain ⟨k, hk⟩ := expTime_bound p₂
  obtain ⟨j, hj⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add r
  obtain ⟨i, hi⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add
    (p₁ + Polynomial.C 2 * r + Polynomial.C (2 + k))
  refine exp_pow_le _ (i + 1 + (j + 1) * k + 1) (fun n hn => ?_)
  have hk' := hk (r.eval n)
  have hi' := hi n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hi'
  have hpos : ∀ e : ℕ, e < n ^ e := fun e =>
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hn e)
  -- the polynomial part
  have a1 : n ^ i + i ≤ n ^ (i + 1) := by
    have := hpos i
    rw [pow_succ]
    nlinarith
  have a2 : n ^ (i + 1) ≤ 2 ^ (n ^ (i + 1)) := Nat.lt_two_pow_self.le
  -- the exponential part
  have b1 : r.eval n ≤ n ^ (j + 1) := by
    have := hpos j
    have := hj n
    rw [pow_succ]
    nlinarith
  have b2 : r.eval n ^ k ≤ n ^ ((j + 1) * k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left b1 k
  have hM1 : n ^ (i + 1) ≤ n ^ (i + 1 + (j + 1) * k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hM2 : n ^ ((j + 1) * k) ≤ n ^ (i + 1 + (j + 1) * k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have c1 : (2 : ℕ) ^ (n ^ (i + 1)) ≤ 2 ^ (n ^ (i + 1 + (j + 1) * k)) :=
    Nat.pow_le_pow_right (by norm_num) hM1
  have c2 : (2 : ℕ) ^ (r.eval n ^ k) ≤ 2 ^ (n ^ (i + 1 + (j + 1) * k)) :=
    Nat.pow_le_pow_right (by norm_num) (b2.trans hM2)
  have c3 : (2 : ℕ) ^ (n ^ (i + 1 + (j + 1) * k)) * 2 ≤
      2 ^ (n ^ (i + 1 + (j + 1) * k + 1)) := by
    rw [← pow_succ]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 1 ≤ n ^ (i + 1 + (j + 1) * k) := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    nlinarith
  omega

/-! ### The decider -/

/-- Every language in NP is decidable within `2 ^ (n ^ k) + k` steps for some `k`. -/
theorem np_subset_exp (L : Language Bool) (hL : L ∈ NP) :
    ∃ k : ℕ, L ∈ DTIME (fun n : ℕ => 2 ^ (n ^ k) + k) := by
  obtain ⟨c, q, hcomp, hsound⟩ := np_code L hL
  let F : List Bool → List Bool :=
    fun x => pairB (encCode c) (pairB x (un (q.eval x.length)))
  have hF : CPTb F := bf_cpt_query (encCode c) q
  have hFlen : ∀ x w, V (F x, w) = true → w.length + 1 ≤ (F x).length := by
    intro x w hw
    have h1 := V_length _ _ _ _ hw
    simp only [F, pairB_length]
    omega
  have hcorr : ∀ x, x ∈ L ↔ bfG (expPad (F x)) = true := by
    intro x
    refine Iff.trans ?_ (bfG_expPad (F x) (hFlen x)).symm
    exact ⟨fun hx => hcomp x _ le_rfl hx, fun ⟨w, hw⟩ => hsound x _ w hw⟩
  obtain ⟨p₁, hp₁⟩ := time_of_polyTime hF
  obtain ⟨r, hr⟩ := output_length_poly F hF
  obtain ⟨p₂, hp₂⟩ := time_of_polyTime cpt_bfG
  have hmono : Monotone (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) := by
    intro a b hab
    have : (2 : ℕ) ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
    show 8 * 2 ^ a + 8 * a + 8 ≤ 8 * 2 ^ b + 8 * b + 8
    omega
  have h1 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => x) F expPad (fun n => p₁.eval n)
    (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) (fun n => r.eval n) hp₁ expPad_time hmono hr
  have h2 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    Computability.encodeBool (fun x => expPad (F x)) bfG _ (fun n => p₂.eval n)
    (fun n => 2 ^ r.eval n + r.eval n + 1) h1 hp₂ (fun _ _ hxy => eval_mono p₂ hxy)
    (fun x => by
      have e := expPad_length (F x)
      have h3 := hr x
      have : (2 : ℕ) ^ (F x).length ≤ 2 ^ r.eval x.length :=
        Nat.pow_le_pow_right (by norm_num) h3
      show (expPad (F x)).length ≤ 2 ^ r.eval x.length + r.eval x.length + 1
      omega)
  obtain ⟨k, hk⟩ := bf_time_bound p₁ r p₂
  exact ⟨k, fun x => bfG (expPad (F x)), hcorr, time_mono h2 hk⟩

end PEqualNP.Library.Universal
