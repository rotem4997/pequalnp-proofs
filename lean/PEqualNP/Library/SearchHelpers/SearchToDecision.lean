import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.SearchHelpers.Encoding

/-!
# Helpers: search reduces to decision for SAT

Helper module (proofs only, no statement may use it).

Given a polynomial-time decider of SAT, a satisfying assignment of a satisfiable formula whose
variables are all below the length `n` of its code is found by fixing the variables `0 .. n - 1`
one at a time (Levin 1973). The loop state is `pairB x (pairB U (pairB B out))`: the input, the
code of the unit clauses chosen so far, the binary digits of the index of the current variable
(least significant first) and the chosen values so far. One round asks the decider whether the
input with the units and the unit clause "the current variable is true" is satisfiable, appends
the unit clause of the answer, increments the index and appends the answer to the output.

The digits of the index are cut at twice the length of the input before use, so the growth of
one round is bounded by a measure the round does not change and the measured iteration theorem
applies on all strings. On the real run the cut removes nothing.
-/

namespace PEqualNP.Library.SearchHelpers.S2D

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.Tab.StepW

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Binary increment -/

/-- Increment of a binary numeral, least significant digit first. -/
def incB : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incB l

theorem bits_succ (n : ℕ) : Nat.bits (n + 1) = incB (Nat.bits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [incB]
      · rw [Nat.bit1_bits, Nat.bit0_bits m (by omega)]
        rfl
    · have e : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
      rw [e, Nat.bit0_bits (m + 1) (by omega), Nat.bit1_bits, ih m (by omega)]
      rfl

theorem incB_length (l : List Bool) : (incB l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [incB]
  | cons b l ih => cases b <;> simp [incB]; omega

/-- The transducer of the increment: the state is the carry. -/
def incD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some false)
  | true, false => (false, some true)
  | false, b => (false, some b)

def incFin : Bool → Option Bool
  | true => some true
  | false => none

theorem incD_false (l : List Bool) : fstRun incD incFin false l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, incD, ih]

theorem incD_true (l : List Bool) : fstRun incD incFin true l = incB l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, incD, incB, ih, incD_false]

theorem cpt_incB : CPTs incB :=
  fst_polyTime _ _ _ incD incFin true (fun s => (incD_true s).symm)

/-! ### Digit pairs -/

/-- The digits of a numeral as digit pairs of the encoding of formulas. -/
def dig (l : List Bool) : List Bool := l.flatMap fun d => [true, d]

theorem dig_length (l : List Bool) : (dig l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [dig] at ih ⊢; omega

theorem dig_run (l : List Bool) :
    fstRun2 (fun (_ : Unit) (b : Bool) => ((), some true, some b)) (fun _ => none) () l =
      dig l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun2, dig] at ih ⊢; exact ih

theorem cpt_dig : CPTs dig :=
  fst2_polyTime _ _ _ (fun (_ : Unit) (b : Bool) => ((), some true, some b)) (fun _ => none) ()
    (fun s => (dig_run s).symm)

/-- The code of a formula with one unit clause, from the polarity and the digit pairs. -/
def unitS (b : Bool) (D : List Bool) : List Bool := true :: b :: (D ++ [false, true, false, false])

theorem unitS_length (b : Bool) (D : List Bool) : (unitS b D).length = D.length + 6 := by
  simp [unitS]

theorem encodeCNF_unit (k : ℕ) (b : Bool) : encodeCNF [[(k, b)]] = unitS b (dig (Nat.bits k)) := by
  simp [encodeCNF, encodeClause, encodeLiteral, unitS, dig]

theorem encodeCNF_app (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF]

/-! ### One round -/

/-- One round of the search, for a flag function `fl` (empty for no, nonempty for yes). -/
def step (fl : List Bool → List Bool) (y : List Bool) : List Bool :=
  pairB (unpairB y).1
    (pairB ((unpairB (unpairB y).2).1 ++
        sel (fl ((unpairB y).1 ++ ((unpairB (unpairB y).2).1 ++
            unitS true (tk ((unpairB y).1 ++ (unpairB y).1)
              (dig (unpairB (unpairB (unpairB y).2).2).1)))))
          (unitS false (tk ((unpairB y).1 ++ (unpairB y).1)
            (dig (unpairB (unpairB (unpairB y).2).2).1)))
          (unitS true (tk ((unpairB y).1 ++ (unpairB y).1)
            (dig (unpairB (unpairB (unpairB y).2).2).1))))
      (pairB (incB (unpairB (unpairB (unpairB y).2).2).1)
        ((unpairB (unpairB (unpairB y).2).2).2 ++
          sel (fl ((unpairB y).1 ++ ((unpairB (unpairB y).2).1 ++
            unitS true (tk ((unpairB y).1 ++ (unpairB y).1)
              (dig (unpairB (unpairB (unpairB y).2).2).1))))) [false] [true])))

theorem step_pairB (fl : List Bool → List Bool) (x U B out : List Bool) :
    step fl (pairB x (pairB U (pairB B out))) =
      pairB x (pairB (U ++ sel (fl (x ++ (U ++ unitS true (tk (x ++ x) (dig B)))))
          (unitS false (tk (x ++ x) (dig B))) (unitS true (tk (x ++ x) (dig B))))
        (pairB (incB B)
          (out ++ sel (fl (x ++ (U ++ unitS true (tk (x ++ x) (dig B))))) [false] [true]))) := by
  simp only [step, unpairB_pairB]

theorem cpt_step {fl : List Bool → List Bool} (hfl : CPTs fl) : CPTs (step fl) := by
  have hx : CPTs (fun y => (unpairB y).1) := cpt_unpairB1
  have h2 : CPTs (fun y => (unpairB y).2) := cpt_unpairB2
  have hU := cpt_unpairB1_1 h2
  have h3 := cpt_unpairB2_1 h2
  have hB := cpt_unpairB1_1 h3
  have hout := cpt_unpairB2_1 h3
  have hD := cpt_tk (cpt_app2 hx hx) (cpt_comp hB cpt_dig)
  have hT := cpt_cons1 true (cpt_cons1 true (cpt_app2 hD (cpt_const [false, true, false, false])))
  have hF := cpt_cons1 true (cpt_cons1 false (cpt_app2 hD (cpt_const [false, true, false, false])))
  have hf := cpt_comp (cpt_app2 hx (cpt_app2 hU hT)) hfl
  exact cptE (cpt_pairB2 hx (cpt_pairB2 (cpt_app2 hU (cpt_sel hf hF hT))
    (cpt_pairB2 (cpt_comp hB cpt_incB)
      (cpt_app2 hout (cpt_sel hf (cpt_const [false]) (cpt_const [true])))))) (fun _ => rfl)

theorem sel_length (f a b : List Bool) : (sel f a b).length ≤ max a.length b.length := by
  unfold sel; split <;> simp

theorem step_measure (fl : List Bool → List Bool) (y : List Bool) :
    4 * (unpairB (step fl y)).1.length + 18 ≤ 4 * (unpairB y).1.length + 18 := by
  simp only [step, unpairB_pairB]
  exact le_rfl

theorem step_length (fl : List Bool → List Bool) (y : List Bool) :
    (step fl y).length ≤ y.length + (4 * (unpairB y).1.length + 18) := by
  have h1 := unpairB_length y
  have h2 := unpairB_length (unpairB y).2
  have h3 := unpairB_length (unpairB (unpairB y).2).2
  have h4 := tk_length ((unpairB y).1 ++ (unpairB y).1)
    (dig (unpairB (unpairB (unpairB y).2).2).1)
  have h5 := incB_length (unpairB (unpairB (unpairB y).2).2).1
  have h6 := sel_length (fl ((unpairB y).1 ++ ((unpairB (unpairB y).2).1 ++
            unitS true (tk ((unpairB y).1 ++ (unpairB y).1)
              (dig (unpairB (unpairB (unpairB y).2).2).1)))))
          (unitS false (tk ((unpairB y).1 ++ (unpairB y).1)
            (dig (unpairB (unpairB (unpairB y).2).2).1)))
          (unitS true (tk ((unpairB y).1 ++ (unpairB y).1)
            (dig (unpairB (unpairB (unpairB y).2).2).1)))
  have h7 := sel_length (fl ((unpairB y).1 ++ ((unpairB (unpairB y).2).1 ++
            unitS true (tk ((unpairB y).1 ++ (unpairB y).1)
              (dig (unpairB (unpairB (unpairB y).2).2).1))))) [false] [true]
  simp only [unitS_length, List.length_append, List.length_cons, List.length_nil,
    max_self] at h4 h6 h7
  simp only [step, pairB_length, List.length_append]
  omega

/-- The search function of a flag function. -/
def searchF (fl : List Bool → List Bool) (x : List Bool) : List Bool :=
  (unpairB (unpairB (unpairB ((step fl)^[x.length]
    (pairB x (pairB [] (pairB [] []))))).2).2).2

theorem cpt_searchF {fl : List Bool → List Bool} (hfl : CPTs fl) : CPTs (searchF fl) := by
  have hit := cpt_iterMeasure (cpt_step hfl) (fun y => 4 * (unpairB y).1.length + 18) 18
    (step_measure fl) (step_length fl)
    (fun y => by have := unpairB_length y; omega) cpt_id
    (cpt_pairB2 cpt_id (cpt_const (pairB [] (pairB [] []))))
  exact cptE (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hit))) (fun _ => rfl)

/-! ### Correctness -/

/-- The unit clauses of a list of chosen values: variable `j` has the value `bs[j]`. -/
def unitsOf (bs : List Bool) : CNF := (List.range bs.length).map fun j => [(j, bs.getD j false)]

theorem unitsOf_snoc (bs : List Bool) (c : Bool) :
    unitsOf (bs ++ [c]) = unitsOf bs ++ [[(bs.length, c)]] := by
  simp only [unitsOf, List.length_append, List.length_cons, List.length_nil, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    simp [List.getElem?_append_left hj, hj]
  · simp

theorem eval_app (σ : Assignment) (a b : CNF) :
    CNF.eval σ (a ++ b) = (CNF.eval σ a && CNF.eval σ b) := by
  simp [CNF.eval]

theorem eval_unit (σ : Assignment) (k : ℕ) (c : Bool) :
    CNF.eval σ [[(k, c)]] = (σ k == c) := by
  simp [CNF.eval, Clause.eval, Literal.eval]

theorem eval_unitsOf (σ : Assignment) (bs : List Bool) (h : CNF.eval σ (unitsOf bs) = true) :
    ∀ j < bs.length, σ j = bs.getD j false := by
  intro j hj
  simp only [CNF.eval, unitsOf, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply] at h
  have := h j hj
  simpa [Clause.eval, Literal.eval] using this

theorem size_bound (k : ℕ) : (dig (Nat.bits k)).length ≤ 2 * k := by
  rw [dig_length, Nat.size_eq_bits_len]
  have : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

/-- The state of the loop after `k` rounds on a satisfiable formula. -/
theorem step_iter (d : List Bool → Bool) (hd : ∀ a, a ∈ SAT ↔ d a = true) (φ : CNF)
    (hsat : Satisfiable φ) (k : ℕ) (hk : k ≤ (encodeCNF φ).length) :
    ∃ bs : List Bool, bs.length = k ∧ Satisfiable (φ ++ unitsOf bs) ∧
      (step (fun a => if d a then [true] else []))^[k]
          (pairB (encodeCNF φ) (pairB [] (pairB [] []))) =
        pairB (encodeCNF φ) (pairB (encodeCNF (unitsOf bs)) (pairB (Nat.bits k) bs)) := by
  induction k with
  | zero => exact ⟨[], rfl, by simpa [unitsOf] using hsat, by simp [unitsOf, encodeCNF]⟩
  | succ k ih =>
    obtain ⟨bs, hlen, ⟨σ, hσ⟩, hst⟩ := ih (by omega)
    have hcut : tk (encodeCNF φ ++ encodeCNF φ) (dig (Nat.bits k)) = dig (Nat.bits k) := by
      rw [tk_eq]
      apply List.take_of_length_le
      have := size_bound k
      rw [List.length_append]
      omega
    have hq : encodeCNF φ ++ (encodeCNF (unitsOf bs) ++ unitS true (dig (Nat.bits k))) =
        encodeCNF (φ ++ unitsOf (bs ++ [true])) := by
      rw [unitsOf_snoc, encodeCNF_app, encodeCNF_app, encodeCNF_unit, hlen]
    rw [Function.iterate_succ_apply', hst, step_pairB, hcut, hq, ← bits_succ]
    rw [eval_app] at hσ
    obtain ⟨hσ1, hσ2⟩ := Bool.and_eq_true_iff.mp hσ
    cases hdq : d (encodeCNF (φ ++ unitsOf (bs ++ [true])))
    · refine ⟨bs ++ [false], by simp [hlen], ⟨σ, ?_⟩, ?_⟩
      · have hk' : σ k = false := by
          by_contra hne
          have hne' : σ k = true := by simpa using hne
          have hmem : encodeCNF (φ ++ unitsOf (bs ++ [true])) ∈ SAT :=
            ⟨_, rfl, σ, by
              rw [unitsOf_snoc, eval_app, eval_app, eval_unit, hσ1, hσ2, hlen, hne']; rfl⟩
          rw [(hd _).mp hmem] at hdq
          exact Bool.noConfusion hdq
        rw [unitsOf_snoc, eval_app, eval_app, eval_unit, hσ1, hσ2, hlen, hk']; rfl
      · simp only [Bool.false_eq_true, ite_false, sel_nil]
        rw [unitsOf_snoc, encodeCNF_app, encodeCNF_unit, hlen]
    · refine ⟨bs ++ [true], by simp [hlen], ?_, ?_⟩
      · obtain ⟨φ', he, hs⟩ := (hd _).mpr hdq
        rw [encodeCNF_injective he] at hs
        exact hs
      · simp only [ite_true, sel_cons]
        rw [unitsOf_snoc, encodeCNF_app, encodeCNF_unit, hlen]

/-- Search reduces to decision: from a polynomial-time decider of SAT, a polynomial-time
function that finds a satisfying assignment of every satisfiable formula whose variables are
below the length of its code. -/
theorem search_of_decider (d : List Bool → Bool) (hd : ∀ a, a ∈ SAT ↔ d a = true)
    (hc : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool d) :
    ∃ f : List Bool → List Bool, CPTs f ∧
      ∀ φ : CNF, (∀ c ∈ φ, ∀ l ∈ c, l.1 < (encodeCNF φ).length) → Satisfiable φ →
        CNF.eval (fun i : ℕ => (f (encodeCNF φ)).getD i false) φ = true := by
  refine ⟨searchF (fun a => if d a then [true] else []), cpt_searchF (cpt_bitFlag hc), ?_⟩
  intro φ hvar hsat
  obtain ⟨bs, hlen, ⟨σ, hσ⟩, hst⟩ := step_iter d hd φ hsat (encodeCNF φ).length le_rfl
  have hf : searchF (fun a => if d a then [true] else []) (encodeCNF φ) = bs := by
    simp only [searchF, hst, unpairB_pairB]
  rw [hf]
  rw [eval_app] at hσ
  obtain ⟨hσ1, hσ2⟩ := Bool.and_eq_true_iff.mp hσ
  have hag := eval_unitsOf σ bs hσ2
  simp only [CNF.eval, List.all_eq_true, Clause.eval, List.any_eq_true, Literal.eval] at hσ1 ⊢
  intro c hc'
  obtain ⟨l, hl, hle⟩ := hσ1 c hc'
  refine ⟨l, hl, ?_⟩
  rw [← hag l.1 (by rw [hlen]; exact hvar c hc' l hl)]
  exact hle

end PEqualNP.Library.SearchHelpers.S2D
