import PEqualNP.Library.Universal.Verify
import PEqualNP.Library.Machines.Transducer
import Mathlib.Data.Nat.Size

/-!
# String functions for the lazy diagonal relation

Helper module (proofs only, no statement may use it). It defines a total relation `RD` on pairs
of bit strings as a composition of small named total functions on bit strings, and proves each
of them against its mathematical meaning. The language defined by `RD` with witnesses of
exponential length is shown to lie outside NP in `Lazy.lean`.

An input is read as `z = pairB cs (pairB au mu)`: a code string `cs`, a padding `au`, and a
counter `mu` whose length `m` is the position in a chain. The start of the chain is
`y0Of z = pairB cs (pairB au [])`, and `pairB cs (pairB au (un m)) = y0Of z ++ un m`.

## Primitives and the toolbox item that computes each

* `half`: a finite-state transducer (state: parity; writes `true` on every second symbol, at
  most one output symbol per input symbol). `half u = un (u.length / 2)`.
* `lgStep`: `unpairB`, a constant prefix `[true]` with append, `half`, `pairB`, and one `sel` on
  the second component. One step of counting halvings on the packed state
  `pairB counter rest`; the output is at most one symbol longer than the input.
* `lgU u`: the bounded iteration `lgStep^[u.length]` on `pairB [] u`, then the first `unpairB`
  component. `lgU u = un (Nat.size u.length)`.
* `condC y mu`: length comparison of `y` with `lgU (lgU mu)`.
* `succB`: a finite-state transducer (state: carry; one output symbol per input symbol and at
  most one at the end). The successor in the enumeration of all bit strings, shorter first.
* `bflag`: a decision bit as a flag string (`[true]` or `[]`).
* `srchStep`: `unpairB` three times, `succB`, the interpreter `V` on the pair of two components,
  `bflag`, append, `pairB` twice. One step of the search on the packed state
  `pairB fixed (pairB candidate flag)`; the output is at most two symbols longer than the input.
* `srch F n`: the bounded iteration `srchStep^[n.length]` on `pairB F (pairB [] [])`, then the
  flag component. It is empty exactly when `V` rejects the first `n.length` candidates.
* `y0Of`, `muOf`, `csOf`: components by `unpairB`, `pairB` with a constant.
* `RD`: the components above, append of a constant, append of four copies of the counter,
  `List.tail`, `V`, emptiness of a flag string, and Boolean connectives.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library.Machines

/-! ### Halving and the binary length -/

/-- Transition of the halving transducer: the state is the parity of the symbols read. -/
def halfD (q : Bool) (_ : Bool) : Bool × Option Bool := (!q, if q then some true else none)

/-- Half of the length, in unary. -/
def half (u : List Bool) : List Bool := fstRun halfD (fun _ => none) false u

theorem halfD_run (q : Bool) (u : List Bool) :
    fstRun halfD (fun _ => none) q u = un ((u.length + (if q then 1 else 0)) / 2) := by
  induction u generalizing q with
  | nil => cases q <;> rfl
  | cons b l ih =>
    cases q
    · simp [fstRun, halfD, ih]
    · have e : (l.length + 1 + 1) / 2 = l.length / 2 + 1 := by omega
      simp [fstRun, halfD, ih, e, un_succ]

theorem half_eq (u : List Bool) : half u = un (u.length / 2) := by
  simp [half, halfD_run]

/-- One step of counting halvings on the packed state `pairB counter rest`. -/
def lgStep (s : List Bool) : List Bool :=
  sel (unpairB s).2 s (pairB (true :: (unpairB s).1) (half (unpairB s).2))

/-- The number of binary digits of the length, in unary. -/
def lgU (u : List Bool) : List Bool := (unpairB (lgStep^[u.length] (pairB [] u))).1

theorem size_half {r : ℕ} (hr : r ≠ 0) : Nat.size r = Nat.size (r / 2) + 1 := by
  apply le_antisymm
  · rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self (r / 2)
    omega
  · rw [Nat.succ_le_iff, Nat.lt_size]
    rcases Nat.eq_zero_or_pos (Nat.size (r / 2)) with h | h
    · rw [h]; simp; omega
    · have h1 : Nat.size (r / 2) - 1 < Nat.size (r / 2) := by omega
      rw [Nat.lt_size] at h1
      have h2 : 2 ^ Nat.size (r / 2) = 2 ^ (Nat.size (r / 2) - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      omega

theorem lgStep_zero (c : ℕ) : lgStep (pairB (un c) (un 0)) = pairB (un c) (un 0) := by
  simp [lgStep, unpairB_pairB, sel]

theorem lgStep_pos (c r : ℕ) (hr : r ≠ 0) :
    lgStep (pairB (un c) (un r)) = pairB (un (c + 1)) (un (r / 2)) := by
  have h : un r ≠ [] := by
    intro h
    exact hr (by simpa using congrArg List.length h)
  simp [lgStep, unpairB_pairB, sel, h, half_eq, un_succ]

theorem lgStep_iter (k : ℕ) : ∀ r c : ℕ, r < 2 ^ k →
    lgStep^[k] (pairB (un c) (un r)) = pairB (un (c + Nat.size r)) (un 0) := by
  induction k with
  | zero =>
    intro r c hr
    obtain rfl : r = 0 := by simpa using hr
    simp
  | succ k ih =>
    intro r c hr
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      rw [lgStep_zero]
      exact ih 0 c (Nat.pos_of_ne_zero (by positivity))
    · rw [lgStep_pos c r (by omega), ih (r / 2) (c + 1) (by rw [pow_succ] at hr; omega),
        size_half (by omega : r ≠ 0)]
      congr 2
      omega

theorem lgU_un (n : ℕ) : lgU (un n) = un (Nat.size n) := by
  have h := lgStep_iter n n 0 Nat.lt_two_pow_self
  rw [un_zero] at h
  simp [lgU, h, unpairB_pairB]

theorem un_length_eq (u : List Bool) (h : ∀ b ∈ u, b = true) : u = un u.length :=
  List.eq_replicate_iff.2 ⟨rfl, h⟩

/-- The length of `lgU u` is the binary length of the length of `u`. -/
theorem lgU_length (n : ℕ) : (lgU (un n)).length = Nat.size n := by
  rw [lgU_un, un_length]

/-- The threshold test: the length of `y` is at most the iterated binary length of `mu`. -/
def condC (y mu : List Bool) : Bool := decide (y.length ≤ (lgU (lgU mu)).length)

theorem condC_un (y : List Bool) (m : ℕ) :
    condC y (un m) = decide (y.length ≤ Nat.size (Nat.size m)) := by
  simp [condC, lgU_un]

/-! ### The enumeration of all bit strings -/

/-- Transition of the successor transducer: the state is the carry. -/
def succD (carry : Bool) (b : Bool) : Bool × Option Bool :=
  if carry then (b, some (!b)) else (false, some b)

/-- Final output of the successor transducer. -/
def succFin (carry : Bool) : Option Bool := if carry then some false else none

/-- The successor of a bit string in the enumeration of all bit strings, shorter ones first:
leading `true`s become `false`, the first `false` becomes `true`, and a `false` is appended when
there was no `false`. -/
def succB (s : List Bool) : List Bool := fstRun succD succFin true s

/-- The enumeration of all bit strings. -/
def cand (j : ℕ) : List Bool := succB^[j] []

theorem succD_run_false (s : List Bool) : fstRun succD succFin false s = s := by
  induction s with
  | nil => rfl
  | cons b l ih => simp [fstRun, succD, ih]

theorem succB_nil : succB [] = [false] := rfl

theorem succB_false (r : List Bool) : succB (false :: r) = true :: r := by
  simp [succB, fstRun, succD, succD_run_false]

theorem succB_true (r : List Bool) : succB (true :: r) = false :: succB r := by
  simp [succB, fstRun, succD]

/-- The position of a bit string in the enumeration. -/
def idx : List Bool → ℕ
  | [] => 0
  | false :: r => 1 + 2 * idx r
  | true :: r => 2 + 2 * idx r

theorem idx_succB (s : List Bool) : idx (succB s) = idx s + 1 := by
  induction s with
  | nil => rfl
  | cons b r ih =>
    cases b
    · rw [succB_false]; simp [idx]; omega
    · rw [succB_true]; simp [idx, ih]; omega

theorem idx_cand (j : ℕ) : idx (cand j) = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cand, Function.iterate_succ_apply', ← cand, idx_succB, ih]

theorem idx_inj : ∀ s t : List Bool, idx s = idx t → s = t
  | [], [], _ => rfl
  | [], false :: _, h => by simp [idx] at h; omega
  | [], true :: _, h => by simp [idx] at h; omega
  | false :: _, [], h => by simp [idx] at h
  | true :: _, [], h => by simp [idx] at h
  | false :: r, false :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | true :: r, true :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | false :: _, true :: _, h => by simp [idx] at h; omega
  | true :: _, false :: _, h => by simp [idx] at h; omega

/-- Every bit string occurs in the enumeration, at its position. -/
theorem cand_idx (s : List Bool) : cand (idx s) = s := idx_inj _ _ (idx_cand _)

/-- Shorter strings come first: a string of length `n` has position below `2 ^ (n + 1) - 1`. -/
theorem idx_bound (s : List Bool) : idx s + 2 ≤ 2 ^ (s.length + 1) := by
  induction s with
  | nil => simp [idx]
  | cons b r ih =>
    have e : 2 ^ ((b :: r).length + 1) = 2 * 2 ^ (r.length + 1) := by
      rw [List.length_cons, pow_succ, Nat.mul_comm]
    cases b <;> simp only [idx] <;> omega

theorem idx_lt_of_length_le {s : List Bool} {b : ℕ} (h : s.length ≤ b) :
    idx s + 2 ≤ 2 ^ (b + 1) :=
  (idx_bound s).trans (Nat.pow_le_pow_right (by omega) (by omega))

/-! ### The bounded search -/

/-- A decision bit as a flag string. -/
def bflag (b : Bool) : List Bool := if b then [true] else []

theorem bflag_eq_nil (b : Bool) : bflag b = [] ↔ b = false := by
  cases b <;> simp [bflag]

/-- One step of the search on the packed state `pairB fixed (pairB candidate flag)`: test the
candidate with `V`, record an acceptance in the flag, and move to the next candidate. -/
def srchStep (s : List Bool) : List Bool :=
  pairB (unpairB s).1 (pairB (succB (unpairB (unpairB s).2).1)
    ((unpairB (unpairB s).2).2 ++ bflag (V ((unpairB s).1, (unpairB (unpairB s).2).1))))

/-- The flag after testing the first `n.length` candidates against the fixed first argument
`F`. -/
def srch (F n : List Bool) : List Bool :=
  (unpairB (unpairB (srchStep^[n.length] (pairB F (pairB [] [])))).2).2

theorem srchStep_pair (F c fl : List Bool) :
    srchStep (pairB F (pairB c fl)) = pairB F (pairB (succB c) (fl ++ bflag (V (F, c)))) := by
  simp [srchStep, unpairB_pairB]

theorem srchStep_iter (F : List Bool) (k : ℕ) : ∀ c fl : List Bool, ∃ fl' : List Bool,
    srchStep^[k] (pairB F (pairB c fl)) = pairB F (pairB (succB^[k] c) fl') ∧
      (fl' = [] ↔ fl = [] ∧ ∀ j < k, V (F, succB^[j] c) = false) := by
  induction k with
  | zero => intro c fl; exact ⟨fl, rfl, by simp⟩
  | succ k ih =>
    intro c fl
    obtain ⟨fl', h1, h2⟩ := ih (succB c) (fl ++ bflag (V (F, c)))
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, srchStep_pair, h1, Function.iterate_succ_apply]
    · rw [h2, List.append_eq_nil_iff, bflag_eq_nil, Nat.forall_lt_succ_left, and_assoc]
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

/-- The search flag is empty exactly when `V` rejects the first `n.length` candidates. -/
theorem srch_eq_nil (F n : List Bool) :
    srch F n = [] ↔ ∀ j < n.length, V (F, cand j) = false := by
  obtain ⟨fl', h1, h2⟩ := srchStep_iter F n.length [] []
  rw [srch, h1]
  simpa [unpairB_pairB, cand] using h2

/-! ### The relation -/

/-- The code string of an input. -/
def csOf (z : List Bool) : List Bool := (unpairB z).1

/-- The counter of an input. -/
def muOf (z : List Bool) : List Bool := (unpairB (unpairB z).2).2

/-- The start of the chain of an input: the input with an empty counter. -/
def y0Of (z : List Bool) : List Bool := pairB (unpairB z).1 (pairB (unpairB (unpairB z).2).1 [])

/-- The lazy diagonal relation on (input, witness). Below the threshold the witness is a pair of
a witness and a budget for the code on the next input of the chain; at the first position past
the threshold the relation holds when the code has no accepted witness on the start of the chain
within the budget `lgU` of the counter; otherwise it fails. -/
def RD (p : List Bool × List Bool) : Bool :=
  (!condC (y0Of p.1) (muOf p.1) &&
      V (pairB (csOf p.1) (pairB (p.1 ++ [true]) (unpairB p.2).2), (unpairB p.2).1)) ||
    (condC (y0Of p.1) (muOf p.1) && (!condC (y0Of p.1) (muOf p.1).tail &&
      (srch (pairB (csOf p.1) (pairB (y0Of p.1) (lgU (muOf p.1))))
        (muOf p.1 ++ (muOf p.1 ++ (muOf p.1 ++ muOf p.1)))).isEmpty))

/-- The lazy diagonal language. -/
def DLang : Language Bool :=
  {z | ∃ w : List Bool, w.length ≤ 2 ^ (z.length ^ 2) + 2 ∧ RD (z, w) = true}

end PEqualNP.Library.Universal
