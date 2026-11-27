import PEqualNP.MetaComplexity.Helpers.Columns
import PEqualNP.Defs.MetaComplexityLgpMono

/-!
# Replaying a circuit on every input, as one Boolean

Helper for FIND steps (an existential row whose proof is the found object and an evaluation).
`allInputs n t` runs a Boolean test on all `2 ^ n` inputs; `replayAll n C f` runs the circuit `C` on all `2 ^ n` inputs and compares with `f`; it is a
`Bool`, so a proof that `C` computes `f` is one `decide` on `replayAll n C f = true`, followed by
`replayAll_sound`. The inputs are enumerated by a recursion on the number of bits (depth `n`,
not `2 ^ n`), input `k` being the bits of the number `k`, least significant first.

`fanInTwoB` and `monotone2B` are Boolean forms of `FanInTwo` and `Monotone2`, with soundness.
-/

namespace PEqualNP.Library.Helpers.Replay

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The input on `n` bits read off the number `k`: bit `i` is binary digit `i` of `k`. -/
def bitsIn (n k : ℕ) : Fin n → Bool := fun i => k.testBit i

/-- `allFrom n t m a` checks the test `t` on the inputs `bitsIn n (a + r)` for every `r < 2 ^ m`. -/
def allFrom (n : ℕ) (t : (Fin n → Bool) → Bool) : ℕ → ℕ → Bool
  | 0, a => t (bitsIn n a)
  | m + 1, a => allFrom n t m a && allFrom n t m (a + 2 ^ m)

/-- The test `t` passes on all `2 ^ n` inputs. -/
def allInputs (n : ℕ) (t : (Fin n → Bool) → Bool) : Bool :=
  allFrom n t n 0

theorem allFrom_spec (n : ℕ) (t : (Fin n → Bool) → Bool) :
    ∀ (m a : ℕ), allFrom n t m a = true → ∀ r, r < 2 ^ m → t (bitsIn n (a + r)) = true := by
  intro m
  induction m with
  | zero =>
    intro a h r hr
    have : r = 0 := by simpa using hr
    subst this
    simpa [allFrom] using h
  | succ m ih =>
    intro a h r hr
    simp only [allFrom, Bool.and_eq_true] at h
    by_cases hr' : r < 2 ^ m
    · exact ih a h.1 r hr'
    · have h2 := ih (a + 2 ^ m) h.2 (r - 2 ^ m) (by rw [pow_succ] at hr; omega)
      have : a + 2 ^ m + (r - 2 ^ m) = a + r := by omega
      rwa [this] at h2

theorem bitsIn_tableIndex {n : ℕ} (x : Fin n → Bool) : bitsIn n (tableIndex x) = x := by
  funext i
  exact PEqualNP.MetaComplexity.Helpers.testBit_tableIndex x i

/-- Soundness of the enumeration: a test that passes on all inputs passes on every input. -/
theorem allInputs_sound {n : ℕ} {t : (Fin n → Bool) → Bool} (h : allInputs n t = true) :
    ∀ x : Fin n → Bool, t x = true := by
  intro x
  have := allFrom_spec n t n 0 h (tableIndex x)
    (PEqualNP.MetaComplexity.Helpers.tableIndex_lt x)
  rwa [Nat.zero_add, bitsIn_tableIndex] at this

/-- `C` agrees with `f` on all `2 ^ n` inputs. -/
def replayAll (n : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool) : Bool :=
  allInputs n fun x => C.eval (List.ofFn x) == f x

/-- Soundness: if the replay says `true`, the circuit computes `f` on every input. -/
theorem replayAll_sound {n : ℕ} {C : Circuit} {f : (Fin n → Bool) → Bool}
    (h : replayAll n C f = true) : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  simpa using allInputs_sound h x

/-- Is the operation AND, OR or NOT? -/
def isAONB : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

/-- Is the operation AND or OR? -/
def isAOB : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

/-- `FanInTwo` as a Boolean. -/
def fanInTwoB (C : Circuit) : Bool :=
  C.gates.all fun g => isAONB g.op && decide (g.inputs.length ≤ 2)

/-- `Monotone2` as a Boolean. -/
def monotone2B (C : Circuit) : Bool :=
  C.gates.all fun g => isAOB g.op && decide (g.inputs.length ≤ 2)

theorem fanInTwoB_sound {C : Circuit} (h : fanInTwoB C = true) : FanInTwo C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [isAONB]

theorem monotone2B_sound {C : Circuit} (h : monotone2B C = true) : Monotone2 C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [isAOB]

/-- One-call form for a FIND row on circuit size. -/
theorem hasCircuitSize_of_replay {n s : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (h : (fanInTwoB C && decide (C.size ≤ s) && replayAll n C f) = true) :
    HasCircuitSize n f s := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨C, fanInTwoB_sound h.1.1, h.1.2, replayAll_sound h.2⟩

end PEqualNP.Library.Helpers.Replay
