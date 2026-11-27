import PEqualNP.Library.Helpers.ReplayCol
import PEqualNP.Defs.BranchingProgram

/-!
# Replaying a branching program on every input, as one Boolean

Helper for FIND steps on `PEqualNP.BranchingProgram.HasBPSize`: `forwardB` and `readsBelowB`
are Boolean forms of `Program.Forward` and `Program.ReadsBelow`, and `hasBPSize_of_replay`
turns one Boolean (both checks, the size bound, and agreement on all `2 ^ n` inputs by
`allInputs`) into the size statement, so a proof is the program and one `decide +kernel`.
-/

namespace PEqualNP.Library.Helpers.ReplayBP

open PEqualNP.BranchingProgram PEqualNP.Library.Helpers.Replay PEqualNP.Library.Helpers.ReplayCol
open PEqualNP.MetaComplexity (tableIndex)

/-- A successor named by state `i` of a program with `L` states is allowed. -/
def okNext (i L : ℕ) : Next → Bool
  | Next.state q => decide (i < q) && decide (q < L)
  | Next.out _ => true

/-- `Program.Forward` as a Boolean. -/
def forwardB (P : Program) : Bool :=
  (List.range P.length).all fun i =>
    match P[i]? with
    | some s => okNext i P.length s.lo && okNext i P.length s.hi
    | none => true

/-- `Program.ReadsBelow` as a Boolean. -/
def readsBelowB (n : ℕ) (P : Program) : Bool :=
  P.all fun s => decide (s.var < n)

theorem okNext_state {i L q : ℕ} (h : okNext i L (Next.state q) = true) : i < q ∧ q < L := by
  simpa [okNext] using h

theorem forwardB_sound {P : Program} (h : forwardB P = true) : P.Forward := by
  intro i s hs q hq
  have hi : i < P.length := (List.getElem?_eq_some_iff.mp hs).1
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [hs] at this
  simp only [Bool.and_eq_true] at this
  rcases hq with hq | hq
  · rw [hq] at this; exact okNext_state this.1
  · rw [hq] at this; exact okNext_state this.2

theorem readsBelowB_sound {n : ℕ} {P : Program} (h : readsBelowB n P = true) :
    P.ReadsBelow n := by
  intro s hs
  simpa using List.all_eq_true.mp h s hs

/-- One-call form for a FIND row on branching-program size. -/
theorem hasBPSize_of_replay {n s : ℕ} {f : (Fin n → Bool) → Bool} (P : Program)
    (h : (forwardB P && readsBelowB n P && decide (P.size ≤ s) &&
      allInputs n (fun x => P.eval (List.ofFn x) == f x)) = true) :
    HasBPSize n f s := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨P, forwardB_sound h.1.1.1, readsBelowB_sound h.1.1.2, h.1.2, fun x => ?_⟩
  simpa using allInputs_sound h.2 x

/-! ## By columns

The column of a state is the number whose digit `k` is the program's output on input `k` when
started at that state. A forward program is processed from its last state to its first, so
each state's column is two `&&&`, one `|||` and one `^^^` on the columns of later states. -/

/-- The column of a successor, read from the columns `acc` of the states from `base` on. -/
def nextCol (n base : ℕ) (acc : List ℕ) : Next → ℕ
  | Next.out b => if b then mask n else 0
  | Next.state q => acc.getD (q - base) 0

/-- The column of a state at index `base - 1`, given the columns `acc` of the states after it. -/
def stateCol (n base : ℕ) (ins : List ℕ) (acc : List ℕ) (s : State) : ℕ :=
  (ins.getD s.var 0 &&& nextCol n base acc s.hi) |||
    ((mask n ^^^ ins.getD s.var 0) &&& nextCol n base acc s.lo)

/-- The step of the backwards pass over a program of `L` states. -/
def bpStep (n L : ℕ) (ins : List ℕ) (s : State) (acc : List ℕ) : List ℕ :=
  stateCol n (L - acc.length) ins acc s :: acc

/-- The columns of the states of `P` on `n` inputs, in order. -/
def bpCols (n : ℕ) (P : Program) : List ℕ :=
  P.foldr (bpStep n P.length (List.ofFn fun i : Fin n => inCol n i)) []

/-- The output column of `P`: the column of state `0` (`0` for the empty program). -/
def bpOut (n : ℕ) (P : Program) : ℕ :=
  (bpCols n P).getD 0 0

theorem length_foldr_bpStep (n L : ℕ) (ins : List ℕ) (S : Program) :
    (S.foldr (bpStep n L ins) []).length = S.length := by
  induction S with
  | nil => rfl
  | cons s S ih => simp [List.foldr_cons, bpStep, ih]

/-- Where a successor leads, for a run with `f'` steps of fuel left. -/
def nextRun (P : Program) (x : List Bool) (f' : ℕ) : Next → Bool
  | Next.out b => b
  | Next.state q' => P.run x f' q'

theorem testBit_nextCol {n k f' L i : ℕ} (hk : k < 2 ^ n) {P : Program} {x : List Bool}
    {acc : List ℕ} (hacc : acc.length = L - (i + 1))
    (IH : ∀ j, j < acc.length → ∀ fuel, acc.length - j ≤ fuel →
      (acc.getD j 0).testBit k = P.run x fuel (i + 1 + j))
    (nx : Next) (hnx : ∀ q, nx = Next.state q → i < q ∧ q < L) (hf : L - (i + 1) ≤ f') :
    (nextCol n (i + 1) acc nx).testBit k = nextRun P x f' nx := by
  cases nx with
  | out b => cases b <;> simp [nextCol, nextRun, testBit_mask hk]
  | state q =>
    obtain ⟨h1, h2⟩ := hnx q rfl
    simp only [nextCol, nextRun]
    have := IH (q - (i + 1)) (by omega) f' (by omega)
    rwa [show i + 1 + (q - (i + 1)) = q by omega] at this

theorem bpCols_spec {n k : ℕ} (hk : k < 2 ^ n) (P : Program) (hP : P.Forward) (x : List Bool)
    (ins : List ℕ) (hins : ∀ v, (ins.getD v 0).testBit k = x.getD v false) :
    ∀ (S pre : Program), P = pre ++ S →
      ∀ j, j < S.length → ∀ fuel, S.length - j ≤ fuel →
        ((S.foldr (bpStep n P.length ins) []).getD j 0).testBit k =
          P.run x fuel (pre.length + j) := by
  intro S
  induction S with
  | nil => intro pre _ j hj; simp at hj
  | cons s S ih =>
    intro pre hpre j hj fuel hf
    have hL : P.length = pre.length + 1 + S.length := by simp [hpre]; omega
    have ih' := ih (pre ++ [s]) (by simp [hpre])
    rw [List.foldr_cons]
    cases j with
    | zero =>
      obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      have hget : P[pre.length]? = some s := by simp [hpre]
      have hfw := hP pre.length s hget
      simp only [bpStep, List.getD_cons_zero, Nat.add_zero, Program.run, hget,
        length_foldr_bpStep]
      have hbase : P.length - S.length = pre.length + 1 := by omega
      rw [hbase]
      have hacc : (S.foldr (bpStep n P.length ins) []).length = P.length - (pre.length + 1) := by
        rw [length_foldr_bpStep]; omega
      have IH : ∀ j, j < (S.foldr (bpStep n P.length ins) []).length → ∀ fuel,
          (S.foldr (bpStep n P.length ins) []).length - j ≤ fuel →
          ((S.foldr (bpStep n P.length ins) []).getD j 0).testBit k =
            P.run x fuel (pre.length + 1 + j) := by
        intro j hj fuel hf
        rw [length_foldr_bpStep] at hj hf
        have := ih' j hj fuel hf
        simpa using this
      have hfuel : P.length - (pre.length + 1) ≤ f' := by simp at hf; omega
      have hhi := testBit_nextCol hk hacc IH s.hi (fun q hq => hfw q (Or.inr hq)) hfuel
      have hlo := testBit_nextCol hk hacc IH s.lo (fun q hq => hfw q (Or.inl hq)) hfuel
      simp only [stateCol, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_mask hk,
        hins, hhi, hlo]
      cases x.getD s.var false <;> simp <;> rfl
    | succ j =>
      simp only [bpStep, List.getD_cons_succ]
      have := ih' j (by simp at hj; omega) fuel (by simp at hf; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem testBit_bpOut {n : ℕ} {P : Program} (hP : P.Forward) (x : Fin n → Bool) :
    (bpOut n P).testBit (tableIndex x) = P.eval (List.ofFn x) := by
  have hk := PEqualNP.MetaComplexity.Helpers.tableIndex_lt x
  have hins : ∀ v, ((List.ofFn fun i : Fin n => inCol n i).getD v 0).testBit
      (tableIndex x) = (List.ofFn x).getD v false := (agree_inputs x).2
  rcases Nat.eq_zero_or_pos P.length with h0 | hpos
  · have : P = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    simp [bpOut, bpCols, Program.eval, Program.run]
  · have := bpCols_spec hk P hP (List.ofFn x) _ hins P [] (by simp) 0 hpos P.length (by omega)
    simpa [bpOut, bpCols, Program.eval] using this

/-- One-call form for a FIND row on branching-program size, by columns. -/
theorem hasBPSize_of_colReplay {n s : ℕ} {f : (Fin n → Bool) → Bool} (P : Program)
    (h : (forwardB P && readsBelowB n P && decide (P.size ≤ s) &&
      (bpOut n P == table n f)) = true) :
    HasBPSize n f s := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hP := forwardB_sound h.1.1.1
  refine ⟨P, hP, readsBelowB_sound h.1.1.2, h.1.2, fun x => ?_⟩
  rw [← testBit_bpOut hP x, h.2, testBit_table]

end PEqualNP.Library.Helpers.ReplayBP
