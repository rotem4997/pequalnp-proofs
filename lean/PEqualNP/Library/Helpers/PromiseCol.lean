import PEqualNP.Library.Helpers.ReplayCol
import PEqualNP.Defs.Represents

/-!
# Column replay on the one-left-one-right promise (seat-gct-2)

`Represents A C` asks the circuit only at the `n * m` inputs `oneEach u v`. This helper replays a circuit on exactly those
rows, one bit per row: row `u * m + v` is the input with left vertex `u` and right vertex `v` on. Every wire becomes one
number of `n * m` bits, and a gate is one big-number operation (the gate fold `ReplayCol.gateCol` with the mask of
`2 ^ N` rows, `n * m ≤ 2 ^ N`). The input columns and the target column have closed forms, built Horner style, so no
column is built by evaluating a function row by row:

* `lcol m j`: left vertex `j`, bits `j * m .. j * m + m - 1`.
* `rcol m v n`: right vertex `v`, bits `u * m + v` for `u < n`.
* `tcol m rows`: the graph given by rows of `m` bits, row `u` the number whose bit `v` says whether `u` and `v` are joined.

`represents_of_pcols` is the soundness: if the output column equals `tcol m rows`, the circuit represents the graph
`fun u v => (rows.getD u 0).testBit v`.
-/

namespace PEqualNP.Library.Helpers.PromiseCol

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.Helpers.Replay
  PEqualNP.Library.Helpers.ReplayCol PEqualNP.Represents

/-- The column of left vertex `j`. -/
def lcol (m : ℕ) : ℕ → ℕ
  | 0 => 2 ^ m - 1
  | j + 1 => 2 ^ m * lcol m j

/-- The column of right vertex `v`, over `n` left vertices. -/
def rcol (m v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ v + 2 ^ m * rcol m v k

/-- The target column of the graph whose rows are `rows` (row `u`, bit `v`). -/
def tcol (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r + 2 ^ m * tcol m rs

/-- The input columns on the promise rows: the `n` left vertices, then the `m` right vertices. -/
def inCols (n m : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => lcol m i) ++ List.ofFn (fun j : Fin m => rcol m j n)

/-- The columns of all wires of `C` on the promise rows, with the mask of `2 ^ N` rows. -/
def pcols (N : ℕ) (C : Circuit) (n m : ℕ) : List ℕ :=
  C.gates.foldl (fun cs g => cs ++ [gateCol N g cs]) (inCols n m)

theorem lt_two_pow_of_lt {a b c : ℕ} (h : a < 2 ^ b) (hbc : b ≤ c) : a < 2 ^ c :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hbc)

theorem bit_lcol {m v : ℕ} (hv : v < m) : ∀ (j u : ℕ), (lcol m j).testBit (u * m + v) = decide (u = j) := by
  intro j
  induction j with
  | zero =>
    intro u
    cases u with
    | zero => simp [lcol, hv]
    | succ u =>
      simp only [lcol, Nat.testBit_two_pow_sub_one]
      have : m ≤ (u + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos u)
      simp; omega
  | succ j ih =>
    intro u
    rw [lcol, Nat.testBit_two_pow_mul]
    cases u with
    | zero => simp; omega
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      simp only [ge_iff_le, g, decide_true, Bool.true_and, e, ih u]
      simp

theorem bit_rcol {m v v' : ℕ} (hv : v < m) (hv' : v' < m) :
    ∀ (n u : ℕ), (rcol m v n).testBit (u * m + v') = decide (u < n ∧ v' = v) := by
  intro n
  induction n with
  | zero => intro u; simp [rcol]
  | succ n ih =>
    intro u
    have hlt : 2 ^ v < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hv
    rw [rcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or, Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v' ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      by_cases h : v' = v
      · subst h; simp
      · simp only [Nat.succ_pos, true_and, h, decide_false]
        exact decide_eq_false (fun e => h e.symm)
    | succ u =>
      have e : (u + 1) * m + v' - m = u * m + v' := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v' ≥ m := by rw [Nat.succ_mul]; omega
      have ne : v ≠ (u + 1) * m + v' := by rw [Nat.succ_mul]; omega
      simp only [g, decide_true, Bool.true_and, e, ih u, ne, decide_false, Bool.or_false]
      simp

theorem bit_tcol {m v : ℕ} (hv : v < m) :
    ∀ (rows : List ℕ), (∀ r ∈ rows, r < 2 ^ m) → ∀ u : ℕ,
      (tcol m rows).testBit (u * m + v) = (rows.getD u 0).testBit v := by
  intro rows
  induction rows with
  | nil => intro _ u; simp [tcol]
  | cons r rs ih =>
    intro hr u
    have hr0 : r < 2 ^ m := hr r List.mem_cons_self
    rw [tcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hr0, Nat.testBit_or, Nat.testBit_two_pow_mul]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      simp
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      have hz : r.testBit ((u + 1) * m + v) = false :=
        Nat.testBit_lt_two_pow (lt_two_pow_of_lt hr0 (by rw [Nat.succ_mul]; omega))
      simp only [g, decide_true, Bool.true_and, e, ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) u, hz,
        Bool.or_false, List.getD_cons_succ]

theorem agree_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) :
    Agree (u.val * m + v.val) (inCols n m) (oneEach u v) := by
  refine ⟨by simp [inCols, oneEach], fun j => ?_⟩
  by_cases hj : j < n
  · rw [inCols, oneEach, List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
    rw [bit_lcol v.isLt j u.val]
    simp [Fin.ext_iff, eq_comm]
  · by_cases hj2 : j < n + m
    · have h1 : (List.ofFn (fun i : Fin n => lcol m i)).length ≤ j := by simp; omega
      have h2 : (List.ofFn (fun i : Fin n => decide (i = u))).length ≤ j := by simp; omega
      rw [inCols, oneEach, List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      rw [bit_rcol (by omega) v.isLt n u.val]
      simp only [u.isLt, true_and]
      simp [Fin.ext_iff]; omega
    · rw [List.getD_eq_default _ _ (by simp [inCols]; omega), List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      simp

/-- Soundness: if the output column on the promise rows equals the target column, `C` represents the graph. -/
theorem represents_of_pcols {n m N : ℕ} (hN : n * m ≤ 2 ^ N) (C : Circuit) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ m) (hg : aonB C = true)
    (h : ((pcols N C n m).getD C.output 0 == tcol m rows) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (rows.getD u.val 0).testBit v.val) C := by
  intro u v
  have hk : u.val * m + v.val < 2 ^ N := by
    have : u.val * m + v.val < (u.val + 1) * m := by rw [Nat.succ_mul]; omega
    have : (u.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m u.isLt
    omega
  have hg' : ∀ g ∈ C.gates, isAONB g.op = true := fun g hg2 => List.all_eq_true.mp hg g hg2
  have hA := agree_foldl hk C.gates _ _ hg' (agree_oneEach u v)
  have := hA.2 C.output
  rw [show C.gates.foldl _ (inCols n m) = pcols N C n m from rfl, beq_iff_eq.mp h,
    bit_tcol v.isLt rows hrows u.val] at this
  exact this.symm

end PEqualNP.Library.Helpers.PromiseCol
