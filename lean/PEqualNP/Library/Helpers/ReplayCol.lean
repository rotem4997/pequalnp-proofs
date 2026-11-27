import PEqualNP.Library.Helpers.Replay

/-!
# Replaying a circuit on every input at once, by bit columns

The same verdict as `replayAll`, computed the fast way for the kernel: every wire carries one
number whose binary digit `k` is the wire's value on input `k` (the input whose bit `i` is digit
`i` of `k`). An AND gate is one `&&&` of numbers, an OR gate one `|||`, a NOT gate one `^^^`
with the all-ones number; the function `f` is tabulated once, by a recursion of depth `n`.
So the kernel does a few big-number operations per gate, and `2 ^ n` evaluations of `f` only.

`colReplay n C f = true` says: every gate of `C` is AND, OR or NOT (any fan-in), and the output
column equals the table of `f`. `colReplay_sound` turns it into agreement on every input.
-/

namespace PEqualNP.Library.Helpers.ReplayCol

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.Helpers.Replay

/-- `colFrom n t m a`: digit `r` (for `r < 2 ^ m`) is the test `t` on input `a + r`. -/
def colFrom (n : ℕ) (t : (Fin n → Bool) → Bool) : ℕ → ℕ → ℕ
  | 0, a => (t (bitsIn n a)).toNat
  | m + 1, a => 2 ^ (2 ^ m) * colFrom n t m (a + 2 ^ m) + colFrom n t m a

/-- The table of `t`: digit `k` is `t` on input `k`. -/
def table (n : ℕ) (t : (Fin n → Bool) → Bool) : ℕ :=
  colFrom n t n 0

theorem colFrom_lt (n : ℕ) (t : (Fin n → Bool) → Bool) :
    ∀ (m a : ℕ), colFrom n t m a < 2 ^ (2 ^ m) := by
  intro m
  induction m with
  | zero => intro a; cases h : t (bitsIn n a) <;> simp [colFrom, h]
  | succ m ih =>
    intro a
    have h1 := ih (a + 2 ^ m)
    have h2 := ih a
    have hp : 2 ^ (2 ^ (m + 1)) = 2 ^ (2 ^ m) * 2 ^ (2 ^ m) := by
      rw [pow_succ, pow_mul, sq]
    rw [hp, colFrom]
    calc 2 ^ 2 ^ m * colFrom n t m (a + 2 ^ m) + colFrom n t m a
        < 2 ^ 2 ^ m * colFrom n t m (a + 2 ^ m) + 2 ^ 2 ^ m := by omega
      _ = 2 ^ 2 ^ m * (colFrom n t m (a + 2 ^ m) + 1) := by ring
      _ ≤ 2 ^ 2 ^ m * 2 ^ 2 ^ m := Nat.mul_le_mul_left _ h1

theorem testBit_colFrom (n : ℕ) (t : (Fin n → Bool) → Bool) :
    ∀ (m a r : ℕ), r < 2 ^ m → (colFrom n t m a).testBit r = t (bitsIn n (a + r)) := by
  intro m
  induction m with
  | zero =>
    intro a r hr
    have : r = 0 := by simpa using hr
    subst this
    cases h : t (bitsIn n (a + 0)) <;> simp_all [colFrom]
  | succ m ih =>
    intro a r hr
    rw [colFrom, Nat.testBit_two_pow_mul_add _ (colFrom_lt n t m a)]
    split
    · next h => exact ih a r h
    · next h =>
      have hr' : r - 2 ^ m < 2 ^ m := by rw [pow_succ] at hr; omega
      have := ih (a + 2 ^ m) (r - 2 ^ m) hr'
      have e : a + 2 ^ m + (r - 2 ^ m) = a + r := by omega
      rwa [e] at this

theorem testBit_table {n : ℕ} (t : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (table n t).testBit (tableIndex x) = t x := by
  rw [table, testBit_colFrom n t n 0 _ (PEqualNP.MetaComplexity.Helpers.tableIndex_lt x),
    Nat.zero_add, bitsIn_tableIndex]

/-- The all-ones column on `n` inputs. -/
def mask (n : ℕ) : ℕ := 2 ^ (2 ^ n) - 1

theorem testBit_mask {n k : ℕ} (hk : k < 2 ^ n) : (mask n).testBit k = true := by
  simp [mask, Nat.testBit_two_pow_sub_one, hk]

/-- The column of input bit `i` over the inputs below `2 ^ m`, in closed form: digit `r` is bit
`i` of `r`. Each step doubles the range with one multiplication and one addition. -/
def icol (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 ^ (2 ^ m) * (if m = i then mask m else icol i m) + icol i m

theorem mask_lt (m : ℕ) : mask m < 2 ^ (2 ^ m) := by
  unfold mask; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos

theorem icol_lt (i : ℕ) : ∀ m, icol i m < 2 ^ (2 ^ m) := by
  intro m
  induction m with
  | zero => simp [icol]
  | succ m ih =>
    have hp : 2 ^ (2 ^ (m + 1)) = 2 ^ (2 ^ m) * 2 ^ (2 ^ m) := by
      rw [pow_succ, pow_mul, sq]
    have hu : (if m = i then mask m else icol i m) < 2 ^ (2 ^ m) := by
      split
      · exact mask_lt m
      · exact ih
    rw [hp, icol]
    calc 2 ^ 2 ^ m * (if m = i then mask m else icol i m) + icol i m
        < 2 ^ 2 ^ m * (if m = i then mask m else icol i m) + 2 ^ 2 ^ m := by omega
      _ = 2 ^ 2 ^ m * ((if m = i then mask m else icol i m) + 1) := by ring
      _ ≤ 2 ^ 2 ^ m * 2 ^ 2 ^ m := Nat.mul_le_mul_left _ hu

theorem testBit_icol (i : ℕ) : ∀ m r, r < 2 ^ m → (icol i m).testBit r = r.testBit i := by
  intro m
  induction m with
  | zero =>
    intro r hr
    have : r = 0 := by simpa using hr
    subst this; simp [icol]
  | succ m ih =>
    intro r hr
    rw [icol, Nat.testBit_two_pow_mul_add _ (icol_lt i m)]
    split
    · next h => exact ih r h
    · next h =>
      obtain ⟨r', rfl⟩ : ∃ r', r = 2 ^ m + r' := ⟨r - 2 ^ m, by omega⟩
      have hr' : r' < 2 ^ m := by rw [pow_succ] at hr; omega
      rw [Nat.add_sub_cancel_left]
      split
      · next hmi =>
        subst hmi
        rw [testBit_mask hr', Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr']
        rfl
      · next hmi =>
        rw [ih _ hr']
        rcases Nat.lt_or_gt_of_ne hmi with hlt | hgt
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by norm_num) hlt.le)),
            Nat.testBit_lt_two_pow]
          calc 2 ^ m + r' < 2 ^ m + 2 ^ m := by omega
            _ = 2 ^ (m + 1) := by ring
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hlt
        · rw [Nat.testBit_two_pow_add_gt hgt]

/-- The column of input bit `i` on `n` inputs. -/
def inCol (n i : ℕ) : ℕ := icol i n

theorem testBit_inCol {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (inCol n i).testBit (tableIndex x) = x i := by
  rw [inCol, testBit_icol i n _ (PEqualNP.MetaComplexity.Helpers.tableIndex_lt x)]
  exact PEqualNP.MetaComplexity.Helpers.testBit_tableIndex x i

/-- The column of a gate, from the columns of the wires before it (a missing wire is `0`). -/
def gateCol (n : ℕ) (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => cs.getD a 0).foldr (· &&& ·) (mask n)
  | GateOp.or => (g.inputs.map fun a => cs.getD a 0).foldr (· ||| ·) 0
  | GateOp.not => mask n ^^^ (g.inputs.map fun a => cs.getD a 0).headD 0
  | _ => 0

/-- The columns of all wires of `C` on `n` inputs. -/
def wireCols (n : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun cs g => cs ++ [gateCol n g cs])
    (List.ofFn fun i : Fin n => inCol n i)

/-- Every gate is AND, OR or NOT. -/
def aonB (C : Circuit) : Bool :=
  C.gates.all fun g => isAONB g.op

/-- `C` (AND, OR, NOT gates only) computes `f` on all `2 ^ n` inputs, by columns. -/
def colReplay (n : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool) : Bool :=
  aonB C && ((wireCols n C).getD C.output 0 == table n f)

/-- Columns `cs` and wire values `w` agree at digit `k`. -/
def Agree (k : ℕ) (cs : List ℕ) (w : List Bool) : Prop :=
  cs.length = w.length ∧ ∀ j, (cs.getD j 0).testBit k = w.getD j false

theorem agree_snoc {k : ℕ} {cs : List ℕ} {w : List Bool} {c : ℕ} {v : Bool}
    (h : Agree k cs w) (hv : c.testBit k = v) : Agree k (cs ++ [c]) (w ++ [v]) := by
  refine ⟨by simp [h.1], fun j => ?_⟩
  rcases lt_trichotomy j cs.length with hj | hj | hj
  · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (h.1 ▸ hj)]
    exact h.2 j
  · subst hj
    rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ h.1.symm.le]
    simp [h.1, hv]
  · have hl := h.1
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem testBit_foldr_and {k : ℕ} {n : ℕ} (hk : k < 2 ^ n) (l : List ℕ) :
    (l.foldr (· &&& ·) (mask n)).testBit k = (l.map fun c => c.testBit k).all id := by
  induction l with
  | nil => simp [testBit_mask hk]
  | cons c l ih => simp [ih]

theorem testBit_foldr_or {k : ℕ} (l : List ℕ) :
    (l.foldr (· ||| ·) 0).testBit k = (l.map fun c => c.testBit k).any id := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

theorem gateCol_spec {n k : ℕ} (hk : k < 2 ^ n) {cs : List ℕ} {w : List Bool}
    (h : Agree k cs w) (g : Gate) (hg : isAONB g.op = true) :
    (gateCol n g cs).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hmap : ((g.inputs.map fun a => cs.getD a 0).map fun c => c.testBit k)
      = g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]; exact List.map_congr_left (fun a _ => h.2 a)
  cases hop : g.op with
  | and => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_and hk, hmap]
  | or => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_or, hmap]
  | not =>
    simp only [gateCol, hop, GateOp.eval]
    rw [Nat.testBit_xor, testBit_mask hk, ← hmap]
    cases g.inputs <;> simp
  | mod m => rw [hop] at hg; simp [isAONB] at hg
  | maj => rw [hop] at hg; simp [isAONB] at hg

theorem agree_foldl {n k : ℕ} (hk : k < 2 ^ n) :
    ∀ (gs : List Gate) (cs : List ℕ) (w : List Bool), (∀ g ∈ gs, isAONB g.op = true) →
      Agree k cs w →
      Agree k (gs.foldl (fun cs g => cs ++ [gateCol n g cs]) cs)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil => intro cs w _ h; exact h
  | cons g gs ih =>
    intro cs w hg h
    exact ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (agree_snoc h (gateCol_spec hk h g (hg g List.mem_cons_self)))

theorem agree_inputs {n : ℕ} (x : Fin n → Bool) :
    Agree (tableIndex x) (List.ofFn fun i : Fin n => inCol n i) (List.ofFn x) := by
  refine ⟨by simp, fun j => ?_⟩
  by_cases hj : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
    exact testBit_inCol x ⟨j, hj⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

/-- Soundness: if the column replay says `true`, the circuit computes `f` on every input. -/
theorem colReplay_sound {n : ℕ} {C : Circuit} {f : (Fin n → Bool) → Bool}
    (h : colReplay n C f = true) : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  simp only [colReplay, Bool.and_eq_true, beq_iff_eq] at h
  have hg : ∀ g ∈ C.gates, isAONB g.op = true := fun g hg => List.all_eq_true.mp h.1 g hg
  have hA := agree_foldl (PEqualNP.MetaComplexity.Helpers.tableIndex_lt x) C.gates _ _ hg
    (agree_inputs x)
  have := hA.2 C.output
  rw [show C.gates.foldl _ (List.ofFn fun i : Fin n => inCol n i) = wireCols n C
    from rfl, h.2, testBit_table] at this
  exact this.symm

/-- One-call form for a FIND row on circuit size, by columns. -/
theorem hasCircuitSize_of_colReplay {n s : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (h : (fanInTwoB C && decide (C.size ≤ s) && colReplay n C f) = true) :
    HasCircuitSize n f s := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨C, fanInTwoB_sound h.1.1, h.1.2, colReplay_sound h.2⟩

end PEqualNP.Library.Helpers.ReplayCol
