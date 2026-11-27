import PEqualNP.Library.Universal.Strings

/-!
# The string-level step of the micro-instruction machine

Helper module (proofs only, no statement may use it). `sstep` maps the encoding of a
configuration to the encoding of the next configuration, the program part being carried along
unchanged, and it is total on all bit strings.

## Primitives and the toolbox item that computes each

From `Pair.lean`:
* `pairB a b`: pairing (a transducer `true ↦ true` on a copy of `a` gives `un a.length`, then
  append of the constant `[false]`, `a` and `b`).
* `unpairB`: the two components of a pair.

From `Strings.lean`:
* `hd` (leading run of `true`): transducer, two states (copying, done).
* `dropN` (drop through the first `false`): transducer, two states (dropping, copying).
* `List.tail` (drop the first symbol): transducer, two states.
* `takeL`, `dropL`, `headL` (first inner list without terminator, the rest after it, first inner
  list with terminator): transducers, three states (at the start of a number, inside a number,
  finished).
* `popT` (drop the first number when the string starts with `true`): transducer, three states.
* `sel f a b` (`a` when the flag `f` is empty, else `b`): selection on emptiness of a string;
  for instance bounded iteration of the constant function `fun _ => b` on `(a, hd-like flag)`,
  or length comparison of `f` with the empty constant.
* `mulU u v`: unary multiplication.
* `move`: on a pair `(r, d)`, pairing of `dropL` applied to `r` and of the append of `d` and
  `headL r`. Lengthens by at most one symbol, see `move_length`.
* `spread`, `bump`, `blank`: transducers with one state, writing at most two symbols per symbol.
* `g^[u.length] y` for `g` among `dropL`, `dropN`, `move`: bounded iteration; `dropL` and
  `dropN` do not lengthen (`dropL_length`, `dropN_length`), and `move` lengthens by at most
  one symbol (`move_length`), so the constant measure `1` works.

In this file:
* `fetch ps pc`: `takeL` after the iteration `dropL^[pc.tail.length] ps`.
* `fOp`, `fK`, `fW`, `fN1`, `fN2`, `fTb`: compositions of `hd`, `dropN` and `List.tail`
  (a constant number of them).
* `lookup tb idx`: `List.tail` of `hd` of the iteration `dropN^[idx.length] tb`.
* `splitK kf sk`: the iteration `move^[kf.length]` on the pair `pairB sk []`.
* `pcSel`, `stSel`, `skSel`: nested `sel` on the tails of the opcode string (a constant number),
  with append of constant strings.
* `pcOut`, `stOut`, `skOut`: compositions of the above; the index of `stOut` is the append of
  `mulU st (fW I)` and `hd` of the remaining part of `splitK`.
* `sstep`: three `unpairB`, the three outputs, three `pairB`.
* Measure for the iteration of `sstep`: `smeasure`, with `smeasure_sstep`, `sstep_length`,
  `smeasure_le`.
-/

namespace PEqualNP.Library.Universal

/-! ## Reading an instruction -/

/-- The instruction at the program counter: empty outside the program. -/
def fetch (ps pc : List Bool) : List Bool := takeL (dropL^[pc.tail.length] ps)

/-- The opcode, as `un (opcode + 1)`. -/
def fOp (I : List Bool) : List Bool := hd I

/-- The stack index, in unary. -/
def fK (I : List Bool) : List Bool := (hd (dropN I)).tail

/-- The row width, in unary. -/
def fW (I : List Bool) : List Bool := (hd (dropN (dropN I))).tail

/-- The first target, as a program counter string. -/
def fN1 (I : List Bool) : List Bool := hd (dropN (dropN (dropN I)))

/-- The second target, as a program counter string. -/
def fN2 (I : List Bool) : List Bool := hd (dropN (dropN (dropN (dropN I))))

/-- The table. -/
def fTb (I : List Bool) : List Bool := dropN (dropN (dropN (dropN (dropN I))))

/-- Table lookup at the index `idx.length`, in unary, with default `0`. -/
def lookup (tb idx : List Bool) : List Bool := (hd (dropN^[idx.length] tb)).tail

/-- The pair (stack `kf.length` and the following ones, the stacks before it). -/
def splitK (kf sk : List Bool) : List Bool := move^[kf.length] (pairB sk [])

/-! ## The three outputs -/

/-- The new program counter string, by cases on the opcode string `o`. -/
def pcSel (pc o n1 n2 valS : List Bool) : List Bool :=
  sel pc pc (sel o [] (sel o.tail n1 (sel o.tail.tail n1 (sel o.tail.tail.tail n1
    (sel o.tail.tail.tail.tail n1 (sel o.tail.tail.tail.tail.tail (sel valS n2 n1)
      (sel o.tail.tail.tail.tail.tail.tail (true :: valS) [])))))))

/-- The new state string, by cases on the opcode string `o`. -/
def stSel (pc o st valS valT : List Bool) : List Bool :=
  sel pc st (sel o st (sel o.tail st (sel o.tail.tail valT (sel o.tail.tail.tail valT
    (sel o.tail.tail.tail.tail valS st)))))

/-- The new stacks string, by cases on the opcode string `o`. -/
def skSel (pc o sk r d pushed : List Bool) : List Bool :=
  sel pc sk (sel o sk (sel o.tail (sel r d (d ++ (pushed ++ r)))
    (sel o.tail.tail (d ++ popT r) sk)))

/-- The new program counter string. -/
def pcOut (ps pc st : List Bool) : List Bool :=
  pcSel pc (fOp (fetch ps pc)) (fN1 (fetch ps pc)) (fN2 (fetch ps pc))
    (lookup (fTb (fetch ps pc)) st)

/-- The new state string. -/
def stOut (ps pc st sk : List Bool) : List Bool :=
  stSel pc (fOp (fetch ps pc)) st (lookup (fTb (fetch ps pc)) st)
    (lookup (fTb (fetch ps pc))
      (mulU st (fW (fetch ps pc)) ++ hd (unpairB (splitK (fK (fetch ps pc)) sk)).1))

/-- The new stacks string. -/
def skOut (ps pc st sk : List Bool) : List Bool :=
  skSel pc (fOp (fetch ps pc)) sk (unpairB (splitK (fK (fetch ps pc)) sk)).1
    (unpairB (splitK (fK (fetch ps pc)) sk)).2
    (true :: lookup (fTb (fetch ps pc)) st ++ [false])

/-- The string-level step, on program, program counter, state and stacks. -/
def sstepParts (ps pc st sk : List Bool) : List Bool :=
  pairB ps (pairB (pcOut ps pc st) (pairB (stOut ps pc st sk) (skOut ps pc st sk)))

/-- The string-level step. -/
def sstep (y : List Bool) : List Bool :=
  sstepParts (unpairB y).1 (unpairB (unpairB y).2).1 (unpairB (unpairB (unpairB y).2).2).1
    (unpairB (unpairB (unpairB y).2).2).2

/-! ## Correctness on encodings -/

theorem fetch_encP (P : List Instr) (n : ℕ) :
    fetch (encP P) (un (n + 1)) = match P[n]? with
      | none => []
      | some i => encNs (instrNs i) := by
  rw [fetch, un_succ, List.tail_cons, un_length]
  exact fetch_spec P n

theorem lookup_encNs (tbl : List ℕ) (i : List Bool) :
    lookup (encNs tbl) i = un (tbl.getD i.length 0) := lookup_spec _ _

theorem splitK_encLL (k : ℕ) (S : List (List ℕ)) :
    unpairB (splitK (un k) (encLL S)) = (encLL (S.drop k), encLL (S.take k)) := by
  rw [splitK, un_length, move_iter_encLL, unpairB_pairB, List.nil_append]

section fields

variable (a b c d e : ℕ) (tbl : List ℕ)

theorem fOp_enc : fOp (encNs (a :: b :: c :: d :: e :: tbl)) = un (a + 1) := by simp [fOp]

theorem fK_enc : fK (encNs (a :: b :: c :: d :: e :: tbl)) = un b := by simp [fK, un_succ]

theorem fW_enc : fW (encNs (a :: b :: c :: d :: e :: tbl)) = un c := by simp [fW, un_succ]

theorem fN1_enc : fN1 (encNs (a :: b :: c :: d :: e :: tbl)) = un (d + 1) := by simp [fN1]

theorem fN2_enc : fN2 (encNs (a :: b :: c :: d :: e :: tbl)) = un (e + 1) := by simp [fN2]

theorem fTb_enc : fTb (encNs (a :: b :: c :: d :: e :: tbl)) = encNs tbl := by simp [fTb]

end fields

theorem un_one : un 1 = [true] := rfl
theorem un_two : un 2 = [true, true] := rfl
theorem un_three : un 3 = [true, true, true] := rfl
theorem un_four : un 4 = [true, true, true, true] := rfl
theorem un_five : un 5 = [true, true, true, true, true] := rfl
theorem un_six : un 6 = [true, true, true, true, true, true] := rfl
theorem un_seven : un 7 = [true, true, true, true, true, true, true] := rfl

theorem sel_un (n : ℕ) (a b : List Bool) : sel (un n) a b = if n = 0 then a else b := by
  cases n <;> simp [un_succ]

/-- The three outputs compute the step. -/
theorem out_spec (P : List Instr) (pc : Option ℕ) (v : ℕ) (S : List (List ℕ)) :
    pcOut (encP P) (encPc pc) (un v) = encPc (step P ⟨pc, v, S⟩).pc ∧
    stOut (encP P) (encPc pc) (un v) (encLL S) = un (step P ⟨pc, v, S⟩).state ∧
    skOut (encP P) (encPc pc) (un v) (encLL S) = encLL (step P ⟨pc, v, S⟩).stk := by
  cases pc with
  | none => simp [pcOut, stOut, skOut, pcSel, stSel, skSel, encPc, step]
  | some n =>
    have hf := fetch_encP P n
    simp only [pcOut, stOut, skOut, encPc, step]
    cases h : P[n]? with
    | none =>
      rw [h] at hf
      simp only [hf]
      simp [pcSel, stSel, skSel, fOp, un_succ]
    | some i =>
      rw [h] at hf
      simp only [hf]
      cases i with
      | push k tbl next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · have := ins_spec [tbl.getD v 0] S k
          simp only [encNs_cons, encN, encNs_nil, List.append_nil,
            un_succ, List.cons_append] at this
          simpa [skSel, un_succ] using this
      | pop k tbl w next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length, hd_drop_encLL,
          List.length_append, mulU]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ, pop_spec]
      | peek k tbl w next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length, hd_drop_encLL,
          List.length_append, mulU]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | load tbl next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | branch tbl next₁ next₂ =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp only [pcSel, sel_un]
          by_cases hz : tbl[v]?.getD 0 = 0 <;> simp [hz, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | goto tbl =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | halt =>
        simp only [instrNs, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]

/-- The string-level step commutes with the step of the machine. -/
theorem sstep_encCfg (P : List Instr) (cfg : Cfg) :
    sstep (encCfg P cfg) = encCfg P (step P cfg) := by
  obtain ⟨pc, v, S⟩ := cfg
  obtain ⟨h1, h2, h3⟩ := out_spec P pc v S
  simp only [sstep, encCfg, unpairB_pairB, sstepParts, h1, h2, h3]

theorem sstep_iter (P : List Instr) (cfg : Cfg) (t : ℕ) :
    sstep^[t] (encCfg P cfg) = encCfg P ((step P)^[t] cfg) := by
  induction t generalizing cfg with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sstep_encCfg, ih]

/-! ## The measure, on all strings -/

theorem tail_length_le (s : List Bool) : s.tail.length ≤ s.length := by simp

theorem fetch_length (ps pc : List Bool) : (fetch ps pc).length ≤ ps.length :=
  (takeL_length _).trans (iter_length dropL dropL_length _ _)

theorem lookup_length (tb idx : List Bool) : (lookup tb idx).length ≤ tb.length :=
  (tail_length_le _).trans ((hd_length _).trans (iter_length dropN dropN_length _ _))

theorem fN1_length (I : List Bool) : (fN1 I).length ≤ I.length :=
  (hd_length _).trans ((dropN_length _).trans ((dropN_length _).trans (dropN_length _)))

theorem fN2_length (I : List Bool) : (fN2 I).length ≤ I.length :=
  (hd_length _).trans ((dropN_length _).trans ((dropN_length _).trans
    ((dropN_length _).trans (dropN_length _))))

theorem fTb_length (I : List Bool) : (fTb I).length ≤ I.length :=
  (dropN_length _).trans ((dropN_length _).trans ((dropN_length _).trans
    ((dropN_length _).trans (dropN_length _))))

theorem pcOut_length (ps pc st : List Bool) :
    (pcOut ps pc st).length ≤ pc.length + ps.length + 1 := by
  have h0 := fetch_length ps pc
  have h1 := fN1_length (fetch ps pc)
  have h2 := fN2_length (fetch ps pc)
  have h3 := (lookup_length (fTb (fetch ps pc)) st).trans (fTb_length _)
  unfold pcOut pcSel
  repeat' apply sel_length
  all_goals (try simp only [List.length_cons, List.length_nil]); omega

theorem stOut_length (ps pc st sk : List Bool) :
    (stOut ps pc st sk).length ≤ st.length + ps.length := by
  have h0 := fetch_length ps pc
  have h3 := fun idx => (lookup_length (fTb (fetch ps pc)) idx).trans (fTb_length _)
  have h4 := h3 st
  have h5 := h3 (mulU st (fW (fetch ps pc)) ++ hd (unpairB (splitK (fK (fetch ps pc)) sk)).1)
  unfold stOut stSel
  repeat' apply sel_length
  all_goals omega

theorem skOut_length (ps pc st sk : List Bool) :
    (skOut ps pc st sk).length ≤ sk.length + ps.length + 2 := by
  have h0 := fetch_length ps pc
  have h3 := (lookup_length (fTb (fetch ps pc)) st).trans (fTb_length _)
  obtain ⟨d', e1, e2⟩ := move_iter (fK (fetch ps pc)).length sk []
  have e3 : unpairB (splitK (fK (fetch ps pc)) sk) = (dropL^[(fK (fetch ps pc)).length] sk, d') := by
    rw [splitK, e1, unpairB_pairB]
  have h6 := popT_length (dropL^[(fK (fetch ps pc)).length] sk)
  unfold skOut skSel
  rw [e3]
  repeat' apply sel_length
  all_goals simp only [List.length_cons, List.length_nil, List.length_append] at *; omega

/-- The measure: a multiple of the length of the program part. -/
def smeasure (y : List Bool) : ℕ := 5 * (unpairB y).1.length + 7

theorem smeasure_sstep (y : List Bool) : smeasure (sstep y) ≤ smeasure y := by
  simp [smeasure, sstep, sstepParts, unpairB_pairB]

theorem sstep_length (y : List Bool) : (sstep y).length ≤ y.length + smeasure y := by
  have a1 := unpairB_length y
  have a2 := unpairB_length (unpairB y).2
  have a3 := unpairB_length (unpairB (unpairB y).2).2
  have b1 := pcOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1
  have b2 := stOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2
  have b3 := skOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2
  simp only [sstep, sstepParts, pairB_length, smeasure]
  omega

theorem smeasure_le (y : List Bool) : smeasure y ≤ 7 * y.length + 7 := by
  have a1 := unpairB_length y
  simp only [smeasure]
  omega

end PEqualNP.Library.Universal
