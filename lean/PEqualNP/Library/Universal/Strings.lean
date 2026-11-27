import PEqualNP.Library.Universal.IM
import PEqualNP.Library.Universal.Pair

/-!
# Bit-string encodings of programs and configurations, and string primitives

Helper module (proofs only, no statement may use it). Pure mathematics on bit strings.

Encodings. A number `n` in a list is `un (n + 1) ++ [false]`; a list of numbers is the
concatenation; a list of lists adds a `false` after each inner list. An instruction is the list
of numbers `[opcode, k, w, next₁, next₂] ++ table`; a program is the list of its instructions.

Primitives. Each is a small total function on bit strings; `SStep.lean` lists the toolbox item
that computes each of them.
-/

namespace PEqualNP.Library.Universal

/-! ## Unary -/

theorem un_succ (n : ℕ) : un (n + 1) = true :: un n := rfl

@[simp] theorem un_zero : un 0 = [] := rfl

@[simp] theorem un_length (n : ℕ) : (un n).length = n := by simp [un]

theorem un_inj {a b : ℕ} (h : un a = un b) : a = b := by
  have := congrArg List.length h
  simpa using this

/-! ## Encodings -/

/-- A number inside a list. -/
def encN (n : ℕ) : List Bool := un (n + 1) ++ [false]

/-- A list of numbers, without terminator. -/
def encNs (l : List ℕ) : List Bool := l.flatMap encN

/-- A list of numbers with its terminator. -/
def encL (l : List ℕ) : List Bool := encNs l ++ [false]

/-- A list of lists of numbers. -/
def encLL (S : List (List ℕ)) : List Bool := S.flatMap encL

@[simp] theorem encNs_nil : encNs [] = [] := rfl

theorem encNs_cons (a : ℕ) (l : List ℕ) : encNs (a :: l) = encN a ++ encNs l := rfl

theorem encNs_append (l m : List ℕ) : encNs (l ++ m) = encNs l ++ encNs m := by
  simp [encNs]

@[simp] theorem encLL_nil : encLL [] = [] := rfl

theorem encLL_cons (a : List ℕ) (S : List (List ℕ)) :
    encLL (a :: S) = encNs a ++ false :: encLL S := by
  simp [encLL, encL]

theorem encLL_append (S T : List (List ℕ)) : encLL (S ++ T) = encLL S ++ encLL T := by
  simp [encLL]

/-- The numbers of an instruction: `[opcode, k, w, next₁, next₂] ++ table`. -/
def instrNs : Instr → List ℕ
  | .push k tbl next => [0, k, 0, next, 0] ++ tbl
  | .pop k tbl w next => [1, k, w, next, 0] ++ tbl
  | .peek k tbl w next => [2, k, w, next, 0] ++ tbl
  | .load tbl next => [3, 0, 0, next, 0] ++ tbl
  | .branch tbl next₁ next₂ => [4, 0, 0, next₁, next₂] ++ tbl
  | .goto tbl => [5, 0, 0, 0, 0] ++ tbl
  | .halt => [6, 0, 0, 0, 0]

/-- A program. -/
def encP (P : List Instr) : List Bool := encLL (P.map instrNs)

/-- A program counter: empty when halted, `un (n + 1)` at `n`. -/
def encPc : Option ℕ → List Bool
  | none => []
  | some n => un (n + 1)

/-- A configuration, containing the program. -/
def encCfg (P : List Instr) (c : Cfg) : List Bool :=
  pairB (encP P) (pairB (encPc c.pc) (pairB (un c.state) (encLL c.stk)))

/-- A code: the program paired with the header `[nstk, pc₀, state₀, kin, kout]`. -/
def encCode (c : Code) : List Bool :=
  pairB (encP c.prog) (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout])

/-! ## Primitives -/

/-- The leading run of `true`: the first number of a list, as `un (n + 1)`, or empty. -/
def hd (s : List Bool) : List Bool := s.takeWhile id

/-- Drop through the first `false`: drop the first number of a list. -/
def dropN (s : List Bool) : List Bool := (s.dropWhile id).tail

/-- Select: the second argument if the flag is empty, else the third. -/
def sel (f a b : List Bool) : List Bool := if f = [] then a else b

/-- Unary multiplication. -/
def mulU (u v : List Bool) : List Bool := un (u.length * v.length)

/-- The first inner list of a list of lists, without its terminator. The flag says that the
reader is inside a number. -/
def takeLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => true :: takeLA true r
  | true, false :: r => false :: takeLA false r
  | false, false :: _ => []

/-- Drop the first inner list of a list of lists, with its terminator. -/
def dropLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => dropLA true r
  | true, false :: r => dropLA false r
  | false, false :: r => r

/-- The first inner list of a list of lists, with its terminator. -/
def headLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => true :: headLA true r
  | true, false :: r => false :: headLA false r
  | false, false :: _ => [false]

/-- The first inner list, without its terminator. -/
def takeL (s : List Bool) : List Bool := takeLA false s

/-- Drop the first inner list. -/
def dropL (s : List Bool) : List Bool := dropLA false s

/-- The first inner list, with its terminator. -/
def headL (s : List Bool) : List Bool := headLA false s

/-- Move one inner list across: on the pair (remaining, done), the first inner list of the
remaining part is appended to the done part. -/
def move (y : List Bool) : List Bool :=
  pairB (dropL (unpairB y).1) ((unpairB y).2 ++ headL (unpairB y).1)

/-- Pop the first number of a list, when there is one. -/
def popT : List Bool → List Bool
  | true :: r => dropN (true :: r)
  | s => s

/-- Every `true` becomes `true, false`. -/
def spread (s : List Bool) : List Bool := s.flatMap fun b => if b then [true, false] else [false]

/-- Every `false` becomes `true, false`. -/
def bump (s : List Bool) : List Bool := s.flatMap fun b => if b then [true] else [true, false]

/-- Every symbol becomes `false`. -/
def blank (s : List Bool) : List Bool := s.map fun _ => false

/-! ## Specifications on encodings -/

@[simp] theorem sel_nil (a b : List Bool) : sel [] a b = a := rfl

@[simp] theorem sel_cons (x : Bool) (f a b : List Bool) : sel (x :: f) a b = b := by
  simp [sel]

theorem sel_append_left (f p a b : List Bool) : sel f (p ++ a) (p ++ b) = p ++ sel f a b := by
  unfold sel; split <;> rfl

@[simp] theorem hd_nil : hd [] = [] := rfl

@[simp] theorem dropN_nil : dropN [] = [] := rfl

theorem hd_un (n : ℕ) (r : List Bool) : hd (un n ++ false :: r) = un n := by
  induction n with
  | zero => simp [hd]
  | succ n ih => simpa [hd, un_succ] using ih

theorem dropN_un (n : ℕ) (r : List Bool) : dropN (un n ++ false :: r) = r := by
  induction n with
  | zero => simp [dropN]
  | succ n ih => simpa [dropN, un_succ] using ih

@[simp] theorem hd_encNs_cons (a : ℕ) (l : List ℕ) : hd (encNs (a :: l)) = un (a + 1) := by
  rw [encNs_cons, encN, List.append_assoc]; exact hd_un _ _

@[simp] theorem dropN_encNs_cons (a : ℕ) (l : List ℕ) : dropN (encNs (a :: l)) = encNs l := by
  rw [encNs_cons, encN, List.append_assoc]; exact dropN_un _ _

theorem dropN_iter_encNs (i : ℕ) (l : List ℕ) : dropN^[i] (encNs l) = encNs (l.drop i) := by
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simpa using ih []
    | cons a l => simpa using ih l

/-- Table lookup with default `0`. -/
theorem lookup_spec (i : ℕ) (l : List ℕ) :
    (hd (dropN^[i] (encNs l))).tail = un (l.getD i 0) := by
  rw [dropN_iter_encNs]
  induction i generalizing l with
  | zero => cases l <;> simp [un_succ]
  | succ i ih =>
    cases l with
    | nil => simp
    | cons a l => simpa using ih l

theorem takeLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    takeLA b (un n ++ true :: false :: r) = un n ++ true :: false :: takeLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [takeLA]
  | succ n ih => cases b <;> simp [un_succ, takeLA, ih]

theorem dropLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    dropLA b (un n ++ true :: false :: r) = dropLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [dropLA]
  | succ n ih => cases b <;> simp [un_succ, dropLA, ih]

theorem headLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    headLA b (un n ++ true :: false :: r) = un n ++ true :: false :: headLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [headLA]
  | succ n ih => cases b <;> simp [un_succ, headLA, ih]

theorem encN_eq (a : ℕ) : encN a = un a ++ [true, false] := by
  induction a with
  | zero => rfl
  | succ a ih => rw [encN, un_succ, List.cons_append, ← encN, ih, un_succ]; rfl

theorem takeL_encNs (l : List ℕ) (r : List Bool) : takeL (encNs l ++ false :: r) = encNs l := by
  induction l with
  | nil => simp [takeL, takeLA]
  | cons a l ih =>
    rw [takeL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [takeLA_un, ih]

theorem dropL_encNs (l : List ℕ) (r : List Bool) : dropL (encNs l ++ false :: r) = r := by
  induction l with
  | nil => simp [dropL, dropLA]
  | cons a l ih =>
    rw [dropL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [dropLA_un, ih]

theorem headL_encNs (l : List ℕ) (r : List Bool) :
    headL (encNs l ++ false :: r) = encNs l ++ [false] := by
  induction l with
  | nil => simp [headL, headLA]
  | cons a l ih =>
    rw [headL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [headLA_un, ih]

@[simp] theorem takeL_nil : takeL [] = [] := rfl

@[simp] theorem dropL_nil : dropL [] = [] := rfl

@[simp] theorem headL_nil : headL [] = [] := rfl

theorem dropL_iter_nil (k : ℕ) : dropL^[k] [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

theorem dropL_iter_encLL (k : ℕ) (S : List (List ℕ)) :
    dropL^[k] (encLL S) = encLL (S.drop k) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases S with
    | nil => simpa using ih []
    | cons a S => rw [encLL_cons, dropL_encNs]; simpa using ih S

/-- Fetching an instruction: empty outside the program. -/
theorem fetch_spec (P : List Instr) (n : ℕ) :
    takeL (dropL^[n] (encP P)) = match P[n]? with
      | none => []
      | some i => encNs (instrNs i) := by
  rw [encP, dropL_iter_encLL]
  induction P generalizing n with
  | nil => simp
  | cons i P ih =>
    cases n with
    | zero => simp [encLL_cons, takeL_encNs]
    | succ n => simpa using ih n

theorem move_pairB (r d : List Bool) : move (pairB r d) = pairB (dropL r) (d ++ headL r) := by
  simp [move, unpairB_pairB]

theorem move_iter_encLL (k : ℕ) (S : List (List ℕ)) (d : List Bool) :
    move^[k] (pairB (encLL S) d) = pairB (encLL (S.drop k)) (d ++ encLL (S.take k)) := by
  induction k generalizing S d with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, move_pairB]
    cases S with
    | nil => simpa using ih [] d
    | cons a S =>
      rw [encLL_cons, dropL_encNs, headL_encNs, ih]
      simp [encLL_cons]

/-- The top index of the `k`-th stack. -/
theorem hd_drop_encLL (S : List (List ℕ)) (k : ℕ) :
    hd (encLL (S.drop k)) = un (topIndex (S.getD k [])) := by
  induction S generalizing k with
  | nil => simp [topIndex]
  | cons a S ih =>
    cases k with
    | zero =>
      cases a with
      | nil => simp [encLL_cons, hd, topIndex]
      | cons s a =>
        simp only [List.drop_zero, encLL_cons, encNs_cons, encN, List.append_assoc,
          List.cons_append, List.nil_append]
        rw [hd_un]; simp [topIndex]
    | succ k => simpa using ih k

/-- Inserting numbers on top of the `k`-th inner list; nothing happens outside the range. -/
theorem ins_spec (l : List ℕ) (S : List (List ℕ)) (k : ℕ) :
    sel (encLL (S.drop k)) (encLL (S.take k))
        (encLL (S.take k) ++ (encNs l ++ encLL (S.drop k))) =
      encLL (S.set k (l ++ S.getD k [])) := by
  induction S generalizing k with
  | nil => simp
  | cons a S ih =>
    cases k with
    | zero =>
      simp [encLL_cons, encNs_append]
      cases h : encNs a <;> simp
    | succ k =>
      have := ih k
      simp only [List.drop_succ_cons, List.take_succ_cons, List.set_cons_succ, encLL_cons,
        List.getD_cons_succ, List.append_assoc, List.cons_append] at this ⊢
      rw [← this]
      unfold sel; split <;> simp

/-- Popping the `k`-th inner list; nothing happens outside the range. -/
theorem pop_spec (S : List (List ℕ)) (k : ℕ) :
    encLL (S.take k) ++ popT (encLL (S.drop k)) = encLL (S.set k (S.getD k []).tail) := by
  induction S generalizing k with
  | nil => simp [popT]
  | cons a S ih =>
    cases k with
    | zero =>
      cases a with
      | nil => simp [encLL_cons, popT]
      | cons s a =>
        simp only [List.take_zero, encLL_nil, List.nil_append, List.drop_zero, List.set_cons_zero,
          List.getD_cons_zero, List.tail_cons]
        rw [encLL_cons, encLL_cons, encNs_cons, encN, un_succ]
        simp only [List.cons_append, List.append_assoc, popT]
        rw [← List.cons_append, ← un_succ, dropN_un]
        simp
    | succ k =>
      have := ih k
      simp only [List.drop_succ_cons, List.take_succ_cons, List.set_cons_succ, encLL_cons,
        List.getD_cons_succ, List.append_assoc, List.cons_append] at this ⊢
      rw [this]

/-! ## Input symbols -/

theorem bump_append (a b : List Bool) : bump (a ++ b) = bump a ++ bump b := by
  simp [bump]

theorem inX_spec (x : List Bool) :
    bump (spread x) = encNs (x.map fun b => cond b 1 0) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h : spread (b :: x) = (if b then [true, false] else [false]) ++ spread x := by
      simp [spread]
    rw [h, bump_append, ih, List.map_cons, encNs_cons]
    cases b <;> rfl

theorem inW_spec (w : List Bool) :
    bump (bump (bump (spread w))) = encNs (w.map fun b => cond b 3 2) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have h : spread (b :: w) = (if b then [true, false] else [false]) ++ spread w := by
      simp [spread]
    rw [h, bump_append, bump_append, bump_append, ih, List.map_cons, encNs_cons]
    cases b <;> rfl

theorem blank_un (n : ℕ) : blank (un n) = encLL (List.replicate n []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [un_succ, List.replicate_succ, encLL_cons, ← ih]; rfl

/-! ## Lengths, on all strings -/

theorem hd_length (s : List Bool) : (hd s).length ≤ s.length :=
  (List.takeWhile_prefix _).length_le

theorem dropN_length (s : List Bool) : (dropN s).length ≤ s.length := by
  have := (List.dropWhile_suffix (l := s) id).length_le
  simp only [dropN, List.length_tail]
  omega

theorem iter_length (g : List Bool → List Bool) (hg : ∀ s, (g s).length ≤ s.length) (k : ℕ)
    (s : List Bool) : (g^[k] s).length ≤ s.length := by
  induction k generalizing s with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply]; exact (ih _).trans (hg s)

theorem takeLA_length (b : Bool) (s : List Bool) : (takeLA b s).length ≤ s.length := by
  induction s generalizing b with
  | nil => simp [takeLA]
  | cons a s ih =>
    cases a <;> cases b <;> simp [takeLA] <;> exact ih _

theorem head_drop_LA (b : Bool) (s : List Bool) : headLA b s ++ dropLA b s = s := by
  induction s generalizing b with
  | nil => simp [headLA, dropLA]
  | cons a s ih =>
    cases a <;> cases b <;> simp [headLA, dropLA] <;> exact ih _

theorem headL_dropL (s : List Bool) : headL s ++ dropL s = s := head_drop_LA false s

theorem headL_dropL_length (s : List Bool) : (headL s).length + (dropL s).length = s.length := by
  have := congrArg List.length (headL_dropL s)
  simpa using this

theorem takeL_length (s : List Bool) : (takeL s).length ≤ s.length := takeLA_length false s

theorem dropL_length (s : List Bool) : (dropL s).length ≤ s.length := by
  have := headL_dropL_length s; omega

theorem popT_length (s : List Bool) : (popT s).length ≤ s.length := by
  unfold popT
  split
  · exact dropN_length _
  · exact le_rfl

theorem sel_length (f a b : List Bool) (B : ℕ) (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (sel f a b).length ≤ B := by
  unfold sel; split <;> assumption

theorem unpairB_length (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have h := congrArg List.length (List.takeWhile_append_dropWhile (p := id) (l := s))
  simp only [List.length_append] at h
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  omega

theorem pairB_length (a b : List Bool) : (pairB a b).length = 2 * a.length + b.length + 1 := by
  simp [pairB]; omega

/-- The move does not lengthen its input by more than one symbol (and by nothing on a pair). -/
theorem move_length (y : List Bool) : (move y).length ≤ y.length + 1 := by
  have h := unpairB_length y
  have h2 := headL_dropL_length (unpairB y).1
  simp only [move, pairB_length, List.length_append]
  omega

/-- After any number of moves from a pair, the two parts together are no longer than at the
start, and the remaining part is the iterated drop. -/
theorem move_iter (k : ℕ) (r d : List Bool) :
    ∃ d', move^[k] (pairB r d) = pairB (dropL^[k] r) d' ∧
      (dropL^[k] r).length + d'.length ≤ r.length + d.length := by
  induction k generalizing r d with
  | zero => exact ⟨d, rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨d', h1, h2⟩ := ih (dropL r) (d ++ headL r)
    refine ⟨d', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, move_pairB, h1, Function.iterate_succ_apply]
    · have := headL_dropL_length r
      rw [Function.iterate_succ_apply]
      simp only [List.length_append] at h2
      omega

end PEqualNP.Library.Universal
