import PEqualNP.MetaComplexity.Helpers.Verifier

/-!
# Rebuilding the full witness of partial MCSP from one row

Helper for "partial MCSP has short witnesses". The full witness of the verifier is the list of
the rows of all inputs, in increasing order. Here it is rebuilt from the last row alone and the
table of the instance.

The state is a string over `Sym`: first the entries not yet used (a run of end symbols), then
the rows built so far. One step `gS` removes the last entry `e` of the leading run and puts,
in front of the first row, a copy of that row with its input bits decremented and with entry
`e`. The step is the concatenation of two finite-state transducer runs (`prevStr`, `dropStr`).

* `rowOf`, `gS_row`, `gS_length`, `rowOf_length_le`: on every string, the step keeps the length
  of the first row and lengthens the string by at most that length.
* `entStr`: the entries of a table code, all but the last, as symbols.
* `expandS`, `expandS_honest`: the iteration, and its value on the last honest row.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.Library.Machines PEqualNP.MetaComplexity

/-! ## General helpers -/

theorem run2_cons {A B Q : Type} (δ : Q → A → Q × Option B × Option B) (fin : Q → Option B)
    (q : Q) (a : A) (l : List A) :
    fstRun2 δ fin q (a :: l)
      = (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l := rfl

theorem nil_or_snoc {α : Type} (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    right
    rcases ih with rfl | ⟨L, b, rfl⟩
    · exact ⟨[], a, rfl⟩
    · exact ⟨a :: L, b, rfl⟩

theorem take_succ_getD {α : Type} (T : List α) (d : α) :
    ∀ k, k < T.length → T.take (k + 1) = T.take k ++ [T.getD k d] := by
  induction T with
  | nil => intro k hk; exact absurd hk (by simp)
  | cons a T ih =>
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      have hk' : k < T.length := by simpa using hk
      show a :: T.take (k + 1) = a :: (T.take k ++ [T.getD k d])
      rw [ih k hk']

theorem isEnd_symE (e : Option Bool) : (symE e).isEnd = true := by
  rcases e with _ | _ | _ <;> rfl

/-! ## The leading entries and the first row of any string -/

/-- The string without its leading end symbols. -/
def skipE : List Sym → List Sym
  | [] => []
  | s :: l => if s.isEnd then skipE l else s :: l

/-- The leading symbols that are not end symbols. -/
def runNE : List Sym → List Sym
  | [] => []
  | s :: l => if s.isEnd then [] else s :: runNE l

/-- The first row of a string, without its end symbol: skip the leading end symbols, then keep
the symbols before the next end symbol. -/
def rowOf (st : List Sym) : List Sym := runNE (skipE st)

/-- `R ++ X` starts with a row: `R` has no end symbol, `X` is empty or starts with an end
symbol, and `X` is empty when `R` is. -/
structure RowForm (R X : List Sym) : Prop where
  hR : ∀ s ∈ R, s.isEnd = false
  hX : X = [] ∨ ∃ e X', X = e :: X' ∧ e.isEnd = true
  hRX : R = [] → X = []

theorem skipE_end (s : Sym) (l : List Sym) (hs : s.isEnd = true) :
    skipE (s :: l) = skipE l := by simp [skipE, hs]

theorem skipE_ends (L rest : List Sym) (hL : ∀ s ∈ L, s.isEnd = true) :
    skipE (L ++ rest) = skipE rest := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    have hs : s.isEnd = true := hL s List.mem_cons_self
    show skipE (s :: (L ++ rest)) = _
    rw [skipE_end s _ hs]
    exact ih fun s' hs' => hL s' (List.mem_cons_of_mem _ hs')

theorem skipE_row (R X : List Sym) (h : RowForm R X) : skipE (R ++ X) = R ++ X := by
  cases R with
  | nil => rw [h.hRX rfl]; rfl
  | cons r R =>
    have hr : r.isEnd = false := h.hR r List.mem_cons_self
    show skipE (r :: (R ++ X)) = _
    rw [skipE, hr]
    rfl

theorem runNE_run (R X : List Sym) (hR : ∀ s ∈ R, s.isEnd = false)
    (hX : X = [] ∨ ∃ e X', X = e :: X' ∧ e.isEnd = true) : runNE (R ++ X) = R := by
  induction R with
  | nil =>
    rcases hX with rfl | ⟨e, X', rfl, he⟩
    · rfl
    · show runNE (e :: X') = []
      simp [runNE, he]
  | cons r R ih =>
    have hr : r.isEnd = false := hR r List.mem_cons_self
    show runNE (r :: (R ++ X)) = _
    rw [runNE, hr, ih fun s' hs' => hR s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem rowOf_form (L R X : List Sym) (hL : ∀ s ∈ L, s.isEnd = true) (h : RowForm R X) :
    rowOf (L ++ (R ++ X)) = R := by
  unfold rowOf
  rw [skipE_ends _ _ hL, skipE_row _ _ h]
  exact runNE_run R X h.hR h.hX

/-- Every string is a run of end symbols followed by a row form. -/
theorem exists_form (st : List Sym) :
    ∃ L R X, st = L ++ (R ++ X) ∧ (∀ s ∈ L, s.isEnd = true) ∧ RowForm R X := by
  induction st with
  | nil => exact ⟨[], [], [], rfl, by simp, ⟨by simp, Or.inl rfl, fun _ => rfl⟩⟩
  | cons s st ih =>
    obtain ⟨L, R, X, rfl, hL, h⟩ := ih
    by_cases hs : s.isEnd = true
    · refine ⟨s :: L, R, X, rfl, ?_, h⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hs
      · exact hL x hx
    · have hs' : s.isEnd = false := by simpa using hs
      cases L with
      | nil =>
        refine ⟨[], s :: R, X, rfl, by simp, ⟨?_, h.hX, by simp⟩⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hs'
        · exact h.hR x hx
      | cons e L =>
        refine ⟨[], [s], (e :: L) ++ (R ++ X), rfl, by simp, ⟨?_, ?_, by simp⟩⟩
        · intro x hx
          rw [List.mem_singleton.1 hx]
          exact hs'
        · exact Or.inr ⟨e, L ++ (R ++ X), rfl, hL e List.mem_cons_self⟩

/-- Every string either starts with a row form, or is a nonempty run of end symbols followed
by a row form. -/
theorem exists_form' (st : List Sym) :
    (∃ R X, st = R ++ X ∧ RowForm R X) ∨
      ∃ L0 e R X, st = L0 ++ e :: (R ++ X) ∧ (∀ s ∈ L0, s.isEnd = true) ∧ e.isEnd = true ∧
        RowForm R X := by
  obtain ⟨L, R, X, rfl, hL, h⟩ := exists_form st
  rcases nil_or_snoc L with rfl | ⟨L0, e, rfl⟩
  · exact Or.inl ⟨R, X, rfl, h⟩
  · refine Or.inr ⟨L0, e, R, X, by simp, ?_, ?_, h⟩
    · intro s hs
      exact hL s (List.mem_append_left _ hs)
    · exact hL e (List.mem_append_right _ List.mem_cons_self)

theorem rowOf_snoc (L0 : List Sym) (e : Sym) (R X : List Sym)
    (hL0 : ∀ s ∈ L0, s.isEnd = true) (he : e.isEnd = true) (h : RowForm R X) :
    rowOf (L0 ++ e :: (R ++ X)) = R := by
  have e1 : L0 ++ e :: (R ++ X) = (L0 ++ [e]) ++ (R ++ X) := by simp
  rw [e1]
  refine rowOf_form _ R X ?_ h
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · exact hL0 s hs
  · rw [List.mem_singleton.1 hs]; exact he

theorem rowOf_length_le (st : List Sym) : (rowOf st).length ≤ st.length := by
  obtain ⟨L, R, X, rfl, hL, h⟩ := exists_form st
  rw [rowOf_form L R X hL h]
  simp only [List.length_append]
  omega

/-! ## Decrementing the input bits of a row -/

/-- Subtract one from the leading input bits: a leading `O` becomes `A` and the borrow goes
on; a leading `A` becomes `O` and the rest is kept; any other symbol stops the borrow. -/
def decS : List Sym → List Sym
  | [] => []
  | s :: l => if s = Sym.O then Sym.A :: decS l else if s = Sym.A then Sym.O :: l else s :: l

theorem decS_O (l : List Sym) : decS (Sym.O :: l) = Sym.A :: decS l := by simp [decS]

theorem decS_A (l : List Sym) : decS (Sym.A :: l) = Sym.O :: l := by simp [decS]

theorem decS_other (s : Sym) (l : List Sym) (h1 : s ≠ Sym.O) (h2 : s ≠ Sym.A) :
    decS (s :: l) = s :: l := by simp [decS, h1, h2]

theorem length_decS (l : List Sym) : (decS l).length = l.length := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    by_cases h1 : s = Sym.O
    · rw [h1, decS_O, List.length_cons, List.length_cons, ih]
    · by_cases h2 : s = Sym.A
      · rw [h2, decS_A]; rfl
      · rw [decS_other s l h1 h2]

theorem isEnd_decS (l : List Sym) (hl : ∀ s ∈ l, s.isEnd = false) :
    ∀ s ∈ decS l, s.isEnd = false := by
  induction l with
  | nil => intro s hs; exact absurd hs (by simp [decS])
  | cons r l ih =>
    intro s hs
    by_cases h1 : r = Sym.O
    · rw [h1, decS_O] at hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rfl
      · exact ih (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs')) s hs
    · by_cases h2 : r = Sym.A
      · rw [h2, decS_A] at hs
        rcases List.mem_cons.1 hs with rfl | hs
        · rfl
        · exact hl s (List.mem_cons_of_mem _ hs)
      · rw [decS_other r l h1 h2] at hs
        exact hl s hs

theorem decS_bits (m : ℕ) : ∀ (j : ℕ) (Y : List Sym), j + 1 < 2 ^ m →
    decS ((bitsL m (j + 1)).map bsym ++ Y) = (bitsL m j).map bsym ++ Y := by
  induction m with
  | zero => intro j Y h; exact absurd h (by simp)
  | succ m ih =>
    intro j Y h
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    by_cases hj : (j + 1) % 2 = 1
    · have h0 : ¬ j % 2 = 1 := by omega
      have h2 : j / 2 = (j + 1) / 2 := by omega
      have e1 : bitsL (m + 1) (j + 1) = true :: bitsL m ((j + 1) / 2) := by simp [bitsL, hj]
      have e2 : bitsL (m + 1) j = false :: bitsL m ((j + 1) / 2) := by simp [bitsL, h0, h2]
      rw [e1, e2]
      exact decS_A _
    · have h1 : j % 2 = 1 := by omega
      have h2 : (j + 1) / 2 = j / 2 + 1 := by omega
      have h3 : j / 2 + 1 < 2 ^ m := by omega
      have e1 : bitsL (m + 1) (j + 1) = false :: bitsL m (j / 2 + 1) := by simp [bitsL, hj, h2]
      have e2 : bitsL (m + 1) j = true :: bitsL m (j / 2) := by simp [bitsL, h1]
      rw [e1, e2]
      show decS (Sym.O :: ((bitsL m (j / 2 + 1)).map bsym ++ Y))
        = Sym.A :: ((bitsL m (j / 2)).map bsym ++ Y)
      rw [decS_O, ih _ _ h3]

theorem decS_rowPre (n j : ℕ) (C : Circuit) (e e' : Option Bool) (h : j + 1 < 2 ^ n) :
    decS (rowPre (bitsL n (j + 1), C, e)) = rowPre (bitsL n j, C, e') :=
  decS_bits n j (encBody C) h

theorem rowPre_ne_nil (w : WRow) : rowPre w ≠ [] := by
  intro h
  have h' : (rowPre w).length = 0 := by rw [h]; rfl
  simp only [rowPre, encBody, List.length_append, List.length_cons] at h'
  omega

/-! ## The transducer that writes the new first row -/

/-- The states: reading the leading end symbols, holding the last one read; borrowing in the
first row, with the entry to write; copying the first row, with the entry to write; done. -/
inductive PrevQ where
  | lead (h : Option Sym)
  | bor (e : Sym)
  | cp (e : Sym)
  | done
  deriving DecidableEq, Fintype

/-- One step while borrowing. -/
def borStep (e s : Sym) : PrevQ × Option Sym × Option Sym :=
  if s = Sym.O then (PrevQ.bor e, some Sym.A, none)
  else if s = Sym.A then (PrevQ.cp e, some Sym.O, none)
  else if s.isEnd then (PrevQ.done, some e, none)
  else (PrevQ.cp e, some s, none)

/-- One step while copying. -/
def cpStep (e s : Sym) : PrevQ × Option Sym × Option Sym :=
  if s.isEnd then (PrevQ.done, some e, none) else (PrevQ.cp e, some s, none)

/-- The transducer: copy the leading end symbols but the last, then write the first row with
its input bits decremented and the last leading end symbol as its entry. With no leading end
symbol nothing is written. -/
def δprev : PrevQ → Sym → PrevQ × Option Sym × Option Sym
  | PrevQ.lead h, s =>
      if s.isEnd then (PrevQ.lead (some s), h, none)
      else match h with
        | none => (PrevQ.done, none, none)
        | some e => borStep e s
  | PrevQ.bor e, s => borStep e s
  | PrevQ.cp e, s => cpStep e s
  | PrevQ.done, _ => (PrevQ.done, none, none)

/-- At the end of the input the held symbol or the entry is written. -/
def finPrev : PrevQ → Option Sym
  | PrevQ.lead h => h
  | PrevQ.bor e => some e
  | PrevQ.cp e => some e
  | PrevQ.done => none

/-- The leading end symbols but the last, then the new first row. -/
def prevStr (l : List Sym) : List Sym := fstRun2 δprev finPrev (PrevQ.lead none) l

theorem prev_done (r : List Sym) : fstRun2 δprev finPrev PrevQ.done r = [] := by
  induction r with
  | nil => rfl
  | cons s r ih => exact ih

theorem prev_cp (e : Sym) (R X : List Sym) (hR : ∀ s ∈ R, s.isEnd = false)
    (hX : X = [] ∨ ∃ x X', X = x :: X' ∧ x.isEnd = true) :
    fstRun2 δprev finPrev (PrevQ.cp e) (R ++ X) = R ++ [e] := by
  induction R with
  | nil =>
    rcases hX with rfl | ⟨x, X', rfl, hx⟩
    · rfl
    · have : δprev (PrevQ.cp e) x = (PrevQ.done, some e, none) := by simp [δprev, cpStep, hx]
      rw [List.nil_append, run2_cons, this, prev_done]
      rfl
  | cons r R ih =>
    have hr : r.isEnd = false := hR r List.mem_cons_self
    have : δprev (PrevQ.cp e) r = (PrevQ.cp e, some r, none) := by simp [δprev, cpStep, hr]
    rw [List.cons_append, run2_cons, this, ih fun s' hs' => hR s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem prev_bor (e : Sym) (R X : List Sym) (hR : ∀ s ∈ R, s.isEnd = false)
    (hX : X = [] ∨ ∃ x X', X = x :: X' ∧ x.isEnd = true) :
    fstRun2 δprev finPrev (PrevQ.bor e) (R ++ X) = decS R ++ [e] := by
  induction R with
  | nil =>
    rcases hX with rfl | ⟨x, X', rfl, hx⟩
    · rfl
    · have h1 : x ≠ Sym.O := by rintro rfl; exact absurd hx (by decide)
      have h2 : x ≠ Sym.A := by rintro rfl; exact absurd hx (by decide)
      have : δprev (PrevQ.bor e) x = (PrevQ.done, some e, none) := by
        simp [δprev, borStep, h1, h2, hx]
      rw [List.nil_append, run2_cons, this, prev_done]
      rfl
  | cons r R ih =>
    have hr : r.isEnd = false := hR r List.mem_cons_self
    have hR' : ∀ s ∈ R, s.isEnd = false := fun s' hs' => hR s' (List.mem_cons_of_mem _ hs')
    by_cases h1 : r = Sym.O
    · have : δprev (PrevQ.bor e) r = (PrevQ.bor e, some Sym.A, none) := by
        simp [δprev, borStep, h1]
      rw [List.cons_append, run2_cons, this, ih hR', h1, decS_O]
      rfl
    · by_cases h2 : r = Sym.A
      · have : δprev (PrevQ.bor e) r = (PrevQ.cp e, some Sym.O, none) := by
          simp [δprev, borStep, h2]
        rw [List.cons_append, run2_cons, this, prev_cp e R X hR' hX, h2, decS_A]
        rfl
      · have : δprev (PrevQ.bor e) r = (PrevQ.cp e, some r, none) := by
          simp [δprev, borStep, h1, h2, hr]
        rw [List.cons_append, run2_cons, this, prev_cp e R X hR' hX, decS_other r R h1 h2]
        rfl

theorem prev_lead (L0 : List Sym) (e : Sym) (rest : List Sym)
    (hL0 : ∀ s ∈ L0, s.isEnd = true) (he : e.isEnd = true) : ∀ h : Option Sym,
    fstRun2 δprev finPrev (PrevQ.lead h) (L0 ++ e :: rest)
      = h.toList ++ (L0 ++ fstRun2 δprev finPrev (PrevQ.lead (some e)) rest) := by
  induction L0 with
  | nil =>
    intro h
    have : δprev (PrevQ.lead h) e = (PrevQ.lead (some e), h, none) := by simp [δprev, he]
    rw [List.nil_append, run2_cons, this]
    simp
  | cons s L0 ih =>
    intro h
    have hs : s.isEnd = true := hL0 s List.mem_cons_self
    have : δprev (PrevQ.lead h) s = (PrevQ.lead (some s), h, none) := by simp [δprev, hs]
    rw [List.cons_append, run2_cons, this,
      ih (fun s' hs' => hL0 s' (List.mem_cons_of_mem _ hs')) (some s)]
    simp

theorem prev_lead_row (e : Sym) (R X : List Sym) (h : RowForm R X) :
    fstRun2 δprev finPrev (PrevQ.lead (some e)) (R ++ X) = decS R ++ [e] := by
  cases R with
  | nil => rw [h.hRX rfl]; rfl
  | cons r R =>
    have hr : r.isEnd = false := h.hR r List.mem_cons_self
    have : δprev (PrevQ.lead (some e)) r = δprev (PrevQ.bor e) r := by simp [δprev, hr]
    have key : fstRun2 δprev finPrev (PrevQ.lead (some e)) ((r :: R) ++ X)
        = fstRun2 δprev finPrev (PrevQ.bor e) ((r :: R) ++ X) := by
      rw [List.cons_append, run2_cons, run2_cons, this]
    rw [key]
    exact prev_bor e (r :: R) X h.hR h.hX

theorem prevStr_snoc (L0 : List Sym) (e : Sym) (R X : List Sym)
    (hL0 : ∀ s ∈ L0, s.isEnd = true) (he : e.isEnd = true) (h : RowForm R X) :
    prevStr (L0 ++ e :: (R ++ X)) = L0 ++ (decS R ++ [e]) := by
  unfold prevStr
  rw [prev_lead L0 e _ hL0 he none, prev_lead_row e R X h]
  rfl

theorem prevStr_row (R X : List Sym) (h : RowForm R X) : prevStr (R ++ X) = [] := by
  cases R with
  | nil => rw [h.hRX rfl]; rfl
  | cons r R =>
    have hr : r.isEnd = false := h.hR r List.mem_cons_self
    have : δprev (PrevQ.lead none) r = (PrevQ.done, none, none) := by simp [δprev, hr]
    unfold prevStr
    rw [List.cons_append, run2_cons, this, prev_done]
    rfl

/-! ## The transducer that drops the leading end symbols -/

/-- The state says whether a symbol that is not an end symbol was read. -/
def δdrop : Bool → Sym → Bool × Option Sym × Option Sym
  | false, s => if s.isEnd then (false, none, none) else (true, some s, none)
  | true, s => (true, some s, none)

/-- Nothing is written at the end of the input. -/
def finDrop : Bool → Option Sym := fun _ => none

/-- The string without its leading end symbols. -/
def dropStr (l : List Sym) : List Sym := fstRun2 δdrop finDrop false l

theorem drop_copy (r : List Sym) : fstRun2 δdrop finDrop true r = r := by
  induction r with
  | nil => rfl
  | cons s r ih =>
    show s :: fstRun2 δdrop finDrop true r = _
    rw [ih]

theorem dropStr_eq (st : List Sym) : dropStr st = skipE st := by
  induction st with
  | nil => rfl
  | cons s st ih =>
    by_cases hs : s.isEnd = true
    · have : δdrop false s = (false, none, none) := by simp [δdrop, hs]
      have e : skipE (s :: st) = skipE st := skipE_end s st hs
      unfold dropStr
      rw [run2_cons, this, e]
      exact ih
    · have hs' : s.isEnd = false := by simpa using hs
      have : δdrop false s = (true, some s, none) := by simp [δdrop, hs']
      have e : skipE (s :: st) = s :: st := by rw [skipE, hs']; rfl
      unfold dropStr
      rw [run2_cons, this, e, drop_copy]
      rfl

/-! ## The step -/

/-- One step: the leading end symbols but the last, the new first row, then the old rows. -/
def gS (st : List Sym) : List Sym := prevStr st ++ dropStr st

theorem gS_snoc (L0 : List Sym) (e : Sym) (R X : List Sym)
    (hL0 : ∀ s ∈ L0, s.isEnd = true) (he : e.isEnd = true) (h : RowForm R X) :
    gS (L0 ++ e :: (R ++ X)) = L0 ++ (decS R ++ e :: (R ++ X)) := by
  have e1 : skipE (L0 ++ e :: (R ++ X)) = R ++ X := by
    rw [skipE_ends _ _ hL0, skipE_end e _ he, skipE_row _ _ h]
  unfold gS
  rw [prevStr_snoc L0 e R X hL0 he h, dropStr_eq, e1]
  simp

theorem gS_row_form (R X : List Sym) (h : RowForm R X) : gS (R ++ X) = R ++ X := by
  unfold gS
  rw [prevStr_row R X h, dropStr_eq, skipE_row R X h]
  rfl

/-- The step keeps the length of the first row, on every string. -/
theorem gS_row (st : List Sym) : (rowOf (gS st)).length = (rowOf st).length := by
  rcases exists_form' st with ⟨R, X, rfl, h⟩ | ⟨L0, e, R, X, rfl, hL0, he, h⟩
  · rw [gS_row_form R X h]
  · rw [gS_snoc L0 e R X hL0 he h, rowOf_snoc L0 e R X hL0 he h]
    by_cases hR : R = []
    · have hX : X = [] := h.hRX hR
      subst hR
      subst hX
      have : L0 ++ (decS [] ++ e :: ([] ++ [])) = L0 ++ e :: (([] : List Sym) ++ []) := rfl
      rw [this, rowOf_snoc L0 e [] [] hL0 he h]
    · have h' : RowForm (decS R) (e :: (R ++ X)) := by
        refine ⟨isEnd_decS R h.hR, Or.inr ⟨e, R ++ X, rfl, he⟩, ?_⟩
        intro h0
        have hl := length_decS R
        rw [h0] at hl
        exact absurd (List.length_eq_zero_iff.1 hl.symm) hR
      rw [rowOf_form L0 (decS R) (e :: (R ++ X)) hL0 h', length_decS]

/-- The step lengthens a string by at most the length of its first row. -/
theorem gS_length (st : List Sym) : (gS st).length ≤ st.length + (rowOf st).length := by
  rcases exists_form' st with ⟨R, X, rfl, h⟩ | ⟨L0, e, R, X, rfl, hL0, he, h⟩
  · rw [gS_row_form R X h]
    omega
  · rw [gS_snoc L0 e R X hL0 he h, rowOf_snoc L0 e R X hL0 he h]
    simp only [List.length_append, List.length_cons, length_decS]
    omega

/-! ## The entries of the instance as symbols -/

/-- The symbol of the entry written with the two bits `a`, `b`. -/
def entSym (a b : Bool) : Sym :=
  if a then (if b then Sym.E1 else Sym.E0) else Sym.En

/-- The transducer that writes the entries of a table code as symbols, all but the last. The
state holds the first bit of the current entry, if read, and the last entry read, if any. -/
def δent : Option Bool × Option Sym → Bool → (Option Bool × Option Sym) × Option Sym × Option Sym
  | (none, h), b => ((some b, h), none, none)
  | (some a, h), b => ((none, some (entSym a b)), h, none)

/-- Nothing is written at the end of the input. -/
def finEnt : Option Bool × Option Sym → Option Sym := fun _ => none

/-- The entries of a table code as symbols, all but the last. -/
def entStr (x : List Bool) : List Sym := fstRun2 δent finEnt (none, none) x

theorem encodePartial_cons' (o : Option Bool) (T : List (Option Bool)) :
    ∃ a b, encodePartial (o :: T) = a :: b :: encodePartial T ∧ entSym a b = symE o := by
  rcases o with _ | _ | _
  · exact ⟨false, false, by simp [encodePartial], rfl⟩
  · exact ⟨true, false, by simp [encodePartial], rfl⟩
  · exact ⟨true, true, by simp [encodePartial], rfl⟩

theorem ent_pair (h : Option Sym) (a b : Bool) (Y : List Bool) :
    fstRun2 δent finEnt (none, h) (a :: b :: Y)
      = h.toList ++ fstRun2 δent finEnt (none, some (entSym a b)) Y := by
  rw [run2_cons, run2_cons]
  simp [δent]

theorem ent_run (T : List (Option Bool)) (t : Option Bool) : ∀ h : Option Sym,
    fstRun2 δent finEnt (none, h) (encodePartial (T ++ [t])) = h.toList ++ T.map symE := by
  induction T with
  | nil =>
    intro h
    obtain ⟨a, b, e, _⟩ := encodePartial_cons' t []
    have e0 : encodePartial [] = [] := rfl
    rw [List.nil_append, e, e0, ent_pair]
    rfl
  | cons o T ih =>
    intro h
    obtain ⟨a, b, e, hs⟩ := encodePartial_cons' o (T ++ [t])
    rw [List.cons_append, e, ent_pair, ih, hs]
    rfl

theorem entStr_snoc (T : List (Option Bool)) (t : Option Bool) :
    entStr (encodePartial (T ++ [t])) = T.map symE :=
  ent_run T t none

/-! ## The iteration and its value on the last honest row -/

/-- The witness rebuilt from the instance `y` and a string `u` for the last row: start from the
entries of the instance but the last, followed by `u`, and apply the step `y.length` times. -/
def expandS (y : List Bool) (u : List Sym) : List Sym :=
  gS^[y.length] (entStr (instStr y) ++ u)

/-- One step on honest rows. -/
theorem gS_honest_step (n j : ℕ) (C : Circuit) (t e1 : Option Bool) (L0 rest : List Sym)
    (hL0 : ∀ s ∈ L0, s.isEnd = true) (h : j + 1 < 2 ^ n) :
    gS (L0 ++ symE t :: (encW (bitsL n (j + 1), C, e1) ++ rest))
      = L0 ++ (encW (bitsL n j, C, t) ++ (encW (bitsL n (j + 1), C, e1) ++ rest)) := by
  have e : encW (bitsL n (j + 1), C, e1) ++ rest
      = rowPre (bitsL n (j + 1), C, e1) ++ symE e1 :: rest := by simp [encW]
  have hf : RowForm (rowPre (bitsL n (j + 1), C, e1)) (symE e1 :: rest) :=
    ⟨isEnd_rowPre _, Or.inr ⟨symE e1, rest, rfl, isEnd_symE e1⟩,
      fun h0 => absurd h0 (rowPre_ne_nil _)⟩
  rw [e, gS_snoc L0 (symE t) _ _ hL0 (isEnd_symE t) hf, decS_rowPre n j C e1 t h]
  simp [encW]

/-- The state after the rows `k, ..., N` are built: the entries below `k`, then these rows. -/
def honestState (n : ℕ) (T : List (Option Bool)) (C : Circuit) (N k : ℕ) : List Sym :=
  (T.take k).map symE
    ++ encWs ((List.range' k (N + 1 - k)).map fun j => ((bitsL n j, C, T.getD j none) : WRow))

theorem gS_honestState (n : ℕ) (T : List (Option Bool)) (C : Circuit) (N : ℕ)
    (hN : 2 ^ n = N + 1) (hT : T.length = N + 1) (k : ℕ) (hk : k < N) :
    gS (honestState n T C N (k + 1)) = honestState n T C N k := by
  obtain ⟨m, hm⟩ : ∃ m, N + 1 - (k + 1) = m + 1 := ⟨N - k - 1, by omega⟩
  have hm' : N + 1 - k = m + 2 := by omega
  have r1 : List.range' k (m + 2) = k :: (k + 1) :: List.range' (k + 2) m := rfl
  have r2 : List.range' (k + 1) (m + 1) = (k + 1) :: List.range' (k + 2) m := rfl
  have hL0 : ∀ s ∈ (T.take k).map symE, s.isEnd = true := by
    intro s hs
    obtain ⟨o, _, rfl⟩ := List.mem_map.1 hs
    exact isEnd_symE o
  unfold honestState
  rw [hm, hm', r1, r2, take_succ_getD T none k (by omega)]
  simp only [List.map_append, List.map_cons, List.map_nil, encWs_cons, List.append_assoc,
    List.cons_append, List.nil_append]
  exact gS_honest_step n k C _ _ _ _ hL0 (by omega)

theorem gS_iterate_honestState (n : ℕ) (T : List (Option Bool)) (C : Circuit) (N : ℕ)
    (hN : 2 ^ n = N + 1) (hT : T.length = N + 1) : ∀ i k : ℕ, k + i ≤ N →
    gS^[i] (honestState n T C N (k + i)) = honestState n T C N k := by
  intro i
  induction i with
  | zero => intro k _; rfl
  | succ i ih =>
    intro k h
    have e : k + (i + 1) = (k + i) + 1 := by omega
    rw [Function.iterate_succ_apply, e, gS_honestState n T C N hN hT (k + i) (by omega),
      ih k (by omega)]

theorem gS_encWs_cons (w : WRow) (W : List WRow) : gS (encWs (w :: W)) = encWs (w :: W) := by
  have e : encWs (w :: W) = rowPre w ++ symE w.2.2 :: encWs W := by
    rw [encWs_cons]; simp [encW]
  rw [e]
  exact gS_row_form _ _ ⟨isEnd_rowPre w, Or.inr ⟨symE w.2.2, encWs W, rfl, isEnd_symE _⟩,
    fun h0 => absurd h0 (rowPre_ne_nil w)⟩

/-- From the last honest row, the iteration rebuilds the honest witness. -/
theorem expandS_honest (n s : ℕ) (T : List (Option Bool)) (hT : T.length = 2 ^ n) (C : Circuit) :
    expandS (List.replicate s true ++ false :: encodePartial T)
        (encW (bitsL n (2 ^ n - 1), C, T.getD (2 ^ n - 1) none))
      = encWs ((List.range (2 ^ n)).map fun j => ((bitsL n j, C, T.getD j none) : WRow)) := by
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ n = N + 1 :=
    ⟨2 ^ n - 1, by have := Nat.pos_of_ne_zero (show 2 ^ n ≠ 0 by simp); omega⟩
  rw [hN] at hT ⊢
  have hN1 : N + 1 - 1 = N := by omega
  rw [hN1]
  have hTs : T.take N ++ [T.getD N none] = T := by
    rw [← take_succ_getD T none N (by omega)]
    exact List.take_of_length_le (by omega)
  have he : entStr (encodePartial T) = (T.take N).map symE := by
    have h1 := entStr_snoc (T.take N) (T.getD N none)
    rwa [hTs] at h1
  obtain ⟨r, hr⟩ : ∃ r, (List.replicate s true ++ false :: encodePartial T).length = r + N :=
    ⟨s + N + 3, by
      simp only [List.length_append, List.length_replicate, List.length_cons,
        length_encodePartial, hT]
      omega⟩
  have h0 : (T.take N).map symE ++ encW (bitsL n N, C, T.getD N none)
      = honestState n T C N (0 + N) := by
    unfold honestState
    have h1 : N + 1 - (0 + N) = 1 := by omega
    rw [h1, Nat.zero_add]
    show _ = _ ++ encWs [((bitsL n N, C, T.getD N none) : WRow)]
    rw [encWs_singleton]
  have h1 : honestState n T C N 0
      = encWs ((List.range (N + 1)).map fun j => ((bitsL n j, C, T.getD j none) : WRow)) := by
    unfold honestState
    rw [List.take_zero, List.map_nil, List.nil_append, Nat.sub_zero, ← List.range_eq_range']
  unfold expandS
  rw [instStr_eq, he, hr, Function.iterate_add_apply, h0,
    gS_iterate_honestState n T C N hN hT N 0 (by omega), h1, List.range_succ_eq_map,
    List.map_cons]
  exact Function.iterate_fixed (gS_encWs_cons _ _) r

end PEqualNP.MetaComplexity.Helpers
