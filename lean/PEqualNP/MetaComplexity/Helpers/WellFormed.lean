import PEqualNP.MetaComplexity.Helpers.Format

/-!
# The well-formedness transducer, and unique reading of a witness

Helper for "partial MCSP is in NP".

* `δwf`, `finWf`, `WfQ.start true true`, `wfFlags`: a transducer whose flags are all true
  exactly on the codes of nonempty lists of rows with good circuits, whose first row has only
  zero input bits, and in which every row but the last has a zero input bit
  (`wfFlags_encWs` and `wf_sound`).
* `encWs_inj`: two lists of rows with good circuits and the same code are equal.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.Library.Machines

/-! ## The transducer -/

/-- The states of the well-formedness transducer.

* `start first ok`: between rows; `first` says no row was read yet, `ok` says another row may
  start (the previous row had a zero input bit).
* `pend first hasO a`: in the input bits, holding the symbol of `a`, not yet known to be an
  input bit; `hasO` says a zero input bit was seen in this row.
* `op h`: after the operation of a gate; `r1 h`, `r2 h`: in its first, second reference.
* `z h`: after the output mark; `zr h`: in the output reference.
* `dead`: after an error.

The flag `h` says a zero input bit was seen in this row. -/
inductive WfQ where
  | start (first ok : Bool)
  | pend (first hasO a : Bool)
  | op (h : Bool)
  | r1 (h : Bool)
  | r2 (h : Bool)
  | z (h : Bool)
  | zr (h : Bool)
  | dead
  deriving DecidableEq, Fintype

/-- What the transducer does on an error. -/
def wfErr : WfQ × Option Bool × Option Bool := (WfQ.dead, some false, none)

/-- The well-formedness transducer. It writes `false` on an error and nothing otherwise. -/
def δwf : WfQ → Sym → WfQ × Option Bool × Option Bool
  | WfQ.start f true, Sym.A => (WfQ.pend f false true, none, none)
  | WfQ.start f true, Sym.O => (WfQ.pend f false false, none, none)
  | WfQ.start _ true, Sym.N => (WfQ.op false, none, none)
  | WfQ.start _ true, Sym.Z => (WfQ.z false, none, none)
  | WfQ.pend f h a, Sym.A => if f && a then wfErr else (WfQ.pend f (h || !a) true, none, none)
  | WfQ.pend f h a, Sym.O => if f && a then wfErr else (WfQ.pend f (h || !a) false, none, none)
  | WfQ.pend f h a, Sym.N => if f && a then wfErr else (WfQ.op (h || !a), none, none)
  | WfQ.pend f h a, Sym.Z => if f && a then wfErr else (WfQ.z (h || !a), none, none)
  | WfQ.pend _ h _, Sym.R => (WfQ.r1 h, none, none)
  | WfQ.op h, Sym.R => (WfQ.r1 h, none, none)
  | WfQ.r1 h, Sym.t => (WfQ.r1 h, none, none)
  | WfQ.r1 h, Sym.R => (WfQ.r2 h, none, none)
  | WfQ.r1 h, Sym.A => (WfQ.op h, none, none)
  | WfQ.r1 h, Sym.O => (WfQ.op h, none, none)
  | WfQ.r1 h, Sym.N => (WfQ.op h, none, none)
  | WfQ.r1 h, Sym.Z => (WfQ.z h, none, none)
  | WfQ.r2 h, Sym.t => (WfQ.r2 h, none, none)
  | WfQ.r2 h, Sym.A => (WfQ.op h, none, none)
  | WfQ.r2 h, Sym.O => (WfQ.op h, none, none)
  | WfQ.r2 h, Sym.N => (WfQ.op h, none, none)
  | WfQ.r2 h, Sym.Z => (WfQ.z h, none, none)
  | WfQ.z h, Sym.R => (WfQ.zr h, none, none)
  | WfQ.zr h, Sym.t => (WfQ.zr h, none, none)
  | WfQ.zr h, Sym.E0 => (WfQ.start false h, none, none)
  | WfQ.zr h, Sym.E1 => (WfQ.start false h, none, none)
  | WfQ.zr h, Sym.En => (WfQ.start false h, none, none)
  | _, _ => wfErr

/-- At the end of the input: `true` exactly between rows, after at least one row. -/
def finWf : WfQ → Option Bool
  | WfQ.start false _ => some true
  | _ => some false

/-- The well-formedness flags of a string. -/
def wfFlags (l : List Sym) : List Bool := fstRun2 δwf finWf (WfQ.start true true) l

/-! ## On coded rows -/

/-- Every row but the last has a zero input bit. -/
def NoOnes (W : List WRow) : Prop :=
  ∀ i w, W[i]? = some w → i + 1 < W.length → false ∈ w.1

theorem noOnes_tail {w : WRow} {W : List WRow} (h : NoOnes (w :: W)) : NoOnes W :=
  fun i w' hi hl => h (i + 1) w' (by simpa using hi) (by simpa using hl)

theorem noOnes_head {w : WRow} {W : List WRow} (h : NoOnes (w :: W)) (hW : W ≠ []) :
    false ∈ w.1 :=
  h 0 w rfl (by
    have := List.length_pos_iff.2 hW
    simp only [List.length_cons]; omega)

theorem noOnes_cons {w : WRow} {W : List WRow} (h1 : W ≠ [] → false ∈ w.1) (h2 : NoOnes W) :
    NoOnes (w :: W) := by
  intro i w' hi hl
  cases i with
  | zero =>
    have hw : w = w' := by simpa using hi
    subst hw
    apply h1
    intro hW
    subst hW
    simp at hl
  | succ i => exact h2 i w' (by simpa using hi) (by simpa using hl)

theorem wf_r1_ticks (h : Bool) (d : ℕ) (X : List Sym) :
    fstRun2 δwf finWf (WfQ.r1 h) (List.replicate d Sym.t ++ X)
      = fstRun2 δwf finWf (WfQ.r1 h) X := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem wf_r2_ticks (h : Bool) (d : ℕ) (X : List Sym) :
    fstRun2 δwf finWf (WfQ.r2 h) (List.replicate d Sym.t ++ X)
      = fstRun2 δwf finWf (WfQ.r2 h) X := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem wf_zr_ticks (h : Bool) (d : ℕ) (X : List Sym) :
    fstRun2 δwf finWf (WfQ.zr h) (List.replicate d Sym.t ++ X)
      = fstRun2 δwf finWf (WfQ.zr h) X := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem wf_out (h : Bool) (o : ℕ) (e : Option Bool) (rest : List Sym) :
    fstRun2 δwf finWf (WfQ.z h) (encRef o ++ symE e :: rest)
      = fstRun2 δwf finWf (WfQ.start false h) rest := by
  show fstRun2 δwf finWf (WfQ.zr h) (List.replicate o Sym.t ++ symE e :: rest) = _
  rw [wf_zr_ticks]
  rcases e with _ | _ | _ <;> rfl

/-- A state from which the part of a row after its input bits is read as from a gate
boundary, with flag `h`. -/
def Entry (h : Bool) (q : WfQ) : Prop :=
  (∀ Y, fstRun2 δwf finWf q (Sym.Z :: Y) = fstRun2 δwf finWf (WfQ.z h) Y) ∧
    ∀ s, (s = Sym.A ∨ s = Sym.O ∨ s = Sym.N) → ∀ Y,
      fstRun2 δwf finWf q (s :: Sym.R :: Y) = fstRun2 δwf finWf (WfQ.r1 h) Y

theorem entry_r1 (h : Bool) : Entry h (WfQ.r1 h) :=
  ⟨fun _ => rfl, by rintro s (rfl | rfl | rfl) Y <;> rfl⟩

theorem entry_r2 (h : Bool) : Entry h (WfQ.r2 h) :=
  ⟨fun _ => rfl, by rintro s (rfl | rfl | rfl) Y <;> rfl⟩

theorem entry_start (f : Bool) : Entry false (WfQ.start f true) :=
  ⟨fun _ => rfl, by rintro s (rfl | rfl | rfl) Y <;> rfl⟩

theorem entry_pend (f h a : Bool) (hfa : (f && a) = false) :
    Entry (h || !a) (WfQ.pend f h a) := by
  cases f <;> cases a <;> first
    | exact absurd hfa (by decide)
    | exact ⟨fun _ => rfl, by rintro s (rfl | rfl | rfl) Y <;> rfl⟩

theorem wf_gates (h : Bool) (o : ℕ) (e : Option Bool) (rest : List Sym) (gs : List Gate) :
    (∀ g ∈ gs, GoodGate g) → ∀ q, Entry h q →
      fstRun2 δwf finWf q (gs.flatMap encGate ++ Sym.Z :: (encRef o ++ symE e :: rest))
        = fstRun2 δwf finWf (WfQ.start false h) rest := by
  induction gs with
  | nil =>
    intro _ q hq
    show fstRun2 δwf finWf q (Sym.Z :: _) = _
    rw [hq.1, wf_out]
  | cons g gs ih =>
    intro hg q hq
    have hgood := hg g List.mem_cons_self
    have ih' := ih fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')
    obtain ⟨op, ins⟩ := g
    rw [List.flatMap_cons, List.append_assoc]
    rcases goodGate_inputs hgood with ⟨a, ha⟩ | ⟨a, b, ha⟩
    · simp only at ha
      subst ha
      rw [encGate_one, hq.2 _ (opSym_cases op), wf_r1_ticks]
      exact ih' _ (entry_r1 h)
    · simp only at ha
      subst ha
      rw [encGate_two, hq.2 _ (opSym_cases op), wf_r1_ticks]
      show fstRun2 δwf finWf (WfQ.r2 h) (List.replicate b Sym.t ++ _) = _
      rw [wf_r2_ticks]
      exact ih' _ (entry_r2 h)

theorem wf_body (h : Bool) (C : Circuit) (hC : GoodC C) (e : Option Bool) (rest : List Sym)
    (q : WfQ) (hq : Entry h q) :
    fstRun2 δwf finWf q (encBody C ++ symE e :: rest)
      = fstRun2 δwf finWf (WfQ.start false h) rest := by
  rw [encBody_append]
  exact wf_gates h _ e rest _ hC q hq

theorem wf_pend (C : Circuit) (hC : GoodC C) (e : Option Bool) (rest : List Sym)
    (bs : List Bool) : ∀ (f h a : Bool), (f && a) = false → (f = true → ∀ b ∈ bs, b = false) →
      fstRun2 δwf finWf (WfQ.pend f h a) (bs.map bsym ++ (encBody C ++ symE e :: rest))
        = fstRun2 δwf finWf (WfQ.start false (h || !a || bs.any (!·))) rest := by
  induction bs with
  | nil =>
    intro f h a hfa _
    have e0 : (h || !a || ([] : List Bool).any (!·)) = (h || !a) := by simp
    rw [e0]
    exact wf_body _ C hC e rest _ (entry_pend f h a hfa)
  | cons b bs ih =>
    intro f h a hfa hall
    have step : fstRun2 δwf finWf (WfQ.pend f h a)
          ((b :: bs).map bsym ++ (encBody C ++ symE e :: rest))
        = fstRun2 δwf finWf (WfQ.pend f (h || !a) b)
            (bs.map bsym ++ (encBody C ++ symE e :: rest)) := by
      cases f <;> cases a <;> cases b <;> first | rfl | exact absurd hfa (by decide)
    have hfb : (f && b) = false := by
      cases f
      · rfl
      · simp [hall rfl b List.mem_cons_self]
    have e1 : (h || !a || !b || bs.any (!·)) = (h || !a || (b :: bs).any (!·)) := by
      simp [Bool.or_assoc]
    rw [step, ih f (h || !a) b hfb fun hf b' hb' => hall hf b' (List.mem_cons_of_mem _ hb'), e1]

theorem wf_row (w : WRow) (hw : GoodC w.2.1) (f : Bool) (hf : f = true → ∀ b ∈ w.1, b = false)
    (rest : List Sym) :
    fstRun2 δwf finWf (WfQ.start f true) (encW w ++ rest)
      = fstRun2 δwf finWf (WfQ.start false (w.1.any (!·))) rest := by
  obtain ⟨bs, C, e⟩ := w
  rw [encW_append]
  show fstRun2 δwf finWf (WfQ.start f true) (bs.map bsym ++ (encBody C ++ symE e :: rest))
    = fstRun2 δwf finWf (WfQ.start false (bs.any (!·))) rest
  cases bs with
  | nil => exact wf_body _ C hw e rest _ (entry_start f)
  | cons b bs =>
    have step : fstRun2 δwf finWf (WfQ.start f true)
          ((b :: bs).map bsym ++ (encBody C ++ symE e :: rest))
        = fstRun2 δwf finWf (WfQ.pend f false b)
            (bs.map bsym ++ (encBody C ++ symE e :: rest)) := by
      cases b <;> rfl
    have hfb : (f && b) = false := by
      cases f
      · rfl
      · simp [hf rfl b List.mem_cons_self]
    have e1 : (false || !b || bs.any (!·)) = (b :: bs).any (!·) := by simp
    rw [step, wf_pend C hw e rest bs f false b hfb
      fun hf' b' hb' => hf hf' b' (List.mem_cons_of_mem _ hb'), e1]

theorem wf_rows (W : List WRow) : ∀ (f ok : Bool), (W ≠ [] → ok = true) →
    (f = true → ∃ w W', W = w :: W' ∧ ∀ b ∈ w.1, b = false) → (∀ w ∈ W, GoodC w.2.1) →
    NoOnes W → fstRun2 δwf finWf (WfQ.start f ok) (encWs W) = [true] := by
  induction W with
  | nil =>
    intro f ok _ hf _ _
    cases f
    · rfl
    · obtain ⟨w, W', h, _⟩ := hf rfl
      exact absurd h (by simp)
  | cons w W ih =>
    intro f ok hok hf hg hn
    rw [hok (by simp), encWs_cons, wf_row w (hg w List.mem_cons_self) f (by
      intro hf'
      obtain ⟨w', W', h, hb⟩ := hf hf'
      rw [(List.cons.inj h).1]
      exact hb)]
    apply ih
    · intro hW
      have := noOnes_head hn hW
      simp only [List.any_eq_true, Bool.not_eq_true']
      exact ⟨false, this, rfl⟩
    · intro h; exact absurd h (by decide)
    · exact fun w' hw' => hg w' (List.mem_cons_of_mem _ hw')
    · exact noOnes_tail hn

/-- The flags of a well-formed witness are all true. -/
theorem wfFlags_encWs (w : WRow) (W : List WRow) (h0 : ∀ b ∈ w.1, b = false)
    (hg : ∀ w' ∈ w :: W, GoodC w'.2.1) (hn : NoOnes (w :: W)) :
    wfFlags (encWs (w :: W)) = [true] :=
  wf_rows (w :: W) true true (fun _ => rfl) (fun _ => ⟨w, W, rfl, h0⟩) hg hn

/-! ## Reading a string whose flags are all true -/

/-- The flags written from state `q` on `l` are all true. -/
def Acc (q : WfQ) (l : List Sym) : Prop := (fstRun2 δwf finWf q l).all id = true

theorem acc_step {q : WfQ} {s : Sym} {l : List Sym} (h : Acc q (s :: l)) :
    (δwf q s).2.1 ≠ some false ∧ Acc (δwf q s).1 l := by
  have h' : ((δwf q s).2.1.toList ++ (δwf q s).2.2.toList
      ++ fstRun2 δwf finWf (δwf q s).1 l).all id = true := h
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true] at h'
  refine ⟨?_, h'.2⟩
  intro hc
  rw [hc] at h'
  exact absurd h'.1.1 (by decide)

/-- The rest of a row from a gate boundary on, then a string accepted between rows. -/
def TailOK (h : Bool) (l : List Sym) : Prop :=
  ∃ (gs : List Gate) (o : ℕ) (e : Option Bool) (rest : List Sym),
    (∀ g ∈ gs, GoodGate g) ∧
      l = gs.flatMap encGate ++ Sym.Z :: (encRef o ++ symE e :: rest) ∧
      Acc (WfQ.start false h) rest

theorem acc_zr (h : Bool) (l : List Sym) : Acc (WfQ.zr h) l →
    ∃ d e rest, l = List.replicate d Sym.t ++ symE e :: rest ∧ Acc (WfQ.start false h) rest := by
  induction l with
  | nil => intro hl; exact absurd hl Bool.false_ne_true
  | cons s l ih =>
    intro hl
    cases s with
    | t =>
      obtain ⟨d, e, rest, rfl, hr⟩ := ih (acc_step hl).2
      exact ⟨d + 1, e, rest, rfl, hr⟩
    | E0 => exact ⟨0, some false, l, rfl, (acc_step hl).2⟩
    | E1 => exact ⟨0, some true, l, rfl, (acc_step hl).2⟩
    | En => exact ⟨0, none, l, rfl, (acc_step hl).2⟩
    | _ => exact absurd rfl (acc_step hl).1

theorem tailOK_z (h : Bool) (l : List Sym) (hl : Acc (WfQ.z h) l) : TailOK h (Sym.Z :: l) := by
  cases l with
  | nil => exact absurd hl Bool.false_ne_true
  | cons s l =>
    cases s with
    | R =>
      obtain ⟨d, e, rest, rfl, hr⟩ := acc_zr h l (acc_step hl).2
      exact ⟨[], d, e, rest, by simp, rfl, hr⟩
    | _ => exact absurd rfl (acc_step hl).1

theorem tailOK_gate (h : Bool) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (ins : List ℕ)
    (hins : ins.length = 1 ∨ ins.length = 2) (l : List Sym) (ht : TailOK h l) :
    TailOK h (opSym op :: (ins.flatMap encRef ++ l)) := by
  obtain ⟨gs, o, e, rest, hg, rfl, hr⟩ := ht
  refine ⟨⟨op, ins⟩ :: gs, o, e, rest, ?_, ?_, hr⟩
  · intro g hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact ⟨hop, hins⟩
    · exact hg g hg'
  · simp [encGate]

/-- What the three states inside a gate accept. -/
theorem acc_gate (l : List Sym) : ∀ h : Bool,
    (Acc (WfQ.op h) l → ∃ (ins : List ℕ) (l' : List Sym), (ins.length = 1 ∨ ins.length = 2) ∧
        l = ins.flatMap encRef ++ l' ∧ TailOK h l') ∧
    (Acc (WfQ.r1 h) l → ∃ d l', l = List.replicate d Sym.t ++ l' ∧
        (TailOK h l' ∨ ∃ d2 l'', l' = encRef d2 ++ l'' ∧ TailOK h l'')) ∧
    (Acc (WfQ.r2 h) l → ∃ d l', l = List.replicate d Sym.t ++ l' ∧ TailOK h l') := by
  induction l with
  | nil =>
    intro h
    exact ⟨fun hl => absurd hl Bool.false_ne_true, fun hl => absurd hl Bool.false_ne_true,
      fun hl => absurd hl Bool.false_ne_true⟩
  | cons s l ih =>
    intro h
    obtain ⟨ihop, ih1, ih2⟩ := ih h
    have viaOp : ∀ op : GateOp, (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
        Acc (WfQ.op h) l → TailOK h (opSym op :: l) := by
      intro op hop hl
      obtain ⟨ins, l', hins, rfl, ht⟩ := ihop hl
      exact tailOK_gate h op hop ins hins l' ht
    refine ⟨?_, ?_, ?_⟩
    · intro hl
      cases s with
      | R =>
        obtain ⟨d, l', rfl, ht | ⟨d2, l'', rfl, ht⟩⟩ := ih1 (acc_step hl).2
        · exact ⟨[d], l', Or.inl rfl, by simp [encRef], ht⟩
        · exact ⟨[d, d2], l'', Or.inr rfl, by simp [encRef], ht⟩
      | _ => exact absurd rfl (acc_step hl).1
    · intro hl
      cases s with
      | t =>
        obtain ⟨d, l', rfl, ht⟩ := ih1 (acc_step hl).2
        exact ⟨d + 1, l', rfl, ht⟩
      | R =>
        obtain ⟨d, l', rfl, ht⟩ := ih2 (acc_step hl).2
        exact ⟨0, _, rfl, Or.inr ⟨d, l', rfl, ht⟩⟩
      | A => exact ⟨0, _, rfl, Or.inl (viaOp GateOp.and (Or.inl rfl) (acc_step hl).2)⟩
      | O => exact ⟨0, _, rfl, Or.inl (viaOp GateOp.or (Or.inr (Or.inl rfl)) (acc_step hl).2)⟩
      | N => exact ⟨0, _, rfl, Or.inl (viaOp GateOp.not (Or.inr (Or.inr rfl)) (acc_step hl).2)⟩
      | Z => exact ⟨0, _, rfl, Or.inl (tailOK_z h l (acc_step hl).2)⟩
      | _ => exact absurd rfl (acc_step hl).1
    · intro hl
      cases s with
      | t =>
        obtain ⟨d, l', rfl, ht⟩ := ih2 (acc_step hl).2
        exact ⟨d + 1, l', rfl, ht⟩
      | A => exact ⟨0, _, rfl, viaOp GateOp.and (Or.inl rfl) (acc_step hl).2⟩
      | O => exact ⟨0, _, rfl, viaOp GateOp.or (Or.inr (Or.inl rfl)) (acc_step hl).2⟩
      | N => exact ⟨0, _, rfl, viaOp GateOp.not (Or.inr (Or.inr rfl)) (acc_step hl).2⟩
      | Z => exact ⟨0, _, rfl, tailOK_z h l (acc_step hl).2⟩
      | _ => exact absurd rfl (acc_step hl).1

theorem tailOK_op (h : Bool) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List Sym)
    (hl : Acc (WfQ.op h) l) : TailOK h (opSym op :: l) := by
  obtain ⟨ins, l', hins, rfl, ht⟩ := (acc_gate l h).1 hl
  exact tailOK_gate h op hop ins hins l' ht

/-- The operation of an input bit symbol read as the start of a gate. -/
def bop : Bool → GateOp
  | true => GateOp.and
  | false => GateOp.or

theorem bop_std (a : Bool) : bop a = GateOp.and ∨ bop a = GateOp.or ∨ bop a = GateOp.not := by
  cases a
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem opSym_bop (a : Bool) : opSym (bop a) = bsym a := by cases a <;> rfl

/-- What the state holding an input bit symbol accepts. -/
theorem acc_pend (l : List Sym) : ∀ f h a : Bool, Acc (WfQ.pend f h a) l →
    ∃ (bs : List Bool) (l' : List Sym) (h' : Bool), bsym a :: l = bs.map bsym ++ l' ∧
      (f = true → ∀ b ∈ bs, b = false) ∧ h' = (h || bs.any (!·)) ∧ TailOK h' l' := by
  induction l with
  | nil => intro f h a hl; exact absurd hl Bool.false_ne_true
  | cons s l ih =>
    intro f h a hl
    have bit : ∀ c : Bool, s = bsym c → (f && a) = false → Acc (WfQ.pend f (h || !a) c) l →
        ∃ (bs : List Bool) (l' : List Sym) (h' : Bool),
          bsym a :: s :: l = bs.map bsym ++ l' ∧
          (f = true → ∀ b ∈ bs, b = false) ∧ h' = (h || bs.any (!·)) ∧ TailOK h' l' := by
      intro c hs hfa hl'
      obtain ⟨bs, l', h', e1, e2, e3, ht⟩ := ih f (h || !a) c hl'
      refine ⟨a :: bs, l', h', ?_, ?_, ?_, ht⟩
      · rw [hs, e1]; rfl
      · intro hf b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · rw [hf] at hfa; simpa using hfa
        · exact e2 hf b hb
      · rw [e3]; simp [Bool.or_assoc]
    have one : (f && a) = false → ∀ l' : List Sym, s :: l = l' → TailOK (h || !a) l' →
        ∃ (bs : List Bool) (l' : List Sym) (h' : Bool),
          bsym a :: s :: l = bs.map bsym ++ l' ∧
          (f = true → ∀ b ∈ bs, b = false) ∧ h' = (h || bs.any (!·)) ∧ TailOK h' l' := by
      intro hfa l' hl' ht
      refine ⟨[a], l', h || !a, by rw [hl']; rfl, ?_, by simp, ht⟩
      intro hf b hb
      rw [List.mem_singleton.1 hb]
      rw [hf] at hfa; simpa using hfa
    cases s with
    | A =>
      have : (f && a) = false ∧ Acc (WfQ.pend f (h || !a) true) l := by
        cases f <;> cases a <;>
          first | exact absurd rfl (acc_step hl).1 | exact ⟨rfl, (acc_step hl).2⟩
      exact bit true rfl this.1 this.2
    | O =>
      have : (f && a) = false ∧ Acc (WfQ.pend f (h || !a) false) l := by
        cases f <;> cases a <;>
          first | exact absurd rfl (acc_step hl).1 | exact ⟨rfl, (acc_step hl).2⟩
      exact bit false rfl this.1 this.2
    | N =>
      have : (f && a) = false ∧ Acc (WfQ.op (h || !a)) l := by
        cases f <;> cases a <;>
          first | exact absurd rfl (acc_step hl).1 | exact ⟨rfl, (acc_step hl).2⟩
      exact one this.1 _ rfl (tailOK_op _ GateOp.not (Or.inr (Or.inr rfl)) l this.2)
    | Z =>
      have : (f && a) = false ∧ Acc (WfQ.z (h || !a)) l := by
        cases f <;> cases a <;>
          first | exact absurd rfl (acc_step hl).1 | exact ⟨rfl, (acc_step hl).2⟩
      exact one this.1 _ rfl (tailOK_z _ l this.2)
    | R =>
      have hl' : Acc (WfQ.r1 h) l := (acc_step hl).2
      obtain ⟨d, l', rfl, ht | ⟨d2, l'', rfl, ht⟩⟩ := (acc_gate l h).2.1 hl'
      · refine ⟨[], _, h, rfl, by simp, by simp, ?_⟩
        have := tailOK_gate h (bop a) (bop_std a) [d] (Or.inl rfl) l' ht
        rw [opSym_bop] at this
        simpa [encRef] using this
      · refine ⟨[], _, h, rfl, by simp, by simp, ?_⟩
        have := tailOK_gate h (bop a) (bop_std a) [d, d2] (Or.inr rfl) l'' ht
        rw [opSym_bop] at this
        simpa [encRef] using this
    | _ => exact absurd rfl (acc_step hl).1

/-- What the state between rows accepts when a symbol follows: one row, then the rest. -/
theorem acc_start (f ok : Bool) (s : Sym) (l : List Sym) (hl : Acc (WfQ.start f ok) (s :: l)) :
    ok = true ∧ ∃ (bs : List Bool) (l' : List Sym), s :: l = bs.map bsym ++ l' ∧
      (f = true → ∀ b ∈ bs, b = false) ∧ TailOK (bs.any (!·)) l' := by
  cases ok with
  | false => cases s <;> exact absurd rfl (acc_step hl).1
  | true =>
    refine ⟨rfl, ?_⟩
    cases s with
    | A =>
      obtain ⟨bs, l', h', e1, e2, e3, ht⟩ := acc_pend l f false true (acc_step hl).2
      refine ⟨bs, l', e1, e2, ?_⟩
      rw [e3, Bool.false_or] at ht
      exact ht
    | O =>
      obtain ⟨bs, l', h', e1, e2, e3, ht⟩ := acc_pend l f false false (acc_step hl).2
      refine ⟨bs, l', e1, e2, ?_⟩
      rw [e3, Bool.false_or] at ht
      exact ht
    | N =>
      exact ⟨[], _, rfl, by simp,
        tailOK_op false GateOp.not (Or.inr (Or.inr rfl)) l (acc_step hl).2⟩
    | Z => exact ⟨[], _, rfl, by simp, tailOK_z false l (acc_step hl).2⟩
    | _ => exact absurd rfl (acc_step hl).1

theorem acc_rows : ∀ (n : ℕ) (l : List Sym), l.length ≤ n → ∀ f ok : Bool,
    Acc (WfQ.start f ok) l →
      (l = [] → f = false) ∧ ∃ W : List WRow, l = encWs W ∧ (∀ w ∈ W, GoodC w.2.1) ∧
        (f = true → ∀ w W', W = w :: W' → ∀ b ∈ w.1, b = false) ∧
        (W ≠ [] → ok = true) ∧ NoOnes W := by
  intro n
  induction n with
  | zero =>
    intro l hl f ok hacc
    have hl0 : l = [] := List.length_eq_zero_iff.1 (by omega)
    subst hl0
    refine ⟨fun _ => ?_, [], rfl, by simp, by simp, by simp, ?_⟩
    · cases f
      · rfl
      · exact absurd hacc Bool.false_ne_true
    · intro i w hi; simp at hi
  | succ n ih =>
    intro l hl f ok hacc
    cases l with
    | nil =>
      refine ⟨fun _ => ?_, [], rfl, by simp, by simp, by simp, ?_⟩
      · cases f
        · rfl
        · exact absurd hacc Bool.false_ne_true
      · intro i w hi; simp at hi
    | cons s l =>
      refine ⟨fun h => absurd h (by simp), ?_⟩
      obtain ⟨hok, bs, l', e1, hbs, gs, o, e, rest, hg, rfl, hr⟩ := acc_start f ok s l hacc
      have hlen : rest.length ≤ n := by
        have := congrArg List.length e1
        simp only [List.length_cons, List.length_append, List.length_map] at this hl
        omega
      obtain ⟨_, W, rfl, hW, _, hWok, hWn⟩ := ih rest hlen false (bs.any (!·)) hr
      refine ⟨(bs, ⟨gs, o⟩, e) :: W, ?_, ?_, ?_, fun _ => hok, ?_⟩
      · rw [e1, encWs_cons, encW_append, encBody_append]
      · intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hg
        · exact hW w hw
      · intro hf w W' hw
        rw [← (List.cons.inj hw).1]
        exact hbs hf
      · apply noOnes_cons _ hWn
        intro hne
        have := hWok hne
        simp only [List.any_eq_true, Bool.not_eq_true'] at this
        obtain ⟨b, hb, rfl⟩ := this
        exact hb

/-- A string whose well-formedness flags are all true is the code of a nonempty list of rows
with good circuits; the input bits of the first row are all zero, and every row but the last
has a zero input bit. -/
theorem wf_sound (u : List Sym) (h : (wfFlags u).all id = true) :
    ∃ (w : WRow) (W : List WRow), u = encWs (w :: W) ∧ (∀ w' ∈ w :: W, GoodC w'.2.1) ∧
      (∀ b ∈ w.1, b = false) ∧ NoOnes (w :: W) := by
  obtain ⟨h0, W, rfl, hg, hf, _, hn⟩ := acc_rows u.length u le_rfl true true h
  cases W with
  | nil => exact absurd (h0 rfl) (by decide)
  | cons w W => exact ⟨w, W, rfl, hg, hf rfl w W rfl, hn⟩

/-! ## Unique reading -/

theorem ticks_inj (a : ℕ) : ∀ (a' : ℕ) (Q Q' : List Sym), Guard Q → Guard Q' →
    List.replicate a Sym.t ++ Q = List.replicate a' Sym.t ++ Q' → a = a' ∧ Q = Q' := by
  induction a with
  | zero =>
    intro a' Q Q' hQ hQ' h
    cases a' with
    | zero => exact ⟨rfl, h⟩
    | succ a' =>
      obtain ⟨s, r, rfl, hs⟩ := hQ
      exact absurd (List.cons.inj h).1 hs
  | succ a ih =>
    intro a' Q Q' hQ hQ' h
    cases a' with
    | zero =>
      obtain ⟨s, r, rfl, hs⟩ := hQ'
      exact absurd (List.cons.inj h).1.symm hs
    | succ a' =>
      obtain ⟨e1, e2⟩ := ih a' Q Q' hQ hQ' (List.cons.inj h).2
      exact ⟨by rw [e1], e2⟩

/-- A string whose first symbol exists and is neither a reference mark nor a tick. -/
def NRT (P : List Sym) : Prop := ∃ s r, P = s :: r ∧ s ≠ Sym.R ∧ s ≠ Sym.t

theorem guard_refs (ins : List ℕ) (P : List Sym) (hP : NRT P) :
    Guard (ins.flatMap encRef ++ P) := by
  cases ins with
  | nil =>
    obtain ⟨s, r, rfl, _, hs⟩ := hP
    exact ⟨s, r, rfl, hs⟩
  | cons a ins => exact ⟨Sym.R, _, rfl, by decide⟩

theorem refs_inj (ins : List ℕ) : ∀ (ins' : List ℕ) (P P' : List Sym), NRT P → NRT P' →
    ins.flatMap encRef ++ P = ins'.flatMap encRef ++ P' → ins = ins' ∧ P = P' := by
  induction ins with
  | nil =>
    intro ins' P P' hP hP' h
    cases ins' with
    | nil => exact ⟨rfl, h⟩
    | cons a' ins' =>
      obtain ⟨s, r, rfl, hs, _⟩ := hP
      exact absurd (List.cons.inj h).1 hs
  | cons a ins ih =>
    intro ins' P P' hP hP' h
    cases ins' with
    | nil =>
      obtain ⟨s, r, rfl, hs, _⟩ := hP'
      exact absurd (List.cons.inj h).1.symm hs
    | cons a' ins' =>
      rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc] at h
      obtain ⟨e1, e2⟩ := ticks_inj a a' _ _ (guard_refs ins P hP) (guard_refs ins' P' hP')
        (List.cons.inj h).2
      obtain ⟨e3, e4⟩ := ih ins' P P' hP hP' e2
      exact ⟨by rw [e1, e3], e4⟩

theorem nrt_gates (gs : List Gate) (Y : List Sym) : NRT (gs.flatMap encGate ++ Sym.Z :: Y) := by
  cases gs with
  | nil => exact ⟨Sym.Z, Y, rfl, by decide, by decide⟩
  | cons g gs =>
    refine ⟨opSym g.op, _, rfl, ?_, ?_⟩ <;> cases g.op <;> simp [opSym]

theorem opSym_inj {op op' : GateOp}
    (h : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (h' : op' = GateOp.and ∨ op' = GateOp.or ∨ op' = GateOp.not) (e : opSym op = opSym op') :
    op = op' := by
  rcases h with rfl | rfl | rfl <;> rcases h' with rfl | rfl | rfl <;>
    first | rfl | exact absurd e (by decide)

theorem gates_inj (gs : List Gate) : ∀ (gs' : List Gate) (Y Y' : List Sym),
    (∀ g ∈ gs, GoodGate g) → (∀ g ∈ gs', GoodGate g) →
    gs.flatMap encGate ++ Sym.Z :: Y = gs'.flatMap encGate ++ Sym.Z :: Y' →
      gs = gs' ∧ Y = Y' := by
  induction gs with
  | nil =>
    intro gs' Y Y' _ _ h
    cases gs' with
    | nil => exact ⟨rfl, (List.cons.inj h).2⟩
    | cons g' gs' =>
      have := (List.cons.inj h).1
      rcases opSym_cases g'.op with e | e | e <;> rw [e] at this <;> exact absurd this (by decide)
  | cons g gs ih =>
    intro gs' Y Y' hg hg' h
    cases gs' with
    | nil =>
      have := (List.cons.inj h).1
      rcases opSym_cases g.op with e | e | e <;> rw [e] at this <;> exact absurd this (by decide)
    | cons g' gs' =>
      obtain ⟨op, ins⟩ := g
      obtain ⟨op', ins'⟩ := g'
      have hgood := hg _ List.mem_cons_self
      have hgood' := hg' _ List.mem_cons_self
      rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc] at h
      have h1 : opSym op = opSym op' := (List.cons.inj h).1
      have h2 : ins.flatMap encRef ++ (gs.flatMap encGate ++ Sym.Z :: Y)
          = ins'.flatMap encRef ++ (gs'.flatMap encGate ++ Sym.Z :: Y') := (List.cons.inj h).2
      obtain ⟨e1, e2⟩ := refs_inj ins ins' _ _ (nrt_gates gs Y) (nrt_gates gs' Y') h2
      obtain ⟨e3, e4⟩ := ih gs' Y Y' (fun g hg0 => hg g (List.mem_cons_of_mem _ hg0))
        (fun g hg0 => hg' g (List.mem_cons_of_mem _ hg0)) e2
      have e0 : op = op' := opSym_inj hgood.1 hgood'.1 h1
      exact ⟨by rw [e0, e1, e3], e4⟩

theorem symE_inj {e e' : Option Bool} (h : symE e = symE e') : e = e' := by
  rcases e with _ | _ | _ <;> rcases e' with _ | _ | _ <;>
    first | rfl | exact absurd h (by decide)

theorem body_inj (C C' : Circuit) (e e' : Option Bool) (r r' : List Sym) (hC : GoodC C)
    (hC' : GoodC C') (h : encBody C ++ symE e :: r = encBody C' ++ symE e' :: r') :
    C = C' ∧ e = e' ∧ r = r' := by
  rw [encBody_append, encBody_append] at h
  obtain ⟨e1, e2⟩ := gates_inj _ _ _ _ hC hC' h
  obtain ⟨e3, e4⟩ := ticks_inj _ _ _ _ (guard_end e r) (guard_end e' r') (List.cons.inj e2).2
  obtain ⟨gs, o⟩ := C
  obtain ⟨gs', o'⟩ := C'
  simp only at e1 e3
  exact ⟨by rw [e1, e3], symE_inj (List.cons.inj e4).1, (List.cons.inj e4).2⟩

theorem bits_ne_body (b : Bool) (bs : List Bool) (X X' : List Sym) (hX : BodyStart X)
    (hX' : BodyStart X') : X ≠ bsym b :: (bs.map bsym ++ X') := by
  intro h
  rcases hX with ⟨r, rfl⟩ | ⟨s, r, rfl, _⟩
  · cases b <;> exact absurd (List.cons.inj h).1 (by decide)
  · have h2 := (List.cons.inj h).2
    cases bs with
    | nil =>
      rcases hX' with ⟨r', rfl⟩ | ⟨s', r', rfl, hs'⟩
      · exact absurd (List.cons.inj h2).1 (by decide)
      · have := (List.cons.inj h2).1
        rcases hs' with rfl | rfl | rfl <;> exact absurd this (by decide)
    | cons c bs => cases c <;> exact absurd (List.cons.inj h2).1 (by decide)

theorem bsym_inj {b b' : Bool} (h : bsym b = bsym b') : b = b' := by
  cases b <;> cases b' <;> first | rfl | exact absurd h (by decide)

theorem bits_inj (bs : List Bool) : ∀ (bs' : List Bool) (X X' : List Sym), BodyStart X →
    BodyStart X' → bs.map bsym ++ X = bs'.map bsym ++ X' → bs = bs' ∧ X = X' := by
  induction bs with
  | nil =>
    intro bs' X X' hX hX' h
    cases bs' with
    | nil => exact ⟨rfl, h⟩
    | cons b' bs' => exact absurd h (bits_ne_body b' bs' X X' hX hX')
  | cons b bs ih =>
    intro bs' X X' hX hX' h
    cases bs' with
    | nil => exact absurd h.symm (bits_ne_body b bs X' X hX' hX)
    | cons b' bs' =>
      obtain ⟨e1, e2⟩ := ih bs' X X' hX hX' (List.cons.inj h).2
      exact ⟨by rw [bsym_inj (List.cons.inj h).1, e1], e2⟩

theorem encW_inj (w w' : WRow) (r r' : List Sym) (hw : GoodC w.2.1) (hw' : GoodC w'.2.1)
    (h : encW w ++ r = encW w' ++ r') : w = w' ∧ r = r' := by
  obtain ⟨bs, C, e⟩ := w
  obtain ⟨bs', C', e'⟩ := w'
  rw [encW_append, encW_append] at h
  obtain ⟨e1, e2⟩ := bits_inj bs bs' _ _ (bodyStart_encBody C hw _) (bodyStart_encBody C' hw' _) h
  obtain ⟨e3, e4, e5⟩ := body_inj C C' e e' r r' hw hw' e2
  exact ⟨by rw [e1, e3, e4], e5⟩

theorem encW_ne_nil (w : WRow) (r : List Sym) : encW w ++ r ≠ [] := by
  simp [encW]

/-- Two lists of rows with good circuits and the same code are equal. -/
theorem encWs_inj (W : List WRow) : ∀ W' : List WRow, (∀ w ∈ W, GoodC w.2.1) →
    (∀ w ∈ W', GoodC w.2.1) → encWs W = encWs W' → W = W' := by
  induction W with
  | nil =>
    intro W' _ _ h
    cases W' with
    | nil => rfl
    | cons w' W' => exact absurd h.symm (encW_ne_nil w' _)
  | cons w W ih =>
    intro W' hW hW' h
    cases W' with
    | nil => exact absurd h (encW_ne_nil w _)
    | cons w' W' =>
      obtain ⟨e1, e2⟩ := encW_inj w w' _ _ (hW w List.mem_cons_self) (hW' w' List.mem_cons_self) h
      rw [e1, ih W' (fun w hw => hW w (List.mem_cons_of_mem _ hw))
        (fun w hw => hW' w (List.mem_cons_of_mem _ hw)) e2]

end PEqualNP.MetaComplexity.Helpers
