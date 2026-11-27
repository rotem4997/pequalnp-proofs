import PEqualNP.MetaComplexity.Helpers.Machines.Glue

/-!
# Helper module (proofs only): reading the bit of a string at a binary index

The index is written in binary, least significant bit first. Reading position `2 * a + b` of a
string is reading position `a` of the string of its entries at the positions of parity `b`. So
the index bits are consumed from the head, the string is halved each time, and at the end the
head of what is left is read.

The state of the iteration is one bit string: the packed raw list of the pair
(remaining index, current string), index first. One round is a finite-state transducer pass.

* `half`, `getD_half`: the pure fact.
* `stepP`, `stepP_iter`: one round on pairs, and the invariant.
* `δstep`, `stepT`, `stepT_encodePair`: one round as a transducer.
* `unpk`, `unpk_packRaw`: reading a packed raw list back.
* `cpt_lookup`: the lookup is polynomial-time computable.
-/

namespace PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.Library PEqualNP.Library.Machines

/-! ## The pure fact -/

/-- The value of an index written in binary, least significant bit first. -/
def idxVal (i : List Bool) : ℕ :=
  List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i

/-- The entries of a string at the even positions (`half false`) or at the odd positions
(`half true`). -/
def half : Bool → List Bool → List Bool
  | _, [] => []
  | false, c :: l => c :: half true l
  | true, _ :: l => half false l

/-- Position `2 * a + b` of a string is position `a` of its half of parity `b`. -/
theorem getD_half (l : List Bool) : ∀ (b : Bool) (a : ℕ),
    l.getD (2 * a + (if b = true then 1 else 0)) false = (half b l).getD a false := by
  induction l with
  | nil => intro b a; cases b <;> simp [half]
  | cons c l ih =>
    intro b a
    cases b with
    | true =>
      have e : 2 * a + (if true = true then 1 else 0) = 2 * a + 1 := by simp
      have h : half true (c :: l) = half false l := rfl
      rw [e, h, List.getD_cons_succ]
      simpa using ih false a
    | false =>
      have h : half false (c :: l) = c :: half true l := rfl
      rw [h]
      cases a with
      | zero => rfl
      | succ a =>
        have e : 2 * (a + 1) + (if false = true then 1 else 0) = (2 * a + 1) + 1 := by
          simp; omega
        rw [e, List.getD_cons_succ, List.getD_cons_succ]
        simpa using ih true a

/-- One round on pairs (remaining index, current string). -/
def stepP : List Bool × List Bool → List Bool × List Bool
  | ([], l) => ([], l)
  | (b :: i, l) => (i, half b l)

/-- After as many rounds as there are index bits, no index bit is left and the head of the
string is the bit looked up. -/
theorem stepP_iter (i : List Bool) : ∀ l : List Bool, ∃ l' : List Bool,
    stepP^[i.length] (i, l) = ([], l') ∧ l'.getD 0 false = l.getD (idxVal i) false := by
  induction i with
  | nil => intro l; exact ⟨l, rfl, rfl⟩
  | cons b i ih =>
    intro l
    obtain ⟨l', h1, h2⟩ := ih (half b l)
    refine ⟨l', ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply]; exact h1
    · rw [h2]; exact (getD_half l b (idxVal i)).symm

/-! ## One round as a transducer -/

/-- The round: the state is `none` before anything is decided, and `some k` once the first
index bit is read, where `k` tells whether the next string symbol is skipped. -/
def δstep : Option Bool → Bool ⊕ Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, Sum.inl b => (some b, none)
  | none, Sum.inr c => (none, some (Sum.inr c))
  | some k, Sum.inl c => (some k, some (Sum.inl c))
  | some k, Sum.inr c => (some (!k), if k = true then none else some (Sum.inr c))

/-- One round on raw lists. -/
def stepT (y : List (Bool ⊕ Bool)) : List (Bool ⊕ Bool) := fstRun δstep (fun _ => none) none y

theorem stepRun_none_str (l : List Bool) :
    fstRun δstep (fun _ => none) none (l.map Sum.inr) = l.map Sum.inr := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [fstRun, δstep, ih]

theorem stepRun_some_str (l : List Bool) : ∀ k : Bool,
    fstRun δstep (fun _ => none) (some k) (l.map Sum.inr) = (half k l).map Sum.inr := by
  induction l with
  | nil => intro k; cases k <;> rfl
  | cons c l ih => intro k; cases k <;> simp [fstRun, δstep, half, ih]

theorem stepRun_some_idx (k : Bool) (i l : List Bool) :
    fstRun δstep (fun _ => none) (some k) (i.map Sum.inl ++ l.map Sum.inr) =
      i.map Sum.inl ++ (half k l).map Sum.inr := by
  induction i with
  | nil => simpa using stepRun_some_str l k
  | cons b i ih => simp [fstRun, δstep, ih]

theorem stepT_encodePair (p : List Bool × List Bool) :
    stepT (encodePair p) = encodePair (stepP p) := by
  obtain ⟨i, l⟩ := p
  cases i with
  | nil => exact stepRun_none_str l
  | cons b i => exact stepRun_some_idx b i l

theorem length_fstRun_le {A B Q : Type} (δ : Q → A → Q × Option B) (q : Q) (l : List A) :
    (fstRun δ (fun _ => none) q l).length ≤ l.length := by
  induction l generalizing q with
  | nil => simp [fstRun]
  | cons a l ih =>
    have h := ih (δ q a).1
    simp only [fstRun, List.length_append, List.length_cons]
    cases (δ q a).2 <;> simp <;> omega

/-! ## Packed raw lists read back -/

/-- The reader: remember the side bit, then write the symbol. -/
def δunpk : Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, a => (some a, none)
  | some a, b => (none, some (if a = true then Sum.inr b else Sum.inl b))

/-- A bit string read as a raw list, two bits per symbol. -/
def unpk (w : List Bool) : List (Bool ⊕ Bool) := fstRun δunpk (fun _ => none) none w

theorem unpk_packRaw (l : List (Bool ⊕ Bool)) : unpk (packRaw l) = l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have h : unpk (packRaw (s :: l)) = s :: unpk (packRaw l) := by cases s <;> rfl
    rw [h, ih]

theorem length_packRaw (l : List (Bool ⊕ Bool)) : (packRaw l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have h : packRaw (s :: l) = Sum.isRight s :: Sum.elim id id s :: packRaw l := rfl
    rw [h]
    simp only [List.length_cons, ih]
    omega

theorem length_unpkRun_le (q : Option Bool) (w : List Bool) :
    2 * (fstRun δunpk (fun _ => none) q w).length ≤ w.length + (if q.isSome then 1 else 0) := by
  induction w generalizing q with
  | nil => simp [fstRun]
  | cons x w ih =>
    rcases q with _ | a
    · have h := ih (some x)
      simp only [fstRun, δunpk, Option.toList_none, List.nil_append, List.length_cons,
        Option.isSome_some, Option.isSome_none] at h ⊢
      simp at h ⊢
      omega
    · have h := ih none
      simp only [fstRun, δunpk, Option.toList_some, List.singleton_append, List.length_cons,
        Option.isSome_some, Option.isSome_none] at h ⊢
      simp at h ⊢
      omega

theorem length_unpk_le (w : List Bool) : 2 * (unpk w).length ≤ w.length := by
  simpa [unpk] using length_unpkRun_le none w

/-! ## The round on bit strings -/

/-- One round on packed bit strings. -/
def lookStep (w : List Bool) : List Bool := packRaw (stepT (unpk w))

theorem length_lookStep_le (w : List Bool) : (lookStep w).length ≤ w.length := by
  have h1 := length_fstRun_le δstep none (unpk w)
  have h2 := length_unpk_le w
  have h3 : (lookStep w).length = 2 * (stepT (unpk w)).length := length_packRaw _
  have h4 : (stepT (unpk w)).length ≤ (unpk w).length := h1
  omega

theorem cpt_packRaw :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) (fun x : List Bool => x) packRaw :=
  cpt_fstRun2 _ _ _

theorem cpt_unpk :
    ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l) unpk :=
  cpt_fstRun δunpk (fun _ => none) none

theorem cpt_lookStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) lookStep :=
  cpt_congr (cpt_comp (cpt_fstRun_comp cpt_unpk δstep (fun _ => none) none) cpt_packRaw)
    (fun _ => rfl)

theorem lookStep_iter (k : ℕ) : ∀ p : List Bool × List Bool,
    lookStep^[k] (packRaw (encodePair p)) = packRaw (encodePair (stepP^[k] p)) := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    simp only [lookStep, unpk_packRaw, stepT_encodePair]

/-! ## The read-out -/

/-- The read-out: write the bit of the first string symbol; the state tells whether it is
written. -/
def δread : Bool → Bool ⊕ Bool → Bool × Option Bool
  | false, Sum.inr c => (true, some c)
  | false, Sum.inl _ => (false, none)
  | true, _ => (true, none)

/-- At the end, write `false` when nothing was written. -/
def finRead : Bool → Option Bool
  | false => some false
  | true => none

theorem readRun_true (y : List (Bool ⊕ Bool)) : fstRun δread finRead true y = [] := by
  induction y with
  | nil => rfl
  | cons s y ih => simp [fstRun, δread, ih]

theorem readRun_str (l : List Bool) :
    fstRun δread finRead false (l.map Sum.inr) = [l.getD 0 false] := by
  cases l with
  | nil => rfl
  | cons c l => simp [fstRun, δread, readRun_true]

/-! ## The lookup -/

/-- The bit of a string at an index written in binary, least significant bit first (false when
out of range), is polynomial-time computable. -/
theorem cpt_lookup :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => p.1.getD
        (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2)
        false) := by
  obtain ⟨c⟩ := cpt_lookStep
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => lookStep^[p.2.length] p.1) :=
    Iter.iter_polyTime lookStep c 0 (fun y => by simpa using length_lookStep_le y)
  have h0 := pair_prod (cpt_comp cpt_swap cpt_pack) cpt_snd
  have h1 := cpt_comp h0 hI
  have h2 := cpt_fstRun_comp (cpt_comp h1 cpt_unpk) δread finRead false
  refine cpt_dec_of_bit (cpt_congr h2 (fun p => ?_))
  obtain ⟨l, i⟩ := p
  obtain ⟨l', e1, e2⟩ := stepP_iter i l
  show fstRun δread finRead false
    (unpk (lookStep^[i.length] (packRaw (encodePair (i, l))))) = _
  rw [lookStep_iter, e1, unpk_packRaw]
  show fstRun δread finRead false (l'.map Sum.inr) = _
  rw [readRun_str, e2]
  rfl

end PEqualNP.MetaComplexity.Helpers.Machines
