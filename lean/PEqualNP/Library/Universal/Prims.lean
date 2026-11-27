import PEqualNP.Library.Universal.Pair
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.Transducer
import PEqualNP.Library.Machines.ConstList
import PEqualNP.Library.Machines.IterMeasure
import PEqualNP.Library.Machines.FirstGRun

/-!
# Primitive polynomial-time operations on bit strings

Helper module (proofs only, no statement may use it).

Closure properties of `PEqualNP.Library.ComputableInPolyTime` used to program polynomial-time
functions by combinators: joining a pair into a self-delimiting string and splitting it again,
conditionals on emptiness, turning a decision bit into a flag string, bounded iteration with the
count and the argument packed in one string, and pairing on any source type.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

/-! ### Small tools -/

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem fm_elim {A B C : Type} (φl : A → Option C) (φr : B → Option C) (x : List A)
    (w : List B) :
    (x.map Sum.inl ++ w.map Sum.inr).filterMap (Sum.elim φl φr) =
      x.filterMap φl ++ w.filterMap φr := by
  have h1 : ∀ x : List A, (x.map Sum.inl).filterMap (Sum.elim φl φr) = x.filterMap φl := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  have h2 : ∀ w : List B, (w.map Sum.inr).filterMap (Sum.elim φl φr) = w.filterMap φr := by
    intro w; induction w with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  rw [List.filterMap_append, h1, h2]

private theorem fm_some {A C : Type} (g : A → C) (l : List A) :
    l.filterMap (fun a => some (g a)) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem fm_none {A C : Type} (l : List A) :
    l.filterMap (fun _ : A => (none : Option C)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

/-! ### P1: joining a pair -/

/-- Joining a pair into a self-delimiting string. -/
theorem cpt_pairB :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
  have hA : ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (p.1, p.1 ++ p.2)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun b : Bool => some (Sum.inl b)) (fun _ : Bool => none))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun b : Bool => some (Sum.inr b))) ?_
    rintro ⟨x, w⟩
    simp only [encodePair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_some, fm_none]
    simp
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a : List Bool => a.map (fun _ => true) ++ [false]) := by
    refine fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true))
      (fun _ => some false) () ?_
    intro a
    induction a with
    | nil => rfl
    | cons b l ih =>
      simp only [fstRun, List.map_cons, List.cons_append, Option.toList_some] at ih ⊢
      rw [← ih]; rfl
  refine cpt_congr (cpt_comp (cpt_comp hA (cpt_first hU)) cpt_append) ?_
  rintro ⟨x, w⟩
  simp [pairB, un]

/-! ### P3: conditionals on emptiness -/

/-- Conditional on emptiness of the first component. -/
theorem cpt_ifEmpty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then p.2 else []) := by
  obtain ⟨c⟩ := constList_polyTime []
  have hI := Iter.iter_polyTime (fun _ : List Bool => ([] : List Bool)) c 0 (by simp)
  refine cpt_congr (cpt_comp cpt_swap hI) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp [Function.iterate_succ_apply']

/-- Conditional on non-emptiness of the first component. -/
theorem cpt_ifNonempty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then [] else p.2) := by
  have hneg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => if x = [] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (constList_polyTime [true])) cpt_ifEmpty
  refine cpt_congr (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp

/-! ### P4: a decision bit as a flag string -/

/-- A decision bit as a flag string: `[true]` for yes, the empty string for no. -/
theorem cpt_bitFlag {α αΓ : Type} {ea : α → List αΓ} {f : α → Bool}
    (hf : ComputableInPolyTime ea Computability.encodeBool f) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun a => if f a then [true] else []) := by
  have h : ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
      (fun b : Bool => if b then [true] else []) := by
    refine filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h

/-! ### P6: pairing on any source type -/

/-- Pairing two functions of the same argument, for any source type and input encoding. -/
theorem cpt_pairG {α αΓ : Type} [Fintype αΓ] [Inhabited αΓ] {ea : α → List αΓ}
    {f g : α → List Bool}
    (hf : ComputableInPolyTime ea (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime ea (fun x : List Bool => x) g) :
    ComputableInPolyTime ea encodePair (fun a => (f a, g a)) := by
  obtain ⟨cf⟩ := hf
  obtain ⟨cg⟩ := hg
  have s0 : ComputableInPolyTime ea (fun a : α => Gen.gpair (ea a, ea a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s)) (fun s => some (Sum.inr s)) ?_
    intro a
    simp only [Gen.gpair, fm_some]
  have s1 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, ea a))
      (fun a : α => Gen.gpair (f a, ea a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := αΓ) ea (fun x : List Bool => x) f cf
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, ea a)⟩⟩
  have s2 : ComputableInPolyTime (fun a : α => Gen.gpair (f a, ea a))
      (fun a : α => Gen.gpair (ea a, f a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : αΓ => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : αΓ => none)) ?_
    intro a
    simp only [Gen.gpair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_none, fm_none]
    simp
  have s3 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, f a))
      (fun a : α => Gen.gpair (g a, f a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := Bool) ea (fun x : List Bool => x) g cg
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, f a)⟩⟩
  have s4 : ComputableInPolyTime (fun a : α => Gen.gpair (g a, f a))
      encodePair (fun a : α => (f a, g a)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : Bool => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : Bool => none)) ?_
    intro a
    simp only [Gen.gpair, encodePair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_none, fm_none]
    simp
  exact cpt_comp (cpt_comp (cpt_comp (cpt_comp s0 s1) s2) s3) s4

/-! ### P2: splitting a self-delimiting string

The string after the first `false` is rewritten with two bits per symbol, a mark and the symbol.
One step of a length-preserving transducer marks the first unmarked symbol; it is iterated once
per leading `true`. A last transducer turns marked symbols into the first component and
unmarked ones into the second. -/

/-- Marked symbols, two bits each. -/
private def encT (u : List Bool) : List Bool := u.flatMap (fun b => [true, b])

/-- Unmarked symbols, two bits each. -/
private def encF (v : List Bool) : List Bool := v.flatMap (fun b => [false, b])

/-- Transducer for the leading `true`s. -/
private def twD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem twD_run (l : List Bool) :
    fstRun twD (fun _ => none) false l = [] ∧
      fstRun twD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, twD, ih.1, ih.2]

/-- Transducer for the part after the first `false`, written unmarked. -/
private def e0D : Bool → Bool → Bool × Option Bool × Option Bool
  | false, true => (false, none, none)
  | false, false => (true, none, none)
  | true, b => (true, some false, some b)

private theorem e0D_run_true (l : List Bool) :
    fstRun2 e0D (fun _ => none) true l = encF l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun2, e0D, encF, ih]

private theorem e0D_run_false (l : List Bool) :
    fstRun2 e0D (fun _ => none) false l = encF (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, e0D, ih, e0D_run_true]

/-- Transducer marking the first unmarked symbol. State: (done, reading the symbol). -/
private def mkD : Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (d, false), t => ((d || !t, true), some (t || !d))
  | (d, true), b => ((d, false), some b)

/-- One marking step. -/
private def mk (l : List Bool) : List Bool := fstRun mkD (fun _ => none) (false, false) l

private theorem mkD_length (q : Bool × Bool) (l : List Bool) :
    (fstRun mkD (fun _ => none) q l).length = l.length := by
  induction l generalizing q with
  | nil => rfl
  | cons b l ih => obtain ⟨d, ph⟩ := q; cases ph <;> simp [fstRun, mkD, ih]

private theorem mkD_done (v : List Bool) :
    fstRun mkD (fun _ => none) (true, false) (encF v) = encF v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, mkD, encF] at ih ⊢; exact ih

private theorem mkD_marked (u r : List Bool) :
    fstRun mkD (fun _ => none) (false, false) (encT u ++ r) =
      encT u ++ fstRun mkD (fun _ => none) (false, false) r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, mkD, encT] at ih ⊢; exact ih

private theorem mk_nil (u : List Bool) : mk (encT u ++ encF []) = encT u ++ encF [] := by
  unfold mk; rw [mkD_marked]; rfl

private theorem mk_cons (u : List Bool) (b : Bool) (v : List Bool) :
    mk (encT u ++ encF (b :: v)) = encT (u ++ [b]) ++ encF v := by
  unfold mk
  rw [mkD_marked]
  have h : fstRun mkD (fun _ => none) (false, false) (encF (b :: v)) =
      true :: b :: encF v := by
    have h' := mkD_done v
    simp [fstRun, mkD, encF] at h' ⊢
    exact h'
  rw [h]
  simp [encT]

private theorem mk_iter (k : ℕ) : ∀ u t : List Bool,
    mk^[k] (encT u ++ encF t) = encT (u ++ t.take k) ++ encF (t.drop k) := by
  induction k with
  | zero => intro u t; simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil => rw [mk_nil, ih]; simp
    | cons b t => rw [mk_cons, ih]; simp

/-- Transducer reading marks: marked symbols are tagged left, unmarked ones right. -/
private def dcD : Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, t => (some t, none)
  | some t, b => (none, some (if t then Sum.inl b else Sum.inr b))

private theorem dcD_F (v : List Bool) :
    fstRun dcD (fun _ => none) none (encF v) = v.map Sum.inr := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, dcD, encF] at ih ⊢; exact ih

private theorem dcD_T (u r : List Bool) :
    fstRun dcD (fun _ => none) none (encT u ++ r) =
      u.map Sum.inl ++ fstRun dcD (fun _ => none) none r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, dcD, encT] at ih ⊢; exact ih

/-- Reading a raw tagged list as a pair. -/
private def rawDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

private theorem rawDec_tagged (u v : List Bool) :
    rawDec (u.map Sum.inl ++ v.map Sum.inr) = (u, v) := by
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [rawDec, List.filterMap_append, h1, h2, h3, h4, List.append_nil, List.nil_append]

/-- Splitting a self-delimiting string (total on all strings). -/
theorem cpt_unpairB :
    ComputableInPolyTime (fun x : List Bool => x) encodePair unpairB := by
  have hTw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.takeWhile id) :=
    fst_polyTime _ _ _ twD (fun _ => none) true (fun s => (twD_run s).2.symm)
  have hE0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => encF (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D (fun _ => none) false (fun s => (e0D_run_false s).symm)
  have hMk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mk :=
    fst_polyTime _ _ _ mkD (fun _ => none) (false, false) (fun _ => rfl)
  obtain ⟨cMk⟩ := hMk
  have hIt := Iter.iter_polyTime mk cMk 0 (fun y => by simp [mk, mkD_length])
  have hDc : ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l)
      (fun l : List Bool => fstRun dcD (fun _ => none) none l) :=
    fst_polyTime _ _ _ dcD (fun _ => none) none (fun _ => rfl)
  have hRaw : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair rawDec := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
      (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [rawDec, encodePair, List.map_filterMap]
  refine cpt_congr (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h := mk_iter (s.takeWhile id).length [] (s.dropWhile id).tail
  have e : encT [] ++ encF (s.dropWhile id).tail = encF (s.dropWhile id).tail := rfl
  rw [e] at h
  simp only [h, List.nil_append]
  rw [dcD_T, dcD_F, rawDec_tagged]
  rfl

/-! ### P5: bounded iteration on a packed string -/

/-- Bounded iteration with the count and the argument packed in one string. -/
theorem cpt_iterB (g : List Bool → List Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y, m (g y) ≤ m y) (hgl : ∀ y, (g y).length ≤ y.length + m y)
    (ha : ∀ y, m y ≤ a * y.length + a) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => g^[(unpairB s).2.length] (unpairB s).1) := by
  obtain ⟨c⟩ := hg
  exact cpt_comp cpt_unpairB (Iter.iter_polyTime_measure g c m a hm hgl ha)

end PEqualNP.Library.Universal
