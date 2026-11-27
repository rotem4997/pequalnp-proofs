import PEqualNP.Library.Universal.Strings
import PEqualNP.Library.Universal.Prims
import PEqualNP.Library.Machines.Mul

/-!
# The string primitives are polynomial-time computable

Helper module (proofs only, no statement may use it).

Each primitive of `Strings.lean` is shown to be `ComputableInPolyTime` on plain bit strings,
either as a finite-state transducer or by combinators from the toolbox of `Prims.lean` and
`Machines/Pairing.lean`.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Transducers with one output per step -/

private def hdD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem hdD_run (l : List Bool) :
    fstRun hdD (fun _ => none) false l = [] ∧
      fstRun hdD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, hdD, ih.1, ih.2]

/-- The leading run of `true`. -/
theorem cpt_hd :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) hd :=
  fst_polyTime _ _ _ hdD (fun _ => none) true (fun s => (hdD_run s).2.symm)

private def dnD : Bool → Bool → Bool × Option Bool
  | false, true => (false, none)
  | false, false => (true, none)
  | true, b => (true, some b)

private theorem dnD_true (l : List Bool) : fstRun dnD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, dnD, ih]

private theorem dnD_false (l : List Bool) :
    fstRun dnD (fun _ => none) false l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, dnD, ih, dnD_true]

/-- Dropping through the first `false`. -/
theorem cpt_dropN :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropN :=
  fst_polyTime _ _ _ dnD (fun _ => none) false (fun s => (dnD_false s).symm)

private def tlD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, none)
  | true, b => (true, some b)

private theorem tlD_true (l : List Bool) : fstRun tlD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tlD, ih]

private theorem tlD_false (l : List Bool) : fstRun tlD (fun _ => none) false l = l.tail := by
  cases l with
  | nil => rfl
  | cons b l => simp [fstRun, tlD, tlD_true]

/-- The tail. -/
theorem cpt_tail :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.tail) :=
  fst_polyTime _ _ _ tlD (fun _ => none) false (fun s => (tlD_false s).symm)

private def tkD : Option Bool → Bool → Option Bool × Option Bool
  | none, _ => (none, none)
  | some _, true => (some true, some true)
  | some true, false => (some false, some false)
  | some false, false => (none, none)

private theorem tkD_none (l : List Bool) : fstRun tkD (fun _ => none) none l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tkD, ih]

private theorem tkD_some (b : Bool) (l : List Bool) :
    fstRun tkD (fun _ => none) (some b) l = takeLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, tkD, takeLA, ih, tkD_none]

/-- The first inner list, without its terminator. -/
theorem cpt_takeL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) takeL :=
  fst_polyTime _ _ _ tkD (fun _ => none) (some false) (fun s => (tkD_some false s).symm)

private def drD : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (none, some b)
  | some _, true => (some true, none)
  | some true, false => (some false, none)
  | some false, false => (none, none)

private theorem drD_none (l : List Bool) : fstRun drD (fun _ => none) none l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, drD, ih]

private theorem drD_some (b : Bool) (l : List Bool) :
    fstRun drD (fun _ => none) (some b) l = dropLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, drD, dropLA, ih, drD_none]

/-- Dropping the first inner list. -/
theorem cpt_dropL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropL :=
  fst_polyTime _ _ _ drD (fun _ => none) (some false) (fun s => (drD_some false s).symm)

private def hlD : Option Bool → Bool → Option Bool × Option Bool
  | none, _ => (none, none)
  | some _, true => (some true, some true)
  | some true, false => (some false, some false)
  | some false, false => (none, some false)

private theorem hlD_none (l : List Bool) : fstRun hlD (fun _ => none) none l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, hlD, ih]

private theorem hlD_some (b : Bool) (l : List Bool) :
    fstRun hlD (fun _ => none) (some b) l = headLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, hlD, headLA, ih, hlD_none]

/-- The first inner list, with its terminator. -/
theorem cpt_headL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headL :=
  fst_polyTime _ _ _ hlD (fun _ => none) (some false) (fun s => (hlD_some false s).symm)

/-- State `none`: start; `some false`: dropping the first number; `some true`: copying. -/
private def ppD : Option Bool → Bool → Option Bool × Option Bool
  | none, true => (some false, none)
  | none, false => (some true, some false)
  | some false, true => (some false, none)
  | some false, false => (some true, none)
  | some true, b => (some true, some b)

private theorem ppD_true (l : List Bool) : fstRun ppD (fun _ => none) (some true) l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ppD, ih]

private theorem ppD_false (l : List Bool) :
    fstRun ppD (fun _ => none) (some false) l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, ppD, ih, ppD_true]

private theorem ppD_none (l : List Bool) : fstRun ppD (fun _ => none) none l = popT l := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp [fstRun, ppD, popT, dropN, ppD_true, ppD_false]

/-- Popping the first number of a list. -/
theorem cpt_popT :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) popT :=
  fst_polyTime _ _ _ ppD (fun _ => none) none (fun s => (ppD_none s).symm)

private theorem blank_run (l : List Bool) :
    fstRun (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) () l = blank l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, blank] at ih ⊢; exact ih

/-- Every symbol becomes `false`. -/
theorem cpt_blank :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) blank :=
  fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) ()
    (fun s => (blank_run s).symm)

/-! ### Transducers with two outputs per step -/

private def spD : Unit → Bool → Unit × Option Bool × Option Bool
  | _, true => ((), some true, some false)
  | _, false => ((), some false, none)

private theorem spD_run (l : List Bool) : fstRun2 spD (fun _ => none) () l = spread l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, spD, spread] at ih ⊢ <;> exact ih

/-- Every `true` becomes `true, false`. -/
theorem cpt_spread :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) spread :=
  fst2_polyTime _ _ _ spD (fun _ => none) () (fun s => (spD_run s).symm)

private def buD : Unit → Bool → Unit × Option Bool × Option Bool
  | _, true => ((), some true, none)
  | _, false => ((), some true, some false)

private theorem buD_run (l : List Bool) : fstRun2 buD (fun _ => none) () l = bump l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, buD, bump] at ih ⊢ <;> exact ih

/-- Every `false` becomes `true, false`. -/
theorem cpt_bump :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bump :=
  fst2_polyTime _ _ _ buD (fun _ => none) () (fun s => (buD_run s).symm)

/-! ### Combinators -/

/-- A constant string. -/
theorem cpt_const (l : List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => l) :=
  constList_polyTime l

/-- Unary multiplication of a pair. -/
theorem cpt_mulU :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => mulU p.1 p.2) :=
  cptc mul_polyTime (fun _ => rfl)

/-- The first component of a self-delimiting pair. -/
theorem cpt_unpairB1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).1) :=
  cptc (cpt_comp cpt_unpairB cpt_fst) (fun _ => rfl)

/-- The second component of a self-delimiting pair. -/
theorem cpt_unpairB2 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) :=
  cptc (cpt_comp cpt_unpairB cpt_snd) (fun _ => rfl)

/-- Concatenation of two functions of a common argument. -/
theorem cpt_app2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => u s ++ v s) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_append) (fun _ => rfl)

/-- Self-delimiting pair of two functions of a common argument. -/
theorem cpt_pairB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_pairB) (fun _ => rfl)

/-- Unary multiplication of two functions of a common argument. -/
theorem cpt_mulU2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_mulU) (fun _ => rfl)

/-- Select, with the flag and the two branches computed from a common argument. -/
theorem cpt_sel {f a b : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
    (hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => sel (f s) (a s) (b s)) := by
  have h1 := cpt_comp (cpt_pair hf ha) cpt_ifEmpty
  have h2 := cpt_comp (cpt_pair hf hb) cpt_ifNonempty
  refine cptc (cpt_app2 h1 h2) ?_
  intro s
  by_cases h : f s = [] <;> simp [sel, h]

/-- Iterating a length-non-increasing function a number of times given by a second function. -/
theorem cpt_iterLen {g cnt arg : List Bool → List Bool}
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (hgl : ∀ s, (g s).length ≤ s.length)
    (hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt)
    (harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 0 (fun y => by simpa using hgl y)
  exact cptc (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

/-- Moving one inner list across. -/
theorem cpt_move :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) move :=
  cptc (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropL)
    (cpt_app2 cpt_unpairB2 (cpt_comp cpt_unpairB1 cpt_headL))) (fun _ => rfl)

end PEqualNP.Library.Universal
