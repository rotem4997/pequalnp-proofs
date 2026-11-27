import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.IterRun
import PEqualNP.Library.Machines.Transducer
import PEqualNP.Defs.CircuitLowerBounds

/-!
# The binary code of a length, by iterated increment

Helper module (proofs only, no statement may use it).

The self-delimiting binary code `encodeNat m` (bits least significant first, each preceded by
`true`, then `false`) is incremented by a finite-state transducer (`incT`): a carry runs over
the bits, and a final new bit is written if the carry survives. Iterating the increment `|x|`
times from `encodeNat 0 = [false]` gives `encodeNat |x|`, and the bounded iteration of the
library makes this polynomial time. Composed with any polynomial-time `f`, the binary code of
`|f s|` is polynomial time.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.CircuitLowerBounds

/-! ## Increment on bits -/

/-- Increment of a bit list, least significant bit first. -/
def incBits : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incBits l

theorem bits_succ (m : ℕ) : Nat.bits (m + 1) = incBits (Nat.bits m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [incBits]
      · have h1 : 2 * k = Nat.bit false k := by simp [Nat.bit]
        have h2 : 2 * k + 1 = Nat.bit true k := by simp [Nat.bit]
        rw [h2, h1, Nat.bits_append_bit _ _ (by intro h; first | rfl | omega),
          Nat.bits_append_bit _ _ (by intro h; first | rfl | omega)]
        rfl
    · have h1 : 2 * k + 1 = Nat.bit true k := by simp [Nat.bit]
      have h2 : 2 * k + 1 + 1 = Nat.bit false (k + 1) := by simp [Nat.bit]; ring
      rw [h2, h1, Nat.bits_append_bit _ _ (by intro h; first | rfl | omega),
        Nat.bits_append_bit _ _ (by intro h; first | rfl | omega), ih (k) (by omega)]
      rfl

/-! ## The increment transducer -/

/-- States: carry before a marker, carry before a bit, copy, after the new bit. -/
inductive IncQ : Type
  | carry | carryBit | copy | done
  deriving DecidableEq

instance : Fintype IncQ :=
  Fintype.ofList [.carry, .carryBit, .copy, .done] (fun x => by cases x <;> simp)

def δinc : IncQ → Bool → IncQ × Option Bool × Option Bool
  | .carry, true => (.carryBit, some true, none)
  | .carry, false => (.done, some true, some true)
  | .carryBit, true => (.carry, some false, none)
  | .carryBit, false => (.copy, some true, none)
  | .copy, b => (.copy, some b, none)
  | .done, b => (.done, some b, none)

def finInc : IncQ → Option Bool
  | .done => some false
  | _ => none

/-- One increment of a bit string. -/
def incT (w : List Bool) : List Bool := fstRun2 δinc finInc .carry w

theorem copy_run (l : List Bool) : fstRun2 δinc finInc .copy l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun2, δinc, ih]

theorem inc_run (l : List Bool) :
    fstRun2 δinc finInc .carry (l.flatMap (fun b => [true, b]) ++ [false]) =
      (incBits l).flatMap (fun b => [true, b]) ++ [false] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a
    · simp [fstRun2, δinc, incBits, copy_run]
    · simp only [List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
      simp only [fstRun2, δinc, incBits, List.flatMap_cons, Option.toList_some,
        Option.toList_none, List.append_nil, List.cons_append, List.nil_append]
      rw [ih]

theorem incT_encodeNat (m : ℕ) : incT (encodeNat m) = encodeNat (m + 1) := by
  unfold incT encodeNat
  rw [inc_run, bits_succ]

theorem incT_iter (m : ℕ) : incT^[m] [false] = encodeNat m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, incT_encodeNat]

theorem incRun_length : ∀ (q : IncQ) (l : List Bool),
    (fstRun2 δinc finInc q l).length ≤ l.length + 2
  | .copy, l => by rw [copy_run]; omega
  | .done, [] => by simp [fstRun2, finInc]
  | .done, a :: l => by
    have := incRun_length .done l
    have e : fstRun2 δinc finInc .done (a :: l) = a :: fstRun2 δinc finInc .done l := by
      simp [fstRun2, δinc]
    rw [e]; simp only [List.length_cons]
    -- the run from `done` is the copy plus one symbol
    have h2 : ∀ l : List Bool, (fstRun2 δinc finInc .done l).length = l.length + 1 := by
      intro l
      induction l with
      | nil => rfl
      | cons b l ih => simp [fstRun2, δinc, ih]
    rw [h2]; omega
  | .carry, [] => by simp [fstRun2, finInc]
  | .carryBit, [] => by simp [fstRun2, finInc]
  | .carry, true :: l => by
    have := incRun_length .carryBit l
    simp only [fstRun2, δinc, Option.toList_some, Option.toList_none, List.append_nil,
      List.cons_append, List.nil_append, List.length_cons]
    omega
  | .carry, false :: l => by
    have h2 : ∀ l : List Bool, (fstRun2 δinc finInc .done l).length = l.length + 1 := by
      intro l
      induction l with
      | nil => rfl
      | cons b l ih => simp [fstRun2, δinc, ih]
    simp only [fstRun2, δinc, Option.toList_some, List.cons_append, List.nil_append,
      List.length_cons, h2]
    omega
  | .carryBit, true :: l => by
    have := incRun_length .carry l
    simp only [fstRun2, δinc, Option.toList_some, Option.toList_none, List.append_nil,
      List.cons_append, List.nil_append, List.length_cons]
    omega
  | .carryBit, false :: l => by
    simp only [fstRun2, δinc, Option.toList_some, Option.toList_none, List.append_nil,
      List.cons_append, List.nil_append, List.length_cons, copy_run]
    omega

/-! ## The binary code of the length -/

def δstart : Bool → Bool → Bool × Option (Bool ⊕ Bool) × Option (Bool ⊕ Bool)
  | false, b => (true, some (Sum.inl false), some (Sum.inr b))
  | true, b => (true, some (Sum.inr b), none)

def finStart : Bool → Option (Bool ⊕ Bool)
  | false => some (Sum.inl false)
  | true => none

theorem start_run_true (l : List Bool) : fstRun2 δstart finStart true l = l.map Sum.inr := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun2, δstart, ih]

theorem cpt_start : ComputableInPolyTime (fun x : List Bool => x) encodePair
    (fun x : List Bool => ([false], x)) := by
  refine fst2_polyTime _ _ _ δstart finStart false ?_
  intro x
  cases x with
  | nil => rfl
  | cons a l => simp [fstRun2, δstart, start_run_true, encodePair]

/-- The binary code of the length of a string is polynomial-time computable. -/
theorem cpt_encodeNat_length : ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => encodeNat x.length) := by
  obtain ⟨c⟩ := fst2_polyTime (fun l : List Bool => l) (fun l : List Bool => l) incT δinc finInc
    .carry (fun _ => rfl)
  have hit := Iter.iter_polyTime incT c 2 (fun y => incRun_length .carry y)
  have h := cpt_comp cpt_start hit
  have e : (fun x : List Bool => incT^[([false], x).2.length] ([false], x).1) =
      (fun x : List Bool => encodeNat x.length) := by
    funext x; exact incT_iter x.length
  rw [e] at h
  exact h

/-- The binary code of the length of a polynomial-time output is polynomial-time computable. -/
theorem cpt_encodeNat_length_comp (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => encodeNat (f s).length) :=
  cpt_comp (g := fun x : List Bool => encodeNat x.length) hf cpt_encodeNat_length

end PEqualNP.MetaComplexity.Helpers.MachinePrint
