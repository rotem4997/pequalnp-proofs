import PEqualNP.MetaComplexity.Helpers.MachinePrintBin
import PEqualNP.MetaComplexity.Helpers.MachinePrintRel

/-!
# The repair of the output wire of a circuit code with no gate

Helper module (proofs only, no statement may use it).

On the code `encodeLgp (n, C)` a finite-state transducer copies the unary `n`; if the gate list
is empty (the next symbol is `false`) and `n` is positive it increments the binary output
index that follows; otherwise it copies. So `fixf` is polynomial time on codes.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive FQ : Type
  | hd0 | hd1 | af0 | af1 | cp | inc (q : IncQ)
  deriving DecidableEq

instance : Fintype FQ :=
  Fintype.ofList [.hd0, .hd1, .af0, .af1, .cp, .inc .carry, .inc .carryBit, .inc .copy,
    .inc .done] (fun x => by cases x with | inc q => cases q <;> simp | _ => simp)

def δfix : FQ → Bool → FQ × Option Bool × Option Bool
  | .hd0, true => (.hd1, some true, none)
  | .hd0, false => (.af0, some false, none)
  | .hd1, true => (.hd1, some true, none)
  | .hd1, false => (.af1, some false, none)
  | .af0, b => (.cp, some b, none)
  | .af1, true => (.cp, some true, none)
  | .af1, false => (.inc .carry, some false, none)
  | .cp, b => (.cp, some b, none)
  | .inc q, b => (.inc (δinc q b).1, (δinc q b).2.1, (δinc q b).2.2)

def finFix : FQ → Option Bool
  | .inc q => finInc q
  | _ => none

theorem fix_cp (l : List Bool) : fstRun2 δfix finFix .cp l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun2, δfix, ih]

theorem fix_inc (q : IncQ) (l : List Bool) :
    fstRun2 δfix finFix (.inc q) l = fstRun2 δinc finInc q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun2, δfix, ih]

theorem fix_hd1 (k : ℕ) (l : List Bool) :
    fstRun2 δfix finFix .hd1 (List.replicate k true ++ l) =
      List.replicate k true ++ fstRun2 δfix finFix .hd1 l := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, fstRun2, δfix, ih]

theorem encodeList_ne {α : Type} (e : α → List Bool) (g : α) (gs : List α) :
    encodeList e (g :: gs) = true :: (e g ++ encodeList e gs) := by
  simp [encodeList]

theorem fix_run (q : ℕ × Circuit) : encodeLgp (fixf q) = fstRun2 δfix finFix .hd0 (encodeLgp q) := by
  obtain ⟨n, ⟨gs, o⟩⟩ := q
  -- the rest after the header
  have hrest : ∀ (st : FQ), (st = .af0 ∨ st = .af1) → (gs ≠ [] ∨ st = .af0) →
      fstRun2 δfix finFix st (encodeList encodeGate gs ++ encodeNat o) =
        encodeList encodeGate gs ++ encodeNat o := by
    intro st hst hcase
    cases gs with
    | nil =>
      have : st = .af0 := by simpa using hcase
      subst this
      simp [encodeList, fstRun2, δfix, fix_cp]
    | cons g gs =>
      rw [encodeList_ne]
      rcases hst with rfl | rfl <;> simp [fstRun2, δfix, fix_cp]
  unfold fixf encodeLgp
  simp only
  cases n with
  | zero =>
    simp only [lt_irrefl, and_false, if_false, List.replicate_zero, List.nil_append]
    simp only [fstRun2, δfix, Option.toList_some, Option.toList_none, List.append_nil,
      List.singleton_append]
    rw [hrest .af0 (Or.inl rfl) (Or.inr rfl)]
  | succ k =>
    rw [List.replicate_succ]
    simp only [List.cons_append, fstRun2, δfix, Option.toList_some, Option.toList_none,
      List.append_nil, List.singleton_append]
    rw [fix_hd1]
    simp only [fstRun2, δfix, Option.toList_some, Option.toList_none, List.append_nil,
      List.singleton_append]
    by_cases hg : gs = []
    · subst hg
      simp only [Nat.succ_pos, and_true, if_true, encodeList, List.flatMap_nil,
        List.nil_append, List.cons_append]
      simp only [fstRun2, δfix, Option.toList_some, Option.toList_none, List.append_nil,
        List.singleton_append]
      rw [fix_inc]
      show _ = true :: (List.replicate k true ++ false :: false :: incT (encodeNat o))
      rw [incT_encodeNat]
      rfl
    · rw [if_neg (fun h => hg h.1), hrest .af1 (Or.inr rfl) (Or.inl hg)]
      simp [List.replicate_succ]

theorem cpt_fixf : ComputableInPolyTime encodeLgp encodeLgp fixf :=
  fst2_polyTime encodeLgp encodeLgp fixf δfix finFix .hd0 fix_run

end PEqualNP.MetaComplexity.Helpers.MachinePrint
